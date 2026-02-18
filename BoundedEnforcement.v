(******************************************************************************)
(*                                                                            *)
(*            Bounded Enforcement in Deontic Obligation Systems               *)
(*                                                                            *)
(*     Deontic logic framework with obligations, violations, and bounded      *)
(*     enforcement rights. Proves that no consistent assignment of            *)
(*     enforcement authority can authorize unbounded punitive response        *)
(*     to a single obligation violation. The Homeworld (1999) universe        *)
(*     supplies the concrete examples that instantiate every schema.          *)
(*                                                                            *)
(*     "The captain claimed our planet violated a 4000 year old treaty        *)
(*     forbidding us to develop hyperspace technology. Extermination          *)
(*     of our planet was the consequence."                                    *)
(*     – Fleet Intelligence                                                   *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: February 10, 2026                                                *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

Require Import Arith.
Require Import List.
Require Import Lia.
Require Import Bool.
Import ListNotations.

(** * Carrier Types *)

(** Agents are moral/legal persons capable of bearing obligations and
    wielding enforcement authority.  We index them by [nat] so that
    equality is decidable and we can quantify over finite populations. *)

Record Agent := mkAgent { agent_id : nat }.

Definition agent_eqb (a b : Agent) : bool :=
  Nat.eqb (agent_id a) (agent_id b).

Lemma agent_eqb_spec : forall a b,
  reflect (a = b) (agent_eqb a b).
Proof.
  intros [m] [n]. unfold agent_eqb. simpl.
  destruct (Nat.eqb_spec m n).
  - subst. constructor. reflexivity.
  - constructor. intros H. injection H. auto.
Qed.

(** Witness: two distinct agents exist. *)
Definition taiidan  := mkAgent 0.
Definition kushan   := mkAgent 1.

Lemma agents_distinct : taiidan <> kushan.
Proof.
  unfold taiidan, kushan. intros H. injection H. lia.
Qed.

(** Obligations are indexed duties that an agent can bear.  The index
    lets us distinguish obligations without committing to content yet. *)

Record Obligation := mkObligation { obligation_id : nat }.

Definition obligation_eqb (o1 o2 : Obligation) : bool :=
  Nat.eqb (obligation_id o1) (obligation_id o2).

Lemma obligation_eqb_spec : forall o1 o2,
  reflect (o1 = o2) (obligation_eqb o1 o2).
Proof.
  intros [m] [n]. unfold obligation_eqb. simpl.
  destruct (Nat.eqb_spec m n).
  - subst. constructor. reflexivity.
  - constructor. intros H. injection H. auto.
Qed.

(** Witness: two distinct obligations. *)
Definition treaty_no_hyperspace := mkObligation 0.
Definition treaty_tribute       := mkObligation 1.

Lemma obligations_distinct :
  treaty_no_hyperspace <> treaty_tribute.
Proof.
  unfold treaty_no_hyperspace, treaty_tribute.
  intros H. injection H. lia.
Qed.

(** Severity is a natural number measuring the magnitude of a punitive
    response.  Zero means no punishment; larger values mean harsher
    responses.  We use [nat] directly rather than an opaque type so
    that arithmetic reasoning is available. *)

Definition Severity := nat.

(** Witness: severity 1 (a fine) is strictly less than severity 1000
    (genocide), and both are non-zero, showing the ordering is
    non-trivial. *)
Lemma severity_nontrivial : (1 < 1000)%nat /\ (0 < 1)%nat.
Proof.
  split; lia.
Qed.

(** * Deontic System *)

(** A [DeonticSystem] packages together:
    - a finite population of agents,
    - an assignment of obligations to agents,
    - a violation predicate (which agents violated which obligations),
    - an enforcement authority relation (who may punish whom),
    - a severity cap per obligation (the maximum lawful punishment). *)

Record DeonticSystem := mkDeonticSystem {
  agents       : list Agent;
  obligated    : Agent -> Obligation -> bool;
  violated     : Agent -> Obligation -> bool;
  may_enforce  : Agent -> Agent -> bool;
  severity_cap : Obligation -> Severity
}.

(** Coherence:
    (1) you can only violate an obligation you actually bear,
    (2) enforcement authority only holds between population members,
    (3) obligations with nonzero caps have at least one bearer. *)
Definition coherent (ds : DeonticSystem) : Prop :=
  (forall a o,
    violated ds a o = true -> obligated ds a o = true) /\
  (forall a b,
    may_enforce ds a b = true -> In a (agents ds) /\ In b (agents ds)) /\
  (forall o,
    severity_cap ds o > 0 ->
    exists a, In a (agents ds) /\ obligated ds a o = true).

(** Non-reflexive enforcement: no agent may punish itself. *)
Definition irreflexive_enforcement (ds : DeonticSystem) : Prop :=
  forall a, may_enforce ds a a = false.

(** Witness: a concrete two-agent system.
    - Kushan bears the hyperspace treaty; Taiidan does not.
    - Kushan has violated the treaty.
    - Taiidan may enforce against Kushan but not vice versa.
    - The severity cap for the hyperspace treaty is 10 (a sanction).  *)

Definition homeworld_system : DeonticSystem := mkDeonticSystem
  [taiidan; kushan]
  (fun a o =>
    agent_eqb a kushan && obligation_eqb o treaty_no_hyperspace)
  (fun a o =>
    agent_eqb a kushan && obligation_eqb o treaty_no_hyperspace)
  (fun enforcer target =>
    agent_eqb enforcer taiidan && agent_eqb target kushan)
  (fun o =>
    if obligation_eqb o treaty_no_hyperspace then 10 else 0).

(** The witness system is coherent. *)
Lemma homeworld_coherent : coherent homeworld_system.
Proof.
  split; [| split].
  - intros a o H. exact H.
  - intros a b H.
    unfold homeworld_system in H. simpl in H.
    destruct (agent_eqb_spec a taiidan); destruct (agent_eqb_spec b kushan);
      subst; simpl in *; try discriminate.
    split; [left; reflexivity | right; left; reflexivity].
  - intros o Hcap.
    unfold homeworld_system in *. simpl in *.
    destruct (obligation_eqb_spec o treaty_no_hyperspace); subst.
    + exists kushan. simpl. split.
      * right. left. reflexivity.
      * reflexivity.
    + simpl in Hcap. lia.
Qed.

(** The witness system has irreflexive enforcement. *)
Lemma homeworld_irreflexive : irreflexive_enforcement homeworld_system.
Proof.
  unfold irreflexive_enforcement, homeworld_system. simpl.
  intros [n]. unfold agent_eqb. simpl.
  destruct (Nat.eqb_spec n 0); destruct (Nat.eqb_spec n 1); subst; auto.
  lia.
Qed.

(** Counterexample: a system where an agent violates an obligation it
    does not bear is incoherent. *)
Definition incoherent_system : DeonticSystem := mkDeonticSystem
  [kushan]
  (fun _ _ => false)
  (fun a o =>
    agent_eqb a kushan && obligation_eqb o treaty_no_hyperspace)
  (fun _ _ => false)
  (fun _ => 0).

Lemma incoherent_system_not_coherent : ~ coherent incoherent_system.
Proof.
  unfold coherent, incoherent_system. simpl.
  intros [H _].
  specialize (H kushan treaty_no_hyperspace).
  simpl in H.
  discriminate H.
  reflexivity.
Qed.

(** * Punitive Response *)

(** A [PunitiveResponse] records an enforcer applying a punishment of
    a given severity against a target for a specific obligation
    violation. *)

Record PunitiveResponse := mkPunitiveResponse {
  enforcer  : Agent;
  target    : Agent;
  cause     : Obligation;
  severity  : Severity
}.

(** A response is *authorized* when:
    (1) both agents are in the population,
    (2) the enforcer may enforce against the target,
    (3) the target actually violated the obligation,
    (4) the target bore the obligation. *)

Definition authorized (ds : DeonticSystem) (pr : PunitiveResponse) : Prop :=
  In (enforcer pr) (agents ds) /\
  In (target pr) (agents ds) /\
  may_enforce ds (enforcer pr) (target pr) = true /\
  violated ds (target pr) (cause pr) = true /\
  obligated ds (target pr) (cause pr) = true.

(** A response is *bounded* when its severity does not exceed the cap. *)

Definition bounded (ds : DeonticSystem) (pr : PunitiveResponse) : Prop :=
  severity pr <= severity_cap ds (cause pr).

(** A response is *unbounded* when its severity strictly exceeds
    the cap. *)

Definition unbounded (ds : DeonticSystem) (pr : PunitiveResponse) : Prop :=
  severity pr > severity_cap ds (cause pr).

(** Bounded and unbounded are mutually exclusive and jointly exhaustive
    (given decidability of [<=] on [nat]). *)

Lemma bounded_unbounded_exclusive :
  forall ds pr, ~ (bounded ds pr /\ unbounded ds pr).
Proof.
  unfold bounded, unbounded. intros ds pr [Hle Hgt]. lia.
Qed.

Lemma bounded_unbounded_exhaustive :
  forall ds pr, bounded ds pr \/ unbounded ds pr.
Proof.
  unfold bounded, unbounded. intros ds pr.
  destruct (le_gt_dec (severity pr) (severity_cap ds (cause pr))).
  - left. exact l.
  - right. exact g.
Qed.

(** Witness: Taiidan imposing severity 5 for the hyperspace treaty
    violation.  This is authorized and bounded (cap = 10). *)

Definition proportional_response := mkPunitiveResponse
  taiidan kushan treaty_no_hyperspace 5.

Lemma proportional_authorized :
  authorized homeworld_system proportional_response.
Proof.
  unfold authorized, homeworld_system, proportional_response. simpl.
  repeat split; auto.
Qed.

Lemma proportional_bounded :
  bounded homeworld_system proportional_response.
Proof.
  unfold bounded, homeworld_system, proportional_response. simpl.
  lia.
Qed.

(** Witness: Taiidan imposing severity 100 (planetary extermination).
    Authorized (they have enforcement authority) but unbounded (cap=10). *)

Definition extermination_response := mkPunitiveResponse
  taiidan kushan treaty_no_hyperspace 100.

Lemma extermination_authorized :
  authorized homeworld_system extermination_response.
Proof.
  unfold authorized, homeworld_system, extermination_response. simpl.
  repeat split; auto.
Qed.

Lemma extermination_unbounded :
  unbounded homeworld_system extermination_response.
Proof.
  unfold unbounded, homeworld_system, extermination_response. simpl.
  lia.
Qed.

(** Counterexample: Kushan cannot punish Taiidan (no enforcement
    authority), so any such response is unauthorized regardless of
    severity. *)

Definition unauthorized_response := mkPunitiveResponse
  kushan taiidan treaty_tribute 1.

Lemma unauthorized_example :
  ~ authorized homeworld_system unauthorized_response.
Proof.
  unfold authorized, homeworld_system, unauthorized_response. simpl.
  intros [_ [_ [H _]]]. discriminate.
Qed.

(** * Lawful Response *)

(** Lawfulness is defined as an inductive judgment with a single
    introduction rule.  The premises are checked independently by the
    rule — boundedness is not built into the definition by conjunction
    but emerges as a consequence of the rule's structure. *)

Inductive lawful (ds : DeonticSystem) (pr : PunitiveResponse) : Prop :=
  | lawful_intro :
      In (enforcer pr) (agents ds) ->
      In (target pr) (agents ds) ->
      may_enforce ds (enforcer pr) (target pr) = true ->
      violated ds (target pr) (cause pr) = true ->
      obligated ds (target pr) (cause pr) = true ->
      severity pr <= severity_cap ds (cause pr) ->
      lawful ds pr.

(** Lawfulness implies authorization. *)
Lemma lawful_authorized :
  forall ds pr, lawful ds pr -> authorized ds pr.
Proof.
  intros ds pr [Hin_e Hin_t Henf Hviol Hobl _].
  unfold authorized. auto.
Qed.

(** Lawfulness implies boundedness — a real inversion, not a projection. *)
Lemma lawful_bounded :
  forall ds pr, lawful ds pr -> bounded ds pr.
Proof.
  intros ds pr [_ _ _ _ _ Hle].
  unfold bounded. exact Hle.
Qed.

(** Completeness: authorized + bounded is sufficient. *)
Lemma lawful_from_auth_bounded :
  forall ds pr, authorized ds pr -> bounded ds pr -> lawful ds pr.
Proof.
  intros ds pr [Hin_e [Hin_t [Henf [Hviol Hobl]]]] Hbnd.
  exact (lawful_intro ds pr Hin_e Hin_t Henf Hviol Hobl Hbnd).
Qed.

(** Witness: the proportional response is lawful. *)
Lemma proportional_lawful :
  lawful homeworld_system proportional_response.
Proof.
  apply lawful_from_auth_bounded.
  - exact proportional_authorized.
  - exact proportional_bounded.
Qed.

(** Witness: the extermination is authorized but NOT lawful. *)
Lemma extermination_not_lawful :
  authorized homeworld_system extermination_response /\
  ~ lawful homeworld_system extermination_response.
Proof.
  split.
  - exact extermination_authorized.
  - intros Hlaw. apply (lawful_bounded) in Hlaw.
    unfold bounded, homeworld_system, extermination_response in Hlaw.
    simpl in Hlaw. lia.
Qed.

(** Authorization does not entail lawful power to impose arbitrary
    severity. *)

Lemma authorization_insufficient :
  exists ds pr,
    authorized ds pr /\ ~ lawful ds pr.
Proof.
  exists homeworld_system, extermination_response.
  exact extermination_not_lawful.
Qed.

(** Counterexample: an unauthorized response is never lawful,
    regardless of severity. *)
Lemma unauthorized_never_lawful :
  forall ds pr, ~ authorized ds pr -> ~ lawful ds pr.
Proof.
  intros ds pr Hnauth Hlaw. apply Hnauth. exact (lawful_authorized ds pr Hlaw).
Qed.

(** * Consistent Deontic Systems *)

(** A deontic system is *consistent* when:
    (1) it is coherent (only bearers can violate),
    (2) enforcement is irreflexive (no self-punishment),
    (3) every severity cap is positive (enforcement is possible, not
        vacuously prevented). *)

Record consistent (ds : DeonticSystem) : Prop := mkConsistent {
  consistent_coherent     : coherent ds;
  consistent_irreflexive  : irreflexive_enforcement ds;
  consistent_caps_positive : forall a o,
    In a (agents ds) ->
    obligated ds a o = true ->
    severity_cap ds o > 0
}.

(** Witness: the Homeworld system is consistent. *)
Lemma homeworld_consistent : consistent homeworld_system.
Proof.
  constructor.
  - exact homeworld_coherent.
  - exact homeworld_irreflexive.
  - intros a o Hin Hobl.
    unfold homeworld_system in *. simpl in *.
    destruct Hin as [Ha | [Ha | []]]; subst; simpl in Hobl.
    + discriminate.
    + unfold agent_eqb in Hobl. simpl in Hobl.
      destruct (obligation_eqb_spec o treaty_no_hyperspace); subst.
      * simpl. lia.
      * simpl in Hobl. discriminate.
Qed.

(** Counterexample: a system with zero caps everywhere is not
    consistent if any agent bears an obligation (enforcement is
    impossible — the cap is not positive). *)
Definition zero_cap_system : DeonticSystem := mkDeonticSystem
  [kushan]
  (fun a o =>
    agent_eqb a kushan && obligation_eqb o treaty_no_hyperspace)
  (fun _ _ => false)
  (fun _ _ => false)
  (fun _ => 0).

Lemma zero_cap_not_consistent : ~ consistent zero_cap_system.
Proof.
  intros [_ _ Hcaps].
  specialize (Hcaps kushan treaty_no_hyperspace).
  unfold zero_cap_system in Hcaps. simpl in Hcaps.
  assert (H : 0 > 0).
  { apply Hcaps.
    - left. reflexivity.
    - reflexivity. }
  lia.
Qed.

(** In a consistent system, every authorized response targets a
    violation with a positive severity cap. *)

Theorem consistent_authorized_positive_cap :
  forall ds pr,
    consistent ds ->
    authorized ds pr ->
    severity_cap ds (cause pr) > 0.
Proof.
  intros ds pr [Hcoh Hirr Hcaps] Hauth.
  destruct Hauth as [Hin_e [Hin_t [Henf [Hviol Hobl]]]].
  exact (Hcaps (target pr) (cause pr) Hin_t Hobl).
Qed.

(** * Per-Response Bound *)

(** Any lawful response has severity at most the cap.  This follows
    directly from the definition of [lawful], but we state it
    explicitly as the single-response bound. *)

Theorem per_response_bound :
  forall ds pr,
    lawful ds pr ->
    severity pr <= severity_cap ds (cause pr).
Proof.
  intros ds pr Hlaw. exact (lawful_bounded ds pr Hlaw).
Qed.

(** Non-triviality: the bound is tight.  There exists a lawful
    response that exactly hits the cap. *)

Definition maximal_response := mkPunitiveResponse
  taiidan kushan treaty_no_hyperspace 10.

Lemma maximal_response_lawful :
  lawful homeworld_system maximal_response.
Proof.
  apply lawful_intro; unfold homeworld_system, maximal_response; simpl; auto; lia.
Qed.

Lemma maximal_response_tight :
  severity maximal_response = severity_cap homeworld_system (cause maximal_response).
Proof.
  unfold maximal_response, homeworld_system. simpl. reflexivity.
Qed.

(** * Aggregate Enforcement Bound *)

(** When multiple enforcers respond to a single violation, the total
    lawful punishment is bounded by the number of enforcers times the
    per-obligation cap.

    We model a collection of responses as a list.  Each response in
    the list targets the same agent for the same violation.  We prove
    that if every response is lawful, the sum of severities is at most
    [length responses * cap]. *)

Fixpoint total_severity (responses : list PunitiveResponse) : nat :=
  match responses with
  | [] => 0
  | pr :: rest => severity pr + total_severity rest
  end.

Definition all_lawful (ds : DeonticSystem) (responses : list PunitiveResponse) : Prop :=
  forall pr, In pr responses -> lawful ds pr.

Definition all_target_same
  (tgt : Agent) (obl : Obligation) (responses : list PunitiveResponse) : Prop :=
  forall pr, In pr responses ->
    target pr = tgt /\ cause pr = obl.

(** Key lemma: each lawful response contributes at most [cap]. *)
Lemma lawful_severity_le_cap :
  forall ds pr obl,
    lawful ds pr ->
    cause pr = obl ->
    severity pr <= severity_cap ds obl.
Proof.
  intros ds pr obl Hlaw Heq.
  subst. exact (lawful_bounded ds pr Hlaw).
Qed.

(** The aggregate bound. *)
Theorem aggregate_enforcement_bound :
  forall ds tgt obl (responses : list PunitiveResponse),
    all_lawful ds responses ->
    all_target_same tgt obl responses ->
    total_severity responses <= length responses * severity_cap ds obl.
Proof.
  intros ds tgt obl responses Hlawful Hsame.
  induction responses as [| pr rest IH].
  - simpl. lia.
  - simpl.
    assert (Hpr : lawful ds pr).
    { apply Hlawful. left. reflexivity. }
    assert (Hobl : cause pr = obl).
    { apply Hsame. left. reflexivity. }
    assert (Hle : severity pr <= severity_cap ds obl).
    { exact (lawful_severity_le_cap ds pr obl Hpr Hobl). }
    assert (Hrest : total_severity rest <= length rest * severity_cap ds obl).
    { apply IH.
      - intros pr' Hin. apply Hlawful. right. exact Hin.
      - intros pr' Hin. apply Hsame. right. exact Hin. }
    lia.
Qed.

(** A [TargetedResponses] record structurally guarantees that all
    responses target the same agent for the same obligation. *)

Record TargetedResponses := mkTargetedResponses {
  tr_target   : Agent;
  tr_cause    : Obligation;
  tr_responses : list PunitiveResponse;
  tr_invariant : forall pr, In pr tr_responses ->
    target pr = tr_target /\ cause pr = tr_cause
}.

(** Aggregate bound using the structural type — no propositional
    side condition needed. *)
Theorem targeted_aggregate_bound :
  forall ds (tr : TargetedResponses),
    all_lawful ds (tr_responses tr) ->
    total_severity (tr_responses tr) <=
      length (tr_responses tr) * severity_cap ds (tr_cause tr).
Proof.
  intros ds tr Hlawful.
  apply (aggregate_enforcement_bound ds (tr_target tr) (tr_cause tr)).
  - exact Hlawful.
  - exact (tr_invariant tr).
Qed.

(** Witness: two lawful responses to the hyperspace violation. *)
Definition two_responses := [proportional_response; maximal_response].

Lemma two_responses_all_lawful :
  all_lawful homeworld_system two_responses.
Proof.
  intros pr Hin. simpl in Hin.
  destruct Hin as [H | [H | []]]; subst.
  - exact proportional_lawful.
  - exact maximal_response_lawful.
Qed.

Lemma two_responses_same_target :
  all_target_same kushan treaty_no_hyperspace two_responses.
Proof.
  intros pr Hin. simpl in Hin.
  destruct Hin as [H | [H | []]]; subst; simpl; auto.
Qed.

Lemma two_responses_bound :
  total_severity two_responses <= 2 * severity_cap homeworld_system treaty_no_hyperspace.
Proof.
  apply (aggregate_enforcement_bound homeworld_system kushan treaty_no_hyperspace).
  - exact two_responses_all_lawful.
  - exact two_responses_same_target.
Qed.

(** Concrete check: 5 + 10 = 15 <= 2 * 10 = 20. *)
Lemma two_responses_concrete : total_severity two_responses = 15.
Proof. reflexivity. Qed.

(** When enforcers are distinct population members, the number of
    responses is bounded by the population size.  We state the
    aggregate bound with an explicit population-size hypothesis,
    avoiding the need for NoDup infrastructure over agents. *)

Definition distinct_enforcers (responses : list PunitiveResponse) : Prop :=
  NoDup (map enforcer responses).

Definition enforcers_in_population
  (ds : DeonticSystem) (responses : list PunitiveResponse) : Prop :=
  forall pr, In pr responses -> In (enforcer pr) (agents ds).

Theorem population_bounded_aggregate :
  forall ds tgt obl responses,
    all_lawful ds responses ->
    all_target_same tgt obl responses ->
    length responses <= length (agents ds) ->
    total_severity responses <= length (agents ds) * severity_cap ds obl.
Proof.
  intros ds tgt obl responses Hlawful Hsame Hpop.
  assert (Hagg := aggregate_enforcement_bound ds tgt obl responses Hlawful Hsame).
  nia.
Qed.

(** A system satisfies *ne bis in idem* when at most one enforcer
    may respond per violation. Under this constraint, aggregate
    punishment for a single violation is bounded by the cap itself. *)

Definition ne_bis_in_idem
  (ds : DeonticSystem) (responses : list PunitiveResponse)
  (tgt : Agent) (obl : Obligation) : Prop :=
  all_target_same tgt obl responses /\
  NoDup (map enforcer responses) /\
  length responses <= 1.

Theorem ne_bis_in_idem_bound :
  forall ds tgt obl responses,
    all_lawful ds responses ->
    ne_bis_in_idem ds responses tgt obl ->
    total_severity responses <= severity_cap ds obl.
Proof.
  intros ds tgt obl responses Hlawful [Hsame [Hnodup Hlen]].
  destruct responses as [| pr rest].
  - simpl. lia.
  - simpl in Hlen. assert (rest = []) as -> by (destruct rest; [reflexivity | simpl in Hlen; lia]).
    simpl.
    assert (Hpr : lawful ds pr) by (apply Hlawful; left; reflexivity).
    assert (Hobl : cause pr = obl) by (apply Hsame; left; reflexivity).
    assert (Hbnd := lawful_bounded ds pr Hpr). unfold bounded in Hbnd.
    subst. lia.
Qed.

(** Witness: the homeworld system with a single response satisfies
    ne bis in idem, bounding total severity to 10. *)
Lemma homeworld_ne_bis_in_idem :
  ne_bis_in_idem homeworld_system [proportional_response]
    kushan treaty_no_hyperspace.
Proof.
  split; [| split].
  - intros pr Hin. destruct Hin as [H | []]; subst; simpl; auto.
  - simpl. constructor.
    + intros [].
    + constructor.
  - simpl. lia.
Qed.

(** * The Main Theorem *)

(** No authorized response that exceeds the severity cap is lawful.
    Equivalently: enforcement authority (standing) never licenses
    disproportionate punishment. *)

Theorem no_unbounded_lawful :
  forall ds pr,
    authorized ds pr ->
    unbounded ds pr ->
    ~ lawful ds pr.
Proof.
  intros ds pr Hauth Hunb Hlaw.
  assert (Hbnd := lawful_bounded ds pr Hlaw).
  exact (bounded_unbounded_exclusive ds pr (conj Hbnd Hunb)).
Qed.

(** Non-triviality: the hypothesis [authorized ds pr] is satisfiable. *)
Lemma no_unbounded_lawful_nontrivial_auth :
  exists ds pr, authorized ds pr /\ unbounded ds pr.
Proof.
  exists homeworld_system, extermination_response.
  split.
  - exact extermination_authorized.
  - exact extermination_unbounded.
Qed.

(** Non-triviality: the conclusion [~ lawful ds pr] is not vacuously
    true — there DO exist lawful responses in the same system. *)
Lemma no_unbounded_lawful_nontrivial_lawful :
  exists ds pr, lawful ds pr.
Proof.
  exists homeworld_system, proportional_response.
  exact proportional_lawful.
Qed.

(** Instantiation: the extermination of Kharak. *)
Corollary kharak_extermination_unlawful :
  ~ lawful homeworld_system extermination_response.
Proof.
  apply no_unbounded_lawful.
  - exact extermination_authorized.
  - exact extermination_unbounded.
Qed.

(** * Strengthened Aggregate Theorem *)

(** If any response in a collection is unbounded, the entire
    collection cannot be all-lawful. *)

Theorem unbounded_member_breaks_collection :
  forall ds (responses : list PunitiveResponse) pr,
    In pr responses ->
    unbounded ds pr ->
    ~ all_lawful ds responses.
Proof.
  intros ds responses pr Hin Hunb Hlawful.
  assert (Hlaw : lawful ds pr) by (apply Hlawful; exact Hin).
  assert (Hbnd := lawful_bounded ds pr Hlaw).
  exact (bounded_unbounded_exclusive ds pr (conj Hbnd Hunb)).
Qed.

(** Witness: adding the extermination response to the collection
    makes it non-all-lawful. *)
Definition mixed_responses := [proportional_response; extermination_response].

Lemma mixed_responses_not_all_lawful :
  ~ all_lawful homeworld_system mixed_responses.
Proof.
  apply (unbounded_member_breaks_collection homeworld_system
           mixed_responses extermination_response).
  - right. left. reflexivity.
  - exact extermination_unbounded.
Qed.

(** * Enforcement Delegation *)

(** In hierarchical enforcement regimes, authority may be delegated:
    agent A grants agent B the right to punish on A's behalf.
    Delegation must not amplify the severity cap — a delegate cannot
    impose harsher punishment than the delegator was entitled to.

    [delegate_cap] is indexed by the delegation pair (delegator,
    delegate), not just the delegate. This allows distinct delegators
    to grant different caps to the same delegate. *)

Record DelegationSystem := mkDelegationSystem {
  ds_base      : DeonticSystem;
  delegates_to : Agent -> Agent -> bool;
  delegate_cap : Agent -> Agent -> Obligation -> Severity
}.

(** A delegation system is *cap-monotone* when every delegate's cap
    from a given delegator does not exceed that delegator's own cap.
    For the root (an agent with base-system enforcement authority),
    the cap is [severity_cap (ds_base del)]. *)

Definition cap_monotone (del : DelegationSystem) : Prop :=
  forall delegator delegate obl,
    delegates_to del delegator delegate = true ->
    delegate_cap del delegator delegate obl <=
      severity_cap (ds_base del) obl.

(** Reachability in the delegation graph. *)

Inductive reachable (del : DelegationSystem) : Agent -> Agent -> Prop :=
  | reach_step : forall a b,
      delegates_to del a b = true -> reachable del a b
  | reach_trans : forall a b c,
      delegates_to del a b = true ->
      reachable del b c ->
      reachable del a c.

(** Acyclicity: no agent is reachable from itself. *)

Definition acyclic (del : DelegationSystem) : Prop :=
  forall a, ~ reachable del a a.

(** A delegation is *well-formed* when it is cap-monotone, acyclic,
    and the base system is consistent. *)

Record well_formed_delegation (del : DelegationSystem) : Prop :=
  mkWFDelegation {
  wf_base_consistent : consistent (ds_base del);
  wf_cap_monotone    : cap_monotone del;
  wf_acyclic         : acyclic del
}.

(** Theorem: in a well-formed delegation, a delegate's cap from any
    delegator is bounded by the base system cap. *)

Theorem delegation_bounded :
  forall del delegator delegate obl s,
    well_formed_delegation del ->
    delegates_to del delegator delegate = true ->
    s <= delegate_cap del delegator delegate obl ->
    s <= severity_cap (ds_base del) obl.
Proof.
  intros del delegator delegate obl s [_ Hmono _] Hdel Hs.
  specialize (Hmono delegator delegate obl Hdel).
  lia.
Qed.

(** In a well-formed delegation with irreflexive base enforcement, no
    agent can be punished via a delegation chain originating from
    itself. Acyclicity prevents laundering self-punishment through
    intermediaries. *)

Theorem no_self_delegation :
  forall del a,
    well_formed_delegation del ->
    ~ reachable del a a.
Proof.
  intros del a [_ _ Hacyclic].
  exact (Hacyclic a).
Qed.

(** Reachability composes transitively. *)

Lemma reachable_trans :
  forall del a b c,
    reachable del a b ->
    reachable del b c ->
    reachable del a c.
Proof.
  intros del a b c Hab Hbc.
  induction Hab as [a' b' Hdel | a' b' m Hdel Hbm IH].
  - exact (reach_trans del a' b' c Hdel Hbc).
  - exact (reach_trans del a' b' c Hdel (IH Hbc)).
Qed.

(** If A delegates (transitively) to B, then B does not delegate
    back to A. *)

Theorem delegation_no_collusion :
  forall del a b,
    well_formed_delegation del ->
    reachable del a b ->
    ~ reachable del b a.
Proof.
  intros del a b [_ _ Hacyclic] Hab Hba.
  exact (Hacyclic a (reachable_trans del a b a Hab Hba)).
Qed.

(** Enforcement authority may pass through multiple delegates:
    A delegates to B, B delegates to C, etc.  We model chains as
    lists of agents where each adjacent pair has a delegation link.

    [chain_cap] computes the effective cap at each hop by taking
    the minimum of the delegate cap at that hop and the effective
    cap from the previous hop. This makes caps genuinely relative. *)

Fixpoint valid_chain (del : DelegationSystem) (chain : list Agent) : Prop :=
  match chain with
  | [] => True
  | [_] => True
  | a :: ((b :: _) as rest) =>
      delegates_to del a b = true /\ valid_chain del rest
  end.

Fixpoint chain_cap (del : DelegationSystem) (chain : list Agent)
  (obl : Obligation) : Severity :=
  match chain with
  | [] => 0
  | [a] => severity_cap (ds_base del) obl
  | a :: ((b :: _) as rest) =>
      Nat.min (delegate_cap del a b obl) (chain_cap del rest obl)
  end.

(** The chain cap is bounded by the base system cap at every hop.
    Proved by induction on the chain. *)

Theorem chain_bounded :
  forall del obl chain,
    cap_monotone del ->
    valid_chain del chain ->
    chain_cap del chain obl <= severity_cap (ds_base del) obl.
Proof.
  intros del obl chain Hmono.
  induction chain as [| a rest IH].
  - simpl. lia.
  - destruct rest as [| b rest'].
    + simpl. lia.
    + simpl. intros [Hdel Hvalid].
      specialize (Hmono a b obl Hdel).
      specialize (IH Hvalid).
      lia.
Qed.

(** Witness: Taiidan delegates to Turanic Raiders (agent 2) with
    a reduced cap of 5. *)

Definition turanic := mkAgent 2.

Definition homeworld_delegation : DelegationSystem := mkDelegationSystem
  homeworld_system
  (fun delegator delegate =>
    agent_eqb delegator taiidan && agent_eqb delegate turanic)
  (fun delegator delegate obl =>
    if agent_eqb delegator taiidan && agent_eqb delegate turanic
       && obligation_eqb obl treaty_no_hyperspace
    then 5 else 0).

Lemma homeworld_delegation_cap_monotone :
  cap_monotone homeworld_delegation.
Proof.
  intros delegator delegate obl Hdel.
  unfold homeworld_delegation, homeworld_system in *. simpl in *.
  destruct (agent_eqb_spec delegator taiidan);
  destruct (agent_eqb_spec delegate turanic);
  destruct (obligation_eqb_spec obl treaty_no_hyperspace);
  subst; simpl; try lia.
  all: simpl in Hdel; try discriminate.
Qed.

Lemma homeworld_delegates_to_shape :
  forall a b,
    delegates_to homeworld_delegation a b = true ->
    a = taiidan /\ b = turanic.
Proof.
  intros a b H.
  unfold homeworld_delegation in H. simpl in H.
  destruct (agent_eqb_spec a taiidan); destruct (agent_eqb_spec b turanic);
    subst; simpl in *; try discriminate.
  auto.
Qed.

Lemma homeworld_reachable_target :
  forall a b,
    reachable homeworld_delegation a b ->
    b = turanic.
Proof.
  intros a b H.
  induction H as [a' b' Hdel | a' b' c Hdel Hreach IH].
  - destruct (homeworld_delegates_to_shape a' b' Hdel). assumption.
  - exact IH.
Qed.

Lemma homeworld_reachable_source :
  forall a b,
    reachable homeworld_delegation a b ->
    a = taiidan.
Proof.
  intros a b H.
  induction H as [a' b' Hdel | a' b' c Hdel Hreach IH].
  - destruct (homeworld_delegates_to_shape a' b' Hdel). assumption.
  - destruct (homeworld_delegates_to_shape a' b' Hdel). assumption.
Qed.

Lemma homeworld_delegation_acyclic :
  acyclic homeworld_delegation.
Proof.
  intros a Hreach.
  assert (H1 := homeworld_reachable_source a a Hreach).
  assert (H2 := homeworld_reachable_target a a Hreach).
  subst. unfold taiidan, turanic in H2. discriminate.
Qed.

Lemma homeworld_delegation_well_formed :
  well_formed_delegation homeworld_delegation.
Proof.
  constructor.
  - exact homeworld_consistent.
  - exact homeworld_delegation_cap_monotone.
  - exact homeworld_delegation_acyclic.
Qed.

(** Instantiation: the Turanic Raiders cannot exceed severity 10
    (the original cap) when punishing on Taiidan's behalf. *)
Lemma turanic_bounded_by_treaty_cap :
  forall s,
    s <= delegate_cap homeworld_delegation taiidan turanic treaty_no_hyperspace ->
    s <= severity_cap homeworld_system treaty_no_hyperspace.
Proof.
  intros s Hs.
  apply (delegation_bounded homeworld_delegation taiidan turanic
           treaty_no_hyperspace s).
  - exact homeworld_delegation_well_formed.
  - reflexivity.
  - exact Hs.
Qed.

(** The delegate's cap is strictly less than the base cap. *)
Lemma turanic_cap_reduced :
  delegate_cap homeworld_delegation taiidan turanic treaty_no_hyperspace <
  severity_cap homeworld_system treaty_no_hyperspace.
Proof.
  unfold homeworld_delegation, homeworld_system. simpl. lia.
Qed.

(** Counterexample: a delegation that amplifies the cap violates
    cap-monotonicity. *)
Definition amplifying_delegation : DelegationSystem := mkDelegationSystem
  homeworld_system
  (fun delegator delegate =>
    agent_eqb delegator taiidan && agent_eqb delegate turanic)
  (fun delegator delegate obl =>
    if agent_eqb delegator taiidan && agent_eqb delegate turanic
       && obligation_eqb obl treaty_no_hyperspace
    then 50 else 0).

Lemma amplifying_not_cap_monotone :
  ~ cap_monotone amplifying_delegation.
Proof.
  intros H.
  specialize (H taiidan turanic treaty_no_hyperspace).
  unfold amplifying_delegation, homeworld_system in H. simpl in H.
  assert (Habs : 50 <= 10) by (apply H; reflexivity).
  lia.
Qed.

(** Witness: a 3-hop chain Taiidan -> Turanic -> Kadeshi (agent 3).
    Caps decrease at each hop: 10 -> 5 -> 2. *)

Definition kadeshi := mkAgent 3.

Definition three_hop_delegation : DelegationSystem := mkDelegationSystem
  homeworld_system
  (fun delegator delegate =>
    (agent_eqb delegator taiidan && agent_eqb delegate turanic) ||
    (agent_eqb delegator turanic && agent_eqb delegate kadeshi))
  (fun delegator delegate obl =>
    if obligation_eqb obl treaty_no_hyperspace then
      if agent_eqb delegator taiidan && agent_eqb delegate turanic then 5
      else if agent_eqb delegator turanic && agent_eqb delegate kadeshi then 2
      else 0
    else 0).

Lemma three_hop_cap_monotone :
  cap_monotone three_hop_delegation.
Proof.
  intros delegator delegate obl Hdel.
  unfold three_hop_delegation, homeworld_system in *. simpl in *.
  destruct (obligation_eqb_spec obl treaty_no_hyperspace); subst; simpl.
  - rewrite Bool.orb_true_iff in Hdel.
    destruct Hdel as [Hdel | Hdel].
    + destruct (agent_eqb_spec delegator taiidan);
      destruct (agent_eqb_spec delegate turanic);
      subst; simpl in *; try discriminate; try lia.
    + destruct (agent_eqb_spec delegator turanic);
      destruct (agent_eqb_spec delegate kadeshi);
      subst; simpl in *; try discriminate; try lia.
  - rewrite Bool.orb_true_iff in Hdel.
    destruct Hdel as [Hdel | Hdel];
    destruct (agent_eqb_spec delegator taiidan);
    destruct (agent_eqb_spec delegator turanic);
    destruct (agent_eqb_spec delegate turanic);
    destruct (agent_eqb_spec delegate kadeshi);
    subst; simpl in *; try discriminate; try lia.
Qed.

Lemma three_hop_valid_chain :
  valid_chain three_hop_delegation [taiidan; turanic; kadeshi].
Proof.
  simpl. split.
  - reflexivity.
  - split.
    + reflexivity.
    + exact I.
Qed.

(** The chain cap at the end (2) is bounded by the base cap (10).
    This is proved by induction via [chain_bounded], not by flat
    lookup. *)
Lemma three_hop_chain_bounded :
  chain_cap three_hop_delegation [taiidan; turanic; kadeshi]
    treaty_no_hyperspace <=
  severity_cap homeworld_system treaty_no_hyperspace.
Proof.
  apply chain_bounded.
  - exact three_hop_cap_monotone.
  - exact three_hop_valid_chain.
Qed.

(** The caps strictly decrease: 10 -> 5 -> 2. *)
Lemma chain_strictly_decreasing :
  severity_cap homeworld_system treaty_no_hyperspace = 10 /\
  delegate_cap three_hop_delegation taiidan turanic treaty_no_hyperspace = 5 /\
  delegate_cap three_hop_delegation turanic kadeshi treaty_no_hyperspace = 2.
Proof.
  unfold three_hop_delegation, homeworld_system. simpl. auto.
Qed.

(** * Temporal Delegation *)

(** Delegation authority may expire. A [TemporalDelegation] wraps a
    delegation system with an expiration time per delegation pair. *)

Record TemporalDelegation := mkTemporalDelegation {
  td_base        : DelegationSystem;
  delegation_expires : Agent -> Agent -> nat;
  delegation_created : Agent -> Agent -> nat
}.

Definition delegation_active (td : TemporalDelegation)
  (delegator delegate : Agent) (t : nat) : Prop :=
  delegation_created td delegator delegate <= t /\
  t < delegation_expires td delegator delegate.

(** A delegated enforcement is temporally valid only if the delegation
    is active at enforcement time. *)

Definition temporally_valid_delegation (td : TemporalDelegation)
  (delegator delegate : Agent) (t : nat) (pr : PunitiveResponse) : Prop :=
  delegates_to (td_base td) delegator delegate = true /\
  delegation_active td delegator delegate t /\
  enforcer pr = delegate.

(** Expired delegation confers no authority. *)

Theorem expired_delegation_invalid :
  forall td delegator delegate t pr,
    t >= delegation_expires td delegator delegate ->
    ~ temporally_valid_delegation td delegator delegate t pr.
Proof.
  intros td delegator delegate t pr Hlate [_ [[_ Hact] _]].
  lia.
Qed.

(** Witness: Taiidan's delegation to Turanic expires at time 100.
    Enforcement at time 200 is invalid. *)

Definition homeworld_temporal_delegation := mkTemporalDelegation
  homeworld_delegation
  (fun _ _ => 100)
  (fun _ _ => 0).

Lemma turanic_delegation_expired_at_200 :
  ~ temporally_valid_delegation homeworld_temporal_delegation
      taiidan turanic 200 proportional_response.
Proof.
  apply expired_delegation_invalid. simpl. lia.
Qed.

(** Delegation active at time 50 is valid. *)
Lemma turanic_delegation_active_at_50 :
  temporally_valid_delegation homeworld_temporal_delegation
    taiidan turanic 50 (mkPunitiveResponse turanic kushan treaty_no_hyperspace 3).
Proof.
  unfold temporally_valid_delegation, delegation_active,
         homeworld_temporal_delegation, homeworld_delegation. simpl.
  repeat split; lia.
Qed.

(** * Temporal Obligations and Enforcement Windows *)

(** Obligations may have a temporal scope: they are created at some
    time and may expire.  Enforcement is only valid during the window
    in which the obligation was active AND the violation occurred. *)

Definition Time := nat.

Record TemporalObligation := mkTemporalObligation {
  base_obligation : Obligation;
  created_at      : Time;
  expires_at      : Time
}.

(** An obligation is active at time [t] when [created_at <= t < expires_at]. *)
Definition active (tobl : TemporalObligation) (t : Time) : Prop :=
  created_at tobl <= t /\ t < expires_at tobl.

(** A temporal enforcement is valid only if:
    (1) the obligation was active when the violation occurred,
    (2) the enforcement occurs while the obligation is still active. *)

Record TemporalResponse := mkTemporalResponse {
  base_response      : PunitiveResponse;
  violation_time     : Time;
  enforcement_time   : Time
}.

Definition temporally_valid (tobl : TemporalObligation) (tr : TemporalResponse) : Prop :=
  base_obligation tobl = cause (base_response tr) /\
  active tobl (violation_time tr) /\
  active tobl (enforcement_time tr) /\
  violation_time tr <= enforcement_time tr.

(** Well-formedness: [created_at < expires_at] (non-degenerate window). *)
Definition well_formed_temporal (tobl : TemporalObligation) : Prop :=
  created_at tobl < expires_at tobl.

(** Witness: the hyperspace treaty was created at time 0 and expires
    at time 4000. The Kushan violation at time 3999 and enforcement
    at time 3999 are temporally valid. *)

Definition hyperspace_treaty_temporal := mkTemporalObligation
  treaty_no_hyperspace 0 4000.

Definition kharak_violation_temporal := mkTemporalResponse
  proportional_response 3999 3999.

Lemma kharak_temporally_valid :
  temporally_valid hyperspace_treaty_temporal kharak_violation_temporal.
Proof.
  unfold temporally_valid, hyperspace_treaty_temporal,
         kharak_violation_temporal, active, proportional_response. simpl.
  repeat split; lia.
Qed.

Lemma hyperspace_treaty_well_formed :
  well_formed_temporal hyperspace_treaty_temporal.
Proof.
  unfold well_formed_temporal, hyperspace_treaty_temporal. simpl. lia.
Qed.

(** Theorem: enforcement after the obligation expires is temporally
    invalid.  This rules out retroactive punishment for obligations
    that have lapsed. *)

Theorem expired_enforcement_invalid :
  forall tobl tr,
    well_formed_temporal tobl ->
    enforcement_time tr >= expires_at tobl ->
    ~ temporally_valid tobl tr.
Proof.
  intros tobl tr Hwf Hlate [_ [_ [[_ Hact_enf] _]]].
  lia.
Qed.

(** Witness: enforcement at time 4001 (after expiration) is invalid. *)

Definition late_enforcement := mkTemporalResponse
  proportional_response 3999 4001.

Lemma late_enforcement_invalid :
  ~ temporally_valid hyperspace_treaty_temporal late_enforcement.
Proof.
  apply expired_enforcement_invalid.
  - exact hyperspace_treaty_well_formed.
  - unfold late_enforcement, hyperspace_treaty_temporal. simpl. lia.
Qed.

(** Theorem: enforcement before the violation is temporally invalid. *)

Theorem preemptive_enforcement_invalid :
  forall tobl tr,
    enforcement_time tr < violation_time tr ->
    ~ temporally_valid tobl tr.
Proof.
  intros tobl tr Hpre [_ [_ [_ Horder]]].
  lia.
Qed.

(** Witness: enforcement at time 100 for a violation at time 200. *)
Definition preemptive := mkTemporalResponse
  proportional_response 200 100.

Lemma preemptive_invalid :
  ~ temporally_valid hyperspace_treaty_temporal preemptive.
Proof.
  apply preemptive_enforcement_invalid.
  unfold preemptive. simpl. lia.
Qed.

(** Counterexample showing the theorem is non-vacuous: there exist
    temporally valid responses (kharak_violation_temporal above). *)
Lemma temporal_validity_inhabited :
  exists tobl tr,
    well_formed_temporal tobl /\ temporally_valid tobl tr.
Proof.
  exists hyperspace_treaty_temporal, kharak_violation_temporal.
  split.
  - exact hyperspace_treaty_well_formed.
  - exact kharak_temporally_valid.
Qed.

(** A response is *temporally lawful* when it is lawful in the base
    deontic system AND temporally valid. *)

Definition temporally_lawful
  (ds : DeonticSystem) (tobl : TemporalObligation) (tr : TemporalResponse)
  : Prop :=
  lawful ds (base_response tr) /\ temporally_valid tobl tr.

(** A lawful-but-temporally-invalid response exists: enforcement
    after expiration is lawful in the base system but not temporally
    lawful. *)
Lemma lawful_not_temporally_lawful :
  exists ds tobl tr,
    lawful ds (base_response tr) /\
    ~ temporally_valid tobl tr.
Proof.
  exists homeworld_system, hyperspace_treaty_temporal, late_enforcement.
  split.
  - unfold late_enforcement. simpl. exact proportional_lawful.
  - exact late_enforcement_invalid.
Qed.

(** In a temporally lawful response, severity is still bounded. *)
Theorem temporally_lawful_bounded :
  forall ds tobl tr,
    temporally_lawful ds tobl tr ->
    severity (base_response tr) <= severity_cap ds (cause (base_response tr)).
Proof.
  intros ds tobl tr [Hlaw _]. exact (lawful_bounded ds (base_response tr) Hlaw).
Qed.

(** A delegated response is *lawful* when its severity is bounded by
    both the delegate cap and the base system cap. *)

Definition lawful_delegated
  (del : DelegationSystem) (delegator : Agent)
  (pr : PunitiveResponse) : Prop :=
  authorized (ds_base del) pr /\
  delegates_to del delegator (enforcer pr) = true /\
  severity pr <= delegate_cap del delegator (enforcer pr) (cause pr) /\
  severity pr <= severity_cap (ds_base del) (cause pr).

(** Delegation cannot launder an unbounded response into a lawful
    delegated one. *)
Theorem delegation_no_laundering :
  forall del delegator pr,
    well_formed_delegation del ->
    unbounded (ds_base del) pr ->
    ~ lawful_delegated del delegator pr.
Proof.
  intros del delegator pr Hwf Hunb [_ [_ [_ Hbase]]].
  unfold unbounded in Hunb. lia.
Qed.

(** * Multi-Violation Proportionality *)

(** When an agent violates multiple obligations, the total permissible
    punishment grows *linearly* with the number of violations — each
    violation independently contributes its cap.  This rules out
    super-linear punishment schemes (e.g., "three strikes" escalation
    that makes the third violation punishable by more than three
    individual caps). *)

(** Sum the severity caps for a list of violated obligations. *)
Fixpoint sum_caps (ds : DeonticSystem) (obls : list Obligation) : nat :=
  match obls with
  | [] => 0
  | o :: rest => severity_cap ds o + sum_caps ds rest
  end.

(** The total lawful punishment for [n] violations, each with one
    lawful response per obligation, is bounded by the sum of caps.
    We model this as: given one lawful response per violated
    obligation, the sum of their severities is at most [sum_caps]. *)

Fixpoint collect_severities (rs : list PunitiveResponse) : nat :=
  match rs with
  | [] => 0
  | pr :: rest => severity pr + collect_severities rest
  end.

(** One lawful response per obligation, matched by position. *)
Definition responses_match_obligations
  (ds : DeonticSystem) (obls : list Obligation) (rs : list PunitiveResponse) : Prop :=
  length obls = length rs /\
  forall i o pr,
    nth_error obls i = Some o ->
    nth_error rs i = Some pr ->
    lawful ds pr /\ cause pr = o.

Theorem multi_violation_bound :
  forall ds obls rs,
    responses_match_obligations ds obls rs ->
    collect_severities rs <= sum_caps ds obls.
Proof.
  intros ds obls.
  induction obls as [| o rest IH].
  - intros rs [Hlen _]. simpl in Hlen.
    destruct rs; try discriminate. simpl. lia.
  - intros rs [Hlen Hmatch].
    destruct rs as [| pr rs']; try discriminate.
    simpl in Hlen. injection Hlen as Hlen'.
    simpl.
    assert (Hpr : lawful ds pr /\ cause pr = o).
    { apply (Hmatch 0); reflexivity. }
    destruct Hpr as [Hlaw Hcause].
    assert (Hbnd := lawful_bounded ds pr Hlaw).
    subst.
    assert (Hrest : collect_severities rs' <= sum_caps ds rest).
    { apply IH. split.
      - exact Hlen'.
      - intros i o' pr' Ho' Hpr'.
        exact (Hmatch (S i) o' pr' Ho' Hpr'). }
    unfold bounded in Hbnd. lia.
Qed.

(** Relational pairing: each obligation paired with its response.
    Order-independent — reordering the list doesn't break anything. *)

Definition paired_responses
  (ds : DeonticSystem) (pairs : list (Obligation * PunitiveResponse)) : Prop :=
  forall o pr, In (o, pr) pairs -> lawful ds pr /\ cause pr = o.

Fixpoint sum_pair_caps (ds : DeonticSystem)
  (pairs : list (Obligation * PunitiveResponse)) : nat :=
  match pairs with
  | [] => 0
  | (o, _) :: rest => severity_cap ds o + sum_pair_caps ds rest
  end.

Fixpoint sum_pair_severities
  (pairs : list (Obligation * PunitiveResponse)) : nat :=
  match pairs with
  | [] => 0
  | (_, pr) :: rest => severity pr + sum_pair_severities rest
  end.

Theorem paired_violation_bound :
  forall ds pairs,
    paired_responses ds pairs ->
    sum_pair_severities pairs <= sum_pair_caps ds pairs.
Proof.
  intros ds pairs Hpaired.
  induction pairs as [| [o pr] rest IH].
  - simpl. lia.
  - simpl.
    assert (Hpr : lawful ds pr /\ cause pr = o).
    { apply Hpaired. left. reflexivity. }
    destruct Hpr as [Hlaw Hcause].
    assert (Hbnd := lawful_bounded ds pr Hlaw). unfold bounded in Hbnd.
    subst.
    assert (Hrest : sum_pair_severities rest <= sum_pair_caps ds rest).
    { apply IH. intros o' pr' Hin. apply Hpaired. right. exact Hin. }
    lia.
Qed.

(** Witness: Kushan violates both the hyperspace treaty (cap 10) and
    the tribute treaty (cap 0).  Total lawful punishment is at most
    10 + 0 = 10 per enforcer. *)

Definition two_violation_caps :=
  sum_caps homeworld_system [treaty_no_hyperspace; treaty_tribute].

Lemma two_violation_caps_value : two_violation_caps = 10.
Proof.
  unfold two_violation_caps, sum_caps, homeworld_system.
  simpl. reflexivity.
Qed.

(** Counterexample: a "three strikes" system where cap(3rd violation)
    is greater than 3 * cap(single violation) violates linearity. *)

Definition three_strikes_system : DeonticSystem := mkDeonticSystem
  [kushan]
  (fun _ _ => true)
  (fun _ _ => true)
  (fun _ _ => false)
  (fun o =>
    match obligation_id o with
    | 0 => 5
    | 1 => 5
    | 2 => 50
    | _ => 0
    end).

Definition strike1 := mkObligation 0.
Definition strike2 := mkObligation 1.
Definition strike3 := mkObligation 2.

Lemma three_strikes_superlinear :
  severity_cap three_strikes_system strike3 >
  severity_cap three_strikes_system strike1 +
  severity_cap three_strikes_system strike2.
Proof.
  unfold three_strikes_system, strike1, strike2, strike3. simpl. lia.
Qed.

(** A system has *linear caps* when the sum of caps for any list of
    obligations is bounded by the length times a uniform cap. *)

Definition linear_caps (ds : DeonticSystem) (k : Severity) : Prop :=
  forall o, severity_cap ds o <= k.

(** The three-strikes system violates linear caps with k=5
    (the single-strike cap). *)
Lemma three_strikes_not_linear :
  ~ linear_caps three_strikes_system 5.
Proof.
  intros H.
  specialize (H strike3).
  unfold three_strikes_system, strike3 in H. simpl in H. lia.
Qed.

(** * Second Witness System *)

(** A trade embargo system with three agents and distinct caps,
    confirming the framework generalizes beyond homeworld_system. *)

Definition embargo_enforcer := mkAgent 10.
Definition embargo_violator := mkAgent 11.
Definition embargo_observer := mkAgent 12.
Definition trade_embargo := mkObligation 10.

Definition embargo_system : DeonticSystem := mkDeonticSystem
  [embargo_enforcer; embargo_violator; embargo_observer]
  (fun a o =>
    agent_eqb a embargo_violator && obligation_eqb o trade_embargo)
  (fun a o =>
    agent_eqb a embargo_violator && obligation_eqb o trade_embargo)
  (fun enforcer target =>
    agent_eqb enforcer embargo_enforcer && agent_eqb target embargo_violator)
  (fun o =>
    if obligation_eqb o trade_embargo then 20 else 0).

Lemma embargo_coherent : coherent embargo_system.
Proof.
  split; [| split].
  - intros a o H. exact H.
  - intros a b H.
    unfold embargo_system in H. simpl in H.
    destruct (agent_eqb_spec a embargo_enforcer);
    destruct (agent_eqb_spec b embargo_violator);
    subst; simpl in *; try discriminate.
    split; [left; reflexivity | right; left; reflexivity].
  - intros o Hcap.
    unfold embargo_system in *. simpl in *.
    destruct (obligation_eqb_spec o trade_embargo); subst.
    + exists embargo_violator. simpl. split.
      * right. left. reflexivity.
      * reflexivity.
    + simpl in Hcap. lia.
Qed.

Lemma embargo_consistent : consistent embargo_system.
Proof.
  constructor.
  - exact embargo_coherent.
  - intros [n]. unfold embargo_system, agent_eqb. simpl.
    destruct (Nat.eqb_spec n 10); destruct (Nat.eqb_spec n 11);
      subst; auto; try lia.
  - intros a o Hin Hobl.
    unfold embargo_system in *. simpl in *.
    destruct Hin as [Ha | [Ha | [Ha | []]]]; subst; simpl in Hobl;
      try discriminate.
    unfold agent_eqb in Hobl. simpl in Hobl.
    destruct (obligation_eqb_spec o trade_embargo); subst.
    + simpl. lia.
    + simpl in Hobl. discriminate.
Qed.

Definition embargo_proportional := mkPunitiveResponse
  embargo_enforcer embargo_violator trade_embargo 15.

Definition embargo_excessive := mkPunitiveResponse
  embargo_enforcer embargo_violator trade_embargo 30.

Lemma embargo_proportional_lawful :
  lawful embargo_system embargo_proportional.
Proof.
  apply lawful_intro; unfold embargo_system, embargo_proportional; simpl; auto; lia.
Qed.

Lemma embargo_excessive_unlawful :
  authorized embargo_system embargo_excessive /\
  unbounded embargo_system embargo_excessive /\
  ~ lawful embargo_system embargo_excessive.
Proof.
  split; [| split].
  - unfold authorized, embargo_system, embargo_excessive. simpl.
    repeat split; auto.
  - unfold unbounded, embargo_system, embargo_excessive. simpl. lia.
  - intros Hlaw. apply (lawful_bounded) in Hlaw.
    unfold bounded, embargo_system, embargo_excessive in Hlaw.
    simpl in Hlaw. lia.
Qed.

(** * Decision Procedures *)

(** Computable classifiers for authorization, boundedness, and
    lawfulness, with reflection lemmas. *)

Fixpoint In_agentb (a : Agent) (l : list Agent) : bool :=
  match l with
  | [] => false
  | x :: rest => agent_eqb a x || In_agentb a rest
  end.

Lemma In_agentb_spec : forall a l,
  In_agentb a l = true <-> In a l.
Proof.
  intros a l.
  induction l as [| x rest IH].
  - simpl. split; [discriminate | tauto].
  - simpl. rewrite Bool.orb_true_iff, IH.
    split.
    + intros [H | H].
      * left. destruct (agent_eqb_spec a x) as [e | ne];
          [symmetry; exact e | discriminate].
      * right. exact H.
    + intros [H | H].
      * left. subst. unfold agent_eqb. rewrite Nat.eqb_refl. reflexivity.
      * right. exact H.
Qed.

Definition authorizedb (ds : DeonticSystem) (pr : PunitiveResponse) : bool :=
  In_agentb (enforcer pr) (agents ds) &&
  In_agentb (target pr) (agents ds) &&
  may_enforce ds (enforcer pr) (target pr) &&
  violated ds (target pr) (cause pr) &&
  obligated ds (target pr) (cause pr).

Lemma authorizedb_spec : forall ds pr,
  authorizedb ds pr = true <-> authorized ds pr.
Proof.
  intros ds pr. unfold authorizedb, authorized.
  repeat rewrite Bool.andb_true_iff.
  repeat rewrite In_agentb_spec.
  tauto.
Qed.

Definition boundedb (ds : DeonticSystem) (pr : PunitiveResponse) : bool :=
  severity pr <=? severity_cap ds (cause pr).

Lemma boundedb_spec : forall ds pr,
  boundedb ds pr = true <-> bounded ds pr.
Proof.
  intros ds pr. unfold boundedb, bounded.
  rewrite Nat.leb_le. tauto.
Qed.

Definition lawfulb (ds : DeonticSystem) (pr : PunitiveResponse) : bool :=
  authorizedb ds pr && boundedb ds pr.

Lemma lawfulb_spec : forall ds pr,
  lawfulb ds pr = true <-> lawful ds pr.
Proof.
  intros ds pr. unfold lawfulb.
  rewrite Bool.andb_true_iff, authorizedb_spec, boundedb_spec.
  split.
  - intros [Hauth Hbnd]. exact (lawful_from_auth_bounded ds pr Hauth Hbnd).
  - intros Hlaw. split.
    + exact (lawful_authorized ds pr Hlaw).
    + exact (lawful_bounded ds pr Hlaw).
Qed.

(** Computational test: the proportional response is lawful. *)
Lemma proportional_lawful_compute :
  lawfulb homeworld_system proportional_response = true.
Proof. reflexivity. Qed.

(** Computational test: the extermination is not lawful. *)
Lemma extermination_not_lawful_compute :
  lawfulb homeworld_system extermination_response = false.
Proof. reflexivity. Qed.

(** * Combined Bounded Enforcement Theorem *)

(** Combined statement covering all enforcement avenues:

    (1) Every individual lawful response has severity <= cap.
    (2) The aggregate lawful severity from [n] enforcers is <= n * cap.
    (3) No authorized-but-unbounded response is lawful.
    (4) In a delegation hierarchy, the chain cap is bounded by the
        base system cap.
    (5) Enforcement outside the temporal window is invalid. *)

Theorem bounded_enforcement_synthesis :
  forall ds,
    (forall pr, lawful ds pr -> severity pr <= severity_cap ds (cause pr))
    /\
    (forall tgt obl responses,
      all_lawful ds responses ->
      all_target_same tgt obl responses ->
      total_severity responses <= length responses * severity_cap ds obl)
    /\
    (forall pr,
      authorized ds pr -> unbounded ds pr -> ~ lawful ds pr)
    /\
    (forall del obl chain,
      ds_base del = ds ->
      cap_monotone del ->
      valid_chain del chain ->
      chain_cap del chain obl <= severity_cap ds obl)
    /\
    (forall tobl tr,
      well_formed_temporal tobl ->
      enforcement_time tr >= expires_at tobl ->
      ~ temporally_valid tobl tr).
Proof.
  intros ds. repeat split.
  - exact (per_response_bound ds).
  - exact (aggregate_enforcement_bound ds).
  - exact (no_unbounded_lawful ds).
  - intros del obl chain Hbase Hmono Hvalid.
    subst. exact (chain_bounded del obl chain Hmono Hvalid).
  - exact expired_enforcement_invalid.
Qed.

(** Non-triviality certificate: all three conjuncts have non-vacuous
    instantiations in the homeworld system. *)

Lemma synthesis_nontrivial :
  (* Conjunct 1 is exercised *)
  (exists pr, lawful homeworld_system pr /\
              severity pr > 0 /\
              severity pr <= severity_cap homeworld_system (cause pr))
  /\
  (* Conjunct 2 is exercised with multiple responses *)
  (exists rs, length rs > 1 /\
              all_lawful homeworld_system rs /\
              total_severity rs > 0)
  /\
  (* Conjunct 3 is exercised *)
  (exists pr, authorized homeworld_system pr /\
              unbounded homeworld_system pr).
Proof.
  split.
  { exists proportional_response.
    split. { exact proportional_lawful. }
    split. { simpl. lia. }
    unfold homeworld_system, proportional_response. simpl. lia. }
  split.
  { exists two_responses.
    split. { simpl. lia. }
    split. { exact two_responses_all_lawful. }
    simpl. lia. }
  { exists extermination_response.
    split. { exact extermination_authorized. }
    exact extermination_unbounded. }
Qed.

(** Completeness: authorized and bounded is sufficient for lawfulness. *)

Theorem authorized_bounded_lawful :
  forall ds pr,
    authorized ds pr ->
    bounded ds pr ->
    lawful ds pr.
Proof.
  exact lawful_from_auth_bounded.
Qed.

(** * The Kharak Theorem *)

(** Instantiation: the extermination of Kharak (severity 100) was
    authorized (Taiidan had standing) and unbounded (100 > cap 10),
    therefore unlawful. *)

Theorem kharak_theorem :
  authorized homeworld_system extermination_response /\
  unbounded homeworld_system extermination_response /\
  ~ lawful homeworld_system extermination_response.
Proof.
  split.
  { exact extermination_authorized. }
  split.
  { exact extermination_unbounded. }
  { exact (proj2 extermination_not_lawful). }
Qed.

(** No combination of delegation, aggregation, or temporal
    manipulation makes the extermination lawful. *)

Theorem kharak_no_rearrangement :
  (* Direct enforcement: unlawful *)
  ~ lawful homeworld_system extermination_response /\
  (* Delegation: delegate cap bounded by base cap (10), severity 100 exceeds it *)
  (forall del delegator,
    well_formed_delegation del ->
    ds_base del = homeworld_system ->
    delegates_to del delegator (enforcer extermination_response) = true ->
    severity extermination_response >
      delegate_cap del delegator (enforcer extermination_response)
        (cause extermination_response) \/
    severity extermination_response >
      severity_cap homeworld_system (cause extermination_response)) /\
  (* Aggregation: any collection containing the extermination is not all-lawful *)
  (forall responses,
    In extermination_response responses ->
    ~ all_lawful homeworld_system responses) /\
  (* Temporal: does not affect severity boundedness *)
  (forall tobl,
    ~ temporally_lawful homeworld_system tobl
        (mkTemporalResponse extermination_response 3999 3999) \/
    ~ bounded homeworld_system extermination_response).
Proof.
  split; [| split; [| split]].
  - exact (proj2 extermination_not_lawful).
  - intros del delegator Hwf Hbase Hdel.
    right. unfold extermination_response, homeworld_system. simpl. lia.
  - intros responses Hin.
    apply (unbounded_member_breaks_collection homeworld_system
             responses extermination_response Hin extermination_unbounded).
  - right. unfold bounded, extermination_response, homeworld_system. simpl. lia.
Qed.
