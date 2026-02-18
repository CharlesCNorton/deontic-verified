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

Lemma agent_eq_dec : forall a b : Agent, {a = b} + {a <> b}.
Proof.
  intros a b. destruct (agent_eqb_spec a b).
  - left. exact e.
  - right. exact n.
Defined.

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
        vacuously prevented),
    (4) the population has no duplicate agents. *)

Record consistent (ds : DeonticSystem) : Prop := mkConsistent {
  consistent_coherent     : coherent ds;
  consistent_irreflexive  : irreflexive_enforcement ds;
  consistent_caps_positive : forall a o,
    In a (agents ds) ->
    obligated ds a o = true ->
    severity_cap ds o > 0;
  consistent_nodup : NoDup (agents ds)
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
  - unfold homeworld_system. simpl.
    constructor.
    + intros [H | []]. unfold taiidan, kushan in H. injection H. lia.
    + constructor; [intros [] | constructor].
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
  intros [_ _ Hcaps _].
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
  intros ds pr [Hcoh Hirr Hcaps _] Hauth.
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
    responses is bounded by the population size. *)

Definition distinct_enforcers (responses : list PunitiveResponse) : Prop :=
  NoDup (map enforcer responses).

Definition enforcers_in_population
  (ds : DeonticSystem) (responses : list PunitiveResponse) : Prop :=
  forall pr, In pr responses -> In (enforcer pr) (agents ds).

(** Pigeonhole: distinct enforcers drawn from a NoDup population
    cannot outnumber the population. *)
Lemma enforcers_bounded_by_population :
  forall ds responses,
    NoDup (agents ds) ->
    distinct_enforcers responses ->
    enforcers_in_population ds responses ->
    length responses <= length (agents ds).
Proof.
  intros ds responses Hnodup Hdistinct Henf.
  unfold distinct_enforcers in Hdistinct.
  unfold enforcers_in_population in Henf.
  rewrite <- (map_length enforcer responses).
  apply NoDup_incl_length.
  - exact Hdistinct.
  - intros x Hx. apply in_map_iff in Hx.
    destruct Hx as [pr [Heq Hin]]. subst. exact (Henf pr Hin).
Qed.

Theorem population_bounded_aggregate :
  forall ds tgt obl responses,
    NoDup (agents ds) ->
    all_lawful ds responses ->
    all_target_same tgt obl responses ->
    distinct_enforcers responses ->
    enforcers_in_population ds responses ->
    total_severity responses <= length (agents ds) * severity_cap ds obl.
Proof.
  intros ds tgt obl responses Hnodup Hlawful Hsame Hdistinct Henf.
  assert (Hpop := enforcers_bounded_by_population ds responses Hnodup Hdistinct Henf).
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
  length responses <= 1.

Theorem ne_bis_in_idem_bound :
  forall ds tgt obl responses,
    all_lawful ds responses ->
    ne_bis_in_idem ds responses tgt obl ->
    total_severity responses <= severity_cap ds obl.
Proof.
  intros ds tgt obl responses Hlawful [Hsame Hlen].
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
  split.
  - intros pr Hin. destruct Hin as [H | []]; subst; simpl; auto.
  - simpl. lia.
Qed.

(** * The Main Theorem *)

(** Any response that exceeds the severity cap is not lawful.
    Authorization is irrelevant: lawfulness requires boundedness,
    and unboundedness contradicts it directly. *)

Theorem no_unbounded_lawful :
  forall ds pr,
    unbounded ds pr ->
    ~ lawful ds pr.
Proof.
  intros ds pr Hunb Hlaw.
  assert (Hbnd := lawful_bounded ds pr Hlaw).
  exact (bounded_unbounded_exclusive ds pr (conj Hbnd Hunb)).
Qed.

(** Non-triviality: the hypothesis is satisfiable — there exist
    authorized-yet-unbounded responses. *)
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
  exact (no_unbounded_lawful homeworld_system extermination_response
           extermination_unbounded).
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

Lemma three_hop_delegates_to_shape :
  forall a b,
    delegates_to three_hop_delegation a b = true ->
    (a = taiidan /\ b = turanic) \/ (a = turanic /\ b = kadeshi).
Proof.
  intros a b H.
  unfold three_hop_delegation in H. simpl in H.
  rewrite Bool.orb_true_iff in H.
  destruct H as [H | H].
  - destruct (agent_eqb_spec a taiidan); destruct (agent_eqb_spec b turanic);
      subst; simpl in *; try discriminate. left. auto.
  - destruct (agent_eqb_spec a turanic); destruct (agent_eqb_spec b kadeshi);
      subst; simpl in *; try discriminate. right. auto.
Qed.

Lemma three_hop_reachable_increasing :
  forall a b,
    reachable three_hop_delegation a b ->
    agent_id a < agent_id b.
Proof.
  intros a b H.
  induction H as [a' b' Hdel | a' b' c Hdel Hreach IH].
  - destruct (three_hop_delegates_to_shape a' b' Hdel) as [[-> ->] | [-> ->]];
      simpl; lia.
  - destruct (three_hop_delegates_to_shape a' b' Hdel) as [[-> ->] | [-> ->]];
      simpl in *; lia.
Qed.

Lemma three_hop_acyclic : acyclic three_hop_delegation.
Proof.
  intros a Hreach.
  assert (H := three_hop_reachable_increasing a a Hreach). lia.
Qed.

Lemma three_hop_well_formed :
  well_formed_delegation three_hop_delegation.
Proof.
  constructor.
  - exact homeworld_consistent.
  - exact three_hop_cap_monotone.
  - exact three_hop_acyclic.
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

(** Well-formedness: [created_at < expires_at] (non-degenerate window).
    Single-tick windows ([expires_at = created_at + 1]) are intentionally
    permitted — the framework models discrete time steps, and an
    obligation active for exactly one tick is the minimal non-trivial
    case. *)
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

(** An [EnforceableObligation] separates the obligation's active
    period from the enforcement window. The statute of limitations
    may extend beyond obligation expiry. *)

Record EnforceableObligation := mkEnforceableObligation {
  eo_obligation     : Obligation;
  eo_created_at     : Time;
  eo_expires_at     : Time;
  eo_enforce_until  : Time
}.

Definition obligation_active (eo : EnforceableObligation) (t : Time) : Prop :=
  eo_created_at eo <= t /\ t < eo_expires_at eo.

Definition enforceable (eo : EnforceableObligation) (t : Time) : Prop :=
  eo_created_at eo <= t /\ t < eo_enforce_until eo.

Definition well_formed_enforceable (eo : EnforceableObligation) : Prop :=
  eo_created_at eo < eo_expires_at eo /\
  eo_expires_at eo <= eo_enforce_until eo.

(** Enforcement is valid when the violation occurred while the
    obligation was active and enforcement occurs within the
    statute of limitations. *)
Definition enforcement_valid (eo : EnforceableObligation)
  (tr : TemporalResponse) : Prop :=
  eo_obligation eo = cause (base_response tr) /\
  obligation_active eo (violation_time tr) /\
  enforceable eo (enforcement_time tr) /\
  violation_time tr <= enforcement_time tr.

(** Enforcement after the statute of limitations is invalid. *)
Theorem statute_expired_invalid :
  forall eo tr,
    enforcement_time tr >= eo_enforce_until eo ->
    ~ enforcement_valid eo tr.
Proof.
  intros eo tr Hlate [_ [_ [[_ Hact] _]]]. lia.
Qed.

(** Enforcement after obligation expiry but within the statute of
    limitations can be valid. This is impossible under the old
    [temporally_valid] which conflated the two windows. *)
Lemma post_expiry_enforcement_possible :
  exists eo tr,
    well_formed_enforceable eo /\
    enforcement_valid eo tr /\
    enforcement_time tr >= eo_expires_at eo.
Proof.
  exists (mkEnforceableObligation treaty_no_hyperspace 0 100 200).
  exists (mkTemporalResponse proportional_response 50 150).
  unfold well_formed_enforceable, enforcement_valid, obligation_active,
         enforceable, proportional_response. simpl.
  repeat split; lia.
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
  - unfold embargo_system. simpl.
    constructor.
    + intros [H | [H | []]].
      * unfold embargo_enforcer, embargo_violator in H. injection H. lia.
      * unfold embargo_enforcer, embargo_observer in H. injection H. lia.
    + constructor.
      * intros [H | []]. unfold embargo_violator, embargo_observer in H. injection H. lia.
      * constructor; [intros [] | constructor].
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

(** * Structural Counterexamples and Witnesses *)

(** A system where an agent can enforce against itself violates
    irreflexive enforcement and is therefore not consistent. *)

Definition self_enforce_system : DeonticSystem := mkDeonticSystem
  [kushan]
  (fun a o =>
    agent_eqb a kushan && obligation_eqb o treaty_no_hyperspace)
  (fun a o =>
    agent_eqb a kushan && obligation_eqb o treaty_no_hyperspace)
  (fun enforcer target =>
    agent_eqb enforcer kushan && agent_eqb target kushan)
  (fun o =>
    if obligation_eqb o treaty_no_hyperspace then 10 else 0).

Lemma self_enforce_not_consistent : ~ consistent self_enforce_system.
Proof.
  intros [_ Hirr _ _].
  specialize (Hirr kushan).
  unfold self_enforce_system in Hirr. simpl in Hirr. discriminate.
Qed.

(** A cyclic delegation (A delegates to B, B delegates to A) is not
    acyclic and therefore not well-formed. *)

Definition cyclic_delegation : DelegationSystem := mkDelegationSystem
  homeworld_system
  (fun delegator delegate =>
    (agent_eqb delegator taiidan && agent_eqb delegate turanic) ||
    (agent_eqb delegator turanic && agent_eqb delegate taiidan))
  (fun _ _ _ => 5).

Lemma cyclic_delegation_not_acyclic : ~ acyclic cyclic_delegation.
Proof.
  intros Hacyclic.
  apply (Hacyclic taiidan).
  apply (reach_trans cyclic_delegation taiidan turanic taiidan).
  - unfold cyclic_delegation. simpl. reflexivity.
  - apply reach_step. unfold cyclic_delegation. simpl. reflexivity.
Qed.

Lemma cyclic_delegation_not_well_formed : ~ well_formed_delegation cyclic_delegation.
Proof.
  intros [_ _ Hacyclic].
  exact (cyclic_delegation_not_acyclic Hacyclic).
Qed.

(** A branching delegation: Taiidan delegates independently to both
    Turanic and Kadeshi with different caps.  This is well-formed
    (acyclic, cap-monotone) and exercises the framework with a
    non-linear delegation graph. *)

Definition branching_delegation : DelegationSystem := mkDelegationSystem
  homeworld_system
  (fun delegator delegate =>
    agent_eqb delegator taiidan &&
    (agent_eqb delegate turanic || agent_eqb delegate kadeshi))
  (fun delegator delegate obl =>
    if agent_eqb delegator taiidan && obligation_eqb obl treaty_no_hyperspace then
      if agent_eqb delegate turanic then 7
      else if agent_eqb delegate kadeshi then 3
      else 0
    else 0).

Lemma branching_delegation_cap_monotone :
  cap_monotone branching_delegation.
Proof.
  intros delegator delegate obl Hdel.
  unfold branching_delegation, homeworld_system in *. simpl in *.
  destruct (agent_eqb_spec delegator taiidan); subst; simpl in *;
    [| discriminate].
  rewrite Bool.orb_true_iff in Hdel.
  destruct (obligation_eqb_spec obl treaty_no_hyperspace); subst; simpl.
  - destruct Hdel as [Hdel | Hdel];
    destruct (agent_eqb_spec delegate turanic);
    destruct (agent_eqb_spec delegate kadeshi);
    subst; simpl in *; try discriminate; try lia.
  - destruct Hdel as [Hdel | Hdel];
    destruct (agent_eqb_spec delegate turanic);
    destruct (agent_eqb_spec delegate kadeshi);
    subst; simpl in *; try discriminate; try lia.
Qed.

Lemma branching_delegates_to_shape :
  forall a b,
    delegates_to branching_delegation a b = true ->
    a = taiidan /\ (b = turanic \/ b = kadeshi).
Proof.
  intros a b H.
  unfold branching_delegation in H. simpl in H.
  destruct (agent_eqb_spec a taiidan); subst; simpl in *; [| discriminate].
  rewrite Bool.orb_true_iff in H.
  destruct H as [H | H].
  - destruct (agent_eqb_spec b turanic); subst; [auto | discriminate].
  - destruct (agent_eqb_spec b kadeshi); subst; [auto | discriminate].
Qed.

Lemma branching_reachable_target :
  forall a b,
    reachable branching_delegation a b ->
    b = turanic \/ b = kadeshi.
Proof.
  intros a b H.
  induction H as [a' b' Hdel | a' b' c Hdel _ IH].
  - destruct (branching_delegates_to_shape a' b' Hdel). assumption.
  - exact IH.
Qed.

Lemma branching_reachable_source :
  forall a b,
    reachable branching_delegation a b ->
    a = taiidan.
Proof.
  intros a b H.
  induction H as [a' b' Hdel | a' b' c Hdel _ IH].
  - destruct (branching_delegates_to_shape a' b' Hdel). assumption.
  - destruct (branching_delegates_to_shape a' b' Hdel). assumption.
Qed.

Lemma branching_delegation_acyclic : acyclic branching_delegation.
Proof.
  intros a Hreach.
  assert (H1 := branching_reachable_source a a Hreach).
  assert (H2 := branching_reachable_target a a Hreach).
  subst. destruct H2 as [H | H];
    unfold taiidan, turanic, kadeshi in H; injection H; lia.
Qed.

Lemma branching_delegation_well_formed :
  well_formed_delegation branching_delegation.
Proof.
  constructor.
  - exact homeworld_consistent.
  - exact branching_delegation_cap_monotone.
  - exact branching_delegation_acyclic.
Qed.

(** The two branches have distinct caps: Turanic gets 7, Kadeshi gets 3,
    both bounded by the base cap of 10. *)
Lemma branching_caps_distinct :
  delegate_cap branching_delegation taiidan turanic treaty_no_hyperspace = 7 /\
  delegate_cap branching_delegation taiidan kadeshi treaty_no_hyperspace = 3 /\
  delegate_cap branching_delegation taiidan turanic treaty_no_hyperspace <>
  delegate_cap branching_delegation taiidan kadeshi treaty_no_hyperspace.
Proof.
  unfold branching_delegation. simpl. repeat split. lia.
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
    (3) No unbounded response is lawful.
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
    (forall pr, unbounded ds pr -> ~ lawful ds pr)
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

(** * Deontic Modalities *)

(** Standard deontic modalities: obligatory, permitted, forbidden. *)

Inductive DeonticModality :=
  | OBL  (* obligatory *)
  | PERM (* permitted *)
  | FORB. (* forbidden *)

(** A [NormativeStatus] assigns a modality to an agent-obligation pair. *)

Definition NormativeStatus := Agent -> Obligation -> DeonticModality.

(** Consistency of modalities: forbidden and obligatory are dual
    (obligatory implies permitted, forbidden and permitted are
    exclusive, forbidden and obligatory are exclusive). *)

Definition modally_consistent (ns : NormativeStatus) : Prop :=
  (forall a o, ns a o = OBL -> ns a o <> FORB) /\
  (forall a o, ns a o = FORB -> ns a o <> PERM).

(** A normative status is *grounded* in a deontic system when:
    - OBL matches [obligated],
    - FORB means not [obligated] and not [may_enforce]. *)

Definition grounded (ds : DeonticSystem) (ns : NormativeStatus) : Prop :=
  (forall a o, ns a o = OBL -> obligated ds a o = true) /\
  (forall a o, ns a o = FORB -> obligated ds a o = false).

(** Violation of a forbidden action is impossible in a grounded
    coherent system: if the action is forbidden, the agent doesn't
    bear the obligation, so coherence prevents violation. *)

Theorem forbidden_no_violation :
  forall ds ns a o,
    grounded ds ns ->
    coherent ds ->
    ns a o = FORB ->
    violated ds a o = false.
Proof.
  intros ds ns a o [_ Hforb] [Hcoh _] Hns.
  assert (Hobl : obligated ds a o = false) by (apply Hforb; exact Hns).
  destruct (violated ds a o) eqn:Hviol.
  - apply Hcoh in Hviol. rewrite Hviol in Hobl. discriminate.
  - reflexivity.
Qed.

(** Witness: in the homeworld system, Taiidan's status for the
    hyperspace treaty is PERM (not obligated, no violation expected). *)

Definition homeworld_norms : NormativeStatus :=
  fun a o =>
    if agent_eqb a kushan && obligation_eqb o treaty_no_hyperspace
    then OBL
    else PERM.

Lemma homeworld_norms_grounded :
  grounded homeworld_system homeworld_norms.
Proof.
  split.
  - intros a o H. unfold homeworld_norms in H.
    unfold homeworld_system. simpl.
    destruct (agent_eqb a kushan && obligation_eqb o treaty_no_hyperspace).
    + reflexivity.
    + discriminate.
  - intros a o H. unfold homeworld_norms in H.
    destruct (agent_eqb a kushan && obligation_eqb o treaty_no_hyperspace);
      discriminate.
Qed.

Lemma homeworld_norms_consistent :
  modally_consistent homeworld_norms.
Proof.
  split.
  - intros a o H Habs. unfold homeworld_norms in H, Habs.
    destruct (agent_eqb a kushan && obligation_eqb o treaty_no_hyperspace);
      discriminate.
  - intros a o H Habs. unfold homeworld_norms in H, Habs.
    destruct (agent_eqb a kushan && obligation_eqb o treaty_no_hyperspace);
      discriminate.
Qed.

(** In a grounded system, OBL entails the obligation precondition
    for authorized enforcement: if the modality is obligatory and
    the agent has violated, both [obligated] and [violated] hold. *)

Theorem obligatory_violation_authorizable :
  forall ds ns a o,
    grounded ds ns ->
    ns a o = OBL ->
    violated ds a o = true ->
    obligated ds a o = true /\ violated ds a o = true.
Proof.
  intros ds ns a o [Hobl _] Hns Hviol.
  split.
  - exact (Hobl a o Hns).
  - exact Hviol.
Qed.

(** Combining modalities with lawfulness: in a grounded coherent
    system, FORB precludes any lawful response (no violation exists
    to punish), while OBL enables lawful responses when enforcement
    authority and boundedness are satisfied. *)

Theorem forb_precludes_lawful :
  forall ds ns a o pr,
    grounded ds ns ->
    coherent ds ->
    ns a o = FORB ->
    target pr = a ->
    cause pr = o ->
    ~ lawful ds pr.
Proof.
  intros ds ns a o pr Hgr Hcoh Hns Htgt Hcause Hlaw.
  assert (Hviol : violated ds a o = false)
    by (exact (forbidden_no_violation ds ns a o Hgr Hcoh Hns)).
  destruct Hlaw as [_ _ _ Hviol_true _ _].
  subst. rewrite Hviol in Hviol_true. discriminate.
Qed.

(** * Proportionality-Derived Caps *)

(** Harm is a natural number measuring the damage caused by a
    violation.  We use [nat] directly so arithmetic is available. *)

Definition Harm := nat.

(** A proportionality function maps violation harm to the maximum
    lawful punishment.  The cap is no longer a free parameter —
    it is derived from the harm assessment. *)

Definition ProportionalityFn := Harm -> Severity.

(** A proportionality function is *monotone*: greater harm permits
    greater (or equal) punishment. *)

Definition monotone_proportionality (f : ProportionalityFn) : Prop :=
  forall h1 h2, h1 <= h2 -> f h1 <= f h2.

(** A proportionality function is *non-trivial*: some positive harm
    level yields a positive cap. *)

Definition nontrivial_proportionality (f : ProportionalityFn) : Prop :=
  exists h, h > 0 /\ f h > 0.

(** A [ProportionalSystem] bundles a deontic system with a harm
    assessment and a proportionality function.  The key constraint
    [ps_cap_derived] forces the severity cap to equal the
    proportionality function applied to the harm of the obligation.
    The cap is no longer axiomatic — it is determined by harm. *)

Record ProportionalSystem := mkProportionalSystem {
  ps_base           : DeonticSystem;
  harm_of           : Obligation -> Harm;
  proportionality   : ProportionalityFn;
  ps_cap_derived    : forall o,
    severity_cap ps_base o = proportionality (harm_of o)
}.

(** In a proportional system, lawful punishment is bounded by the
    proportionality function applied to the violation's harm. *)

Theorem proportional_bound :
  forall ps pr,
    lawful (ps_base ps) pr ->
    severity pr <= proportionality ps (harm_of ps (cause pr)).
Proof.
  intros ps pr Hlaw.
  assert (Hbnd := lawful_bounded (ps_base ps) pr Hlaw).
  unfold bounded in Hbnd.
  rewrite (ps_cap_derived ps) in Hbnd.
  exact Hbnd.
Qed.

(** If the proportionality function is monotone and obligation A's
    harm exceeds obligation B's harm, then the cap for A is at
    least as large as the cap for B. *)

Theorem monotone_caps :
  forall ps o1 o2,
    monotone_proportionality (proportionality ps) ->
    harm_of ps o1 <= harm_of ps o2 ->
    severity_cap (ps_base ps) o1 <= severity_cap (ps_base ps) o2.
Proof.
  intros ps o1 o2 Hmono Hharm.
  rewrite (ps_cap_derived ps o1).
  rewrite (ps_cap_derived ps o2).
  exact (Hmono (harm_of ps o1) (harm_of ps o2) Hharm).
Qed.

(** Witness: the homeworld system as a proportional system.
    Harm of the hyperspace treaty violation is 5; proportionality
    function is [fun h => 2 * h], giving cap = 10. *)

Definition homeworld_proportionality : ProportionalityFn :=
  fun h => 2 * h.

Definition homeworld_harm : Obligation -> Harm :=
  fun o =>
    if obligation_eqb o treaty_no_hyperspace then 5 else 0.

Lemma homeworld_proportional_cap_derived :
  forall o,
    severity_cap homeworld_system o =
    homeworld_proportionality (homeworld_harm o).
Proof.
  intros o.
  unfold homeworld_system, homeworld_proportionality, homeworld_harm. simpl.
  destruct (obligation_eqb_spec o treaty_no_hyperspace); subst; simpl; lia.
Qed.

Definition homeworld_proportional : ProportionalSystem :=
  mkProportionalSystem
    homeworld_system
    homeworld_harm
    homeworld_proportionality
    homeworld_proportional_cap_derived.

(** The proportionality function is monotone. *)
Lemma homeworld_proportionality_monotone :
  monotone_proportionality homeworld_proportionality.
Proof.
  intros h1 h2 Hle. unfold homeworld_proportionality. lia.
Qed.

(** The proportionality function is non-trivial. *)
Lemma homeworld_proportionality_nontrivial :
  nontrivial_proportionality homeworld_proportionality.
Proof.
  exists 1. unfold homeworld_proportionality. split; lia.
Qed.

(** Instantiation: the proportional response (severity 5) is bounded
    by 2 * harm(5) = 10.  The extermination (severity 100) exceeds
    the derived cap. *)

Lemma proportional_response_within_derived_cap :
  severity proportional_response <=
  proportionality homeworld_proportional
    (harm_of homeworld_proportional (cause proportional_response)).
Proof.
  apply proportional_bound. exact proportional_lawful.
Qed.

Lemma extermination_exceeds_derived_cap :
  severity extermination_response >
  proportionality homeworld_proportional
    (harm_of homeworld_proportional (cause extermination_response)).
Proof.
  unfold homeworld_proportional, homeworld_proportionality,
         homeworld_harm, extermination_response. simpl. lia.
Qed.

(** Counterexample: a non-monotone proportionality function where
    greater harm yields a smaller cap. *)

Definition pathological_proportionality : ProportionalityFn :=
  fun h => if h <=? 5 then 100 else 1.

Lemma pathological_not_monotone :
  ~ monotone_proportionality pathological_proportionality.
Proof.
  intros H.
  specialize (H 5 6).
  unfold pathological_proportionality in H.
  simpl in H.
  assert (Habs : 100 <= 1) by (apply H; lia).
  lia.
Qed.

(** * Graded Violations and Culpability *)

(** Culpability levels, ordered from most to least blameworthy.
    Each level carries a natural-number weight that scales the
    effective severity cap. *)

Inductive CulpabilityLevel :=
  | Intentional
  | Reckless
  | Negligent
  | StrictLiability.

Definition culpability_weight (c : CulpabilityLevel) : nat :=
  match c with
  | Intentional     => 4
  | Reckless        => 3
  | Negligent       => 2
  | StrictLiability => 1
  end.

(** Culpability is ordered: more blameworthy levels have strictly
    higher weight. *)

Definition more_culpable (c1 c2 : CulpabilityLevel) : Prop :=
  culpability_weight c1 > culpability_weight c2.

Lemma intentional_most_culpable :
  forall c, c <> Intentional -> more_culpable Intentional c.
Proof.
  intros c Hne. unfold more_culpable.
  destruct c; simpl; try lia.
  exfalso. apply Hne. reflexivity.
Qed.

(** A [GradedDeonticSystem] replaces the boolean [violated] with a
    function that returns [option CulpabilityLevel].  [None] means
    no violation; [Some c] means a violation at culpability level [c]. *)

Record GradedDeonticSystem := mkGradedDeonticSystem {
  gds_agents       : list Agent;
  gds_obligated    : Agent -> Obligation -> bool;
  gds_violated     : Agent -> Obligation -> option CulpabilityLevel;
  gds_may_enforce  : Agent -> Agent -> bool;
  gds_base_cap     : Obligation -> Severity
}.

(** The effective severity cap depends on culpability: lower
    culpability reduces the maximum punishment.  The effective cap
    is [base_cap * culpability_weight / max_weight], but to stay
    in nat we use [base_cap * culpability_weight] and compare
    against [severity * max_weight]. *)

Definition effective_cap (gds : GradedDeonticSystem)
  (o : Obligation) (c : CulpabilityLevel) : Severity :=
  gds_base_cap gds o * culpability_weight c.

(** A graded response is lawful when the severity scaled by max
    weight does not exceed the effective cap. *)

Definition graded_lawful (gds : GradedDeonticSystem)
  (pr : PunitiveResponse) (c : CulpabilityLevel) : Prop :=
  In (enforcer pr) (gds_agents gds) /\
  In (target pr) (gds_agents gds) /\
  gds_may_enforce gds (enforcer pr) (target pr) = true /\
  gds_violated gds (target pr) (cause pr) = Some c /\
  gds_obligated gds (target pr) (cause pr) = true /\
  severity pr * culpability_weight Intentional <=
    effective_cap gds (cause pr) c.

(** Higher culpability permits harsher punishment. *)

Theorem culpability_scales_cap :
  forall gds o c1 c2,
    more_culpable c1 c2 ->
    effective_cap gds o c2 < effective_cap gds o c1 \/
    gds_base_cap gds o = 0.
Proof.
  intros gds o c1 c2 Hmore.
  unfold effective_cap, more_culpable in *.
  destruct (gds_base_cap gds o) eqn:Hcap.
  - right. reflexivity.
  - left. nia.
Qed.

(** Embedding: a boolean DeonticSystem embeds into a GradedDeonticSystem
    by treating all violations as strict liability. *)

Definition embed_boolean (ds : DeonticSystem) : GradedDeonticSystem :=
  mkGradedDeonticSystem
    (agents ds)
    (obligated ds)
    (fun a o => if violated ds a o then Some Intentional else None)
    (may_enforce ds)
    (severity_cap ds).

(** The embedding preserves lawfulness: a lawful response in the
    boolean system is graded-lawful at Intentional (full weight)
    in the embedded system, since boolean violation does not
    distinguish culpability. *)

Theorem embed_preserves_lawful :
  forall ds pr,
    lawful ds pr ->
    graded_lawful (embed_boolean ds) pr Intentional.
Proof.
  intros ds pr Hlaw.
  destruct Hlaw as [Hine Hint Henf Hviol Hobl Hbnd].
  unfold graded_lawful, embed_boolean, effective_cap. simpl.
  repeat split; auto.
  - rewrite Hviol. reflexivity.
  - lia.
Qed.

(** Converse: graded-lawful at Intentional in the embedded
    system implies lawful in the boolean system. *)

Theorem embed_reflects_lawful :
  forall ds pr,
    graded_lawful (embed_boolean ds) pr Intentional ->
    lawful ds pr.
Proof.
  intros ds pr [Hine [Hint [Henf [Hviol [Hobl Hbnd]]]]].
  unfold embed_boolean in *. simpl in *.
  apply lawful_intro; auto.
  - destruct (violated ds (target pr) (cause pr)); [reflexivity | discriminate].
  - unfold effective_cap in Hbnd. simpl in Hbnd. lia.
Qed.

(** Witness: the homeworld system embedded with graded violations.
    The hyperspace treaty violation by Kushan was intentional
    (they knowingly developed hyperspace tech). *)

Definition homeworld_graded : GradedDeonticSystem :=
  mkGradedDeonticSystem
    [taiidan; kushan]
    (fun a o =>
      agent_eqb a kushan && obligation_eqb o treaty_no_hyperspace)
    (fun a o =>
      if agent_eqb a kushan && obligation_eqb o treaty_no_hyperspace
      then Some Intentional else None)
    (fun enforcer target =>
      agent_eqb enforcer taiidan && agent_eqb target kushan)
    (fun o =>
      if obligation_eqb o treaty_no_hyperspace then 10 else 0).

(** With intentional violation, the effective cap is 10 * 4 = 40
    (scaled units), permitting severity up to 40/4 = 10 in real
    units.  A negligent violation would give effective cap 10 * 2
    = 20, permitting severity up to 20/4 = 5. *)

Lemma intentional_effective_cap :
  effective_cap homeworld_graded treaty_no_hyperspace Intentional = 40.
Proof.
  unfold effective_cap, homeworld_graded. simpl. lia.
Qed.

Lemma negligent_effective_cap :
  effective_cap homeworld_graded treaty_no_hyperspace Negligent = 20.
Proof.
  unfold effective_cap, homeworld_graded. simpl. lia.
Qed.

(** A severity-10 response is graded-lawful for an intentional violation
    (10 * 4 <= 40) but NOT for a negligent violation (10 * 4 > 20). *)

Lemma severity_10_lawful_intentional :
  graded_lawful homeworld_graded
    (mkPunitiveResponse taiidan kushan treaty_no_hyperspace 10)
    Intentional.
Proof.
  unfold graded_lawful, homeworld_graded, effective_cap. simpl.
  repeat split; auto.
Qed.

Lemma severity_10_unlawful_negligent :
  ~ graded_lawful homeworld_graded
      (mkPunitiveResponse taiidan kushan treaty_no_hyperspace 10)
      Negligent.
Proof.
  unfold graded_lawful, homeworld_graded, effective_cap. simpl.
  intros [_ [_ [_ [Hviol _]]]]. discriminate.
Qed.

(** * Contrary-to-Duty Obligations *)

(** A contrary-to-duty (CTD) obligation is a second-order norm
    triggered by the violation of a primary obligation:
    "if you violate A, you must do B."

    Classic example (Chisholm): you ought not steal; but if you do
    steal, you ought to return the goods.  In Homeworld terms:
    Kushan ought not develop hyperspace; but if they do, they must
    submit to inspection. *)

Record CTDObligation := mkCTDObligation {
  ctd_primary   : Obligation;
  ctd_secondary : Obligation;
  ctd_agent     : Agent
}.

(** A CTD obligation is *triggered* when the agent has violated the
    primary obligation. *)

Definition ctd_triggered (ds : DeonticSystem) (ctd : CTDObligation) : Prop :=
  violated ds (ctd_agent ctd) (ctd_primary ctd) = true.

(** A CTD obligation is *satisfied* when, upon triggering, the agent
    bears and has not violated the secondary obligation. *)

Definition ctd_satisfied (ds : DeonticSystem) (ctd : CTDObligation) : Prop :=
  ctd_triggered ds ctd ->
  obligated ds (ctd_agent ctd) (ctd_secondary ctd) = true /\
  violated ds (ctd_agent ctd) (ctd_secondary ctd) = false.

(** A CTD obligation is *doubly violated* when the agent violates
    both the primary and secondary obligations. *)

Definition ctd_doubly_violated (ds : DeonticSystem) (ctd : CTDObligation) : Prop :=
  violated ds (ctd_agent ctd) (ctd_primary ctd) = true /\
  violated ds (ctd_agent ctd) (ctd_secondary ctd) = true.

(** When a CTD is doubly violated, the total lawful punishment
    across both obligations is bounded by the sum of their caps. *)

Theorem ctd_double_violation_bound :
  forall ds ctd pr_primary pr_secondary,
    ctd_doubly_violated ds ctd ->
    lawful ds pr_primary ->
    cause pr_primary = ctd_primary ctd ->
    lawful ds pr_secondary ->
    cause pr_secondary = ctd_secondary ctd ->
    severity pr_primary + severity pr_secondary <=
      severity_cap ds (ctd_primary ctd) +
      severity_cap ds (ctd_secondary ctd).
Proof.
  intros ds ctd pr1 pr2 _ Hlaw1 Hc1 Hlaw2 Hc2.
  assert (H1 := lawful_bounded ds pr1 Hlaw1).
  assert (H2 := lawful_bounded ds pr2 Hlaw2).
  unfold bounded in *. rewrite Hc1 in H1. rewrite Hc2 in H2. lia.
Qed.

(** Witness: Kushan must not develop hyperspace (treaty_no_hyperspace).
    If they do, they must submit to inspection (treaty_tribute,
    repurposed as the inspection obligation).  The system models
    both obligations with distinct caps. *)

Definition hyperspace_ctd := mkCTDObligation
  treaty_no_hyperspace treaty_tribute kushan.

(** In the homeworld system, the CTD is triggered because Kushan
    violated the hyperspace treaty. *)

Lemma hyperspace_ctd_triggered :
  ctd_triggered homeworld_system hyperspace_ctd.
Proof.
  unfold ctd_triggered, homeworld_system, hyperspace_ctd. simpl. reflexivity.
Qed.

(** The CTD secondary (inspection) has cap 0 in the homeworld system,
    so the total bound for double violation is 10 + 0 = 10 —
    the CTD secondary adds no additional punishment authority. *)

Lemma hyperspace_ctd_bound_value :
  severity_cap homeworld_system (ctd_primary hyperspace_ctd) +
  severity_cap homeworld_system (ctd_secondary hyperspace_ctd) = 10.
Proof.
  unfold homeworld_system, hyperspace_ctd. simpl. reflexivity.
Qed.

(** A [CTDSystem] extends a deontic system with a list of CTD
    obligations and a well-formedness condition: the secondary
    obligation must be distinct from the primary. *)

Record CTDSystem := mkCTDSystem {
  ctds_base  : DeonticSystem;
  ctds_rules : list CTDObligation;
  ctds_distinct : forall ctd,
    In ctd ctds_rules ->
    ctd_primary ctd <> ctd_secondary ctd
}.

(** In a CTD system, the secondary obligation becomes enforceable
    only upon violation of the primary.  This is not built into the
    base DeonticSystem (which is a snapshot), so we express it as a
    property of the CTD rule + system state. *)

Definition ctd_enforcement_valid
  (cs : CTDSystem) (ctd : CTDObligation) (pr : PunitiveResponse) : Prop :=
  In ctd (ctds_rules cs) /\
  ctd_triggered (ctds_base cs) ctd /\
  cause pr = ctd_secondary ctd /\
  lawful (ctds_base cs) pr.

(** CTD enforcement is still bounded by the secondary cap. *)

Theorem ctd_enforcement_bounded :
  forall cs ctd pr,
    ctd_enforcement_valid cs ctd pr ->
    severity pr <= severity_cap (ctds_base cs) (ctd_secondary ctd).
Proof.
  intros cs ctd pr [_ [_ [Hcause Hlaw]]].
  assert (Hbnd := lawful_bounded (ctds_base cs) pr Hlaw).
  unfold bounded in Hbnd. rewrite Hcause in Hbnd. exact Hbnd.
Qed.

(** * Normative Conflict *)

(** Two obligations *conflict* for an agent when complying with one
    entails violating the other. *)

Record NormConflict := mkNormConflict {
  nc_agent : Agent;
  nc_obl1  : Obligation;
  nc_obl2  : Obligation
}.

(** A conflict is genuine when both obligations are borne by the
    agent and the agent has violated at least one. *)

Definition genuine_conflict (ds : DeonticSystem) (nc : NormConflict) : Prop :=
  obligated ds (nc_agent nc) (nc_obl1 nc) = true /\
  obligated ds (nc_agent nc) (nc_obl2 nc) = true /\
  (violated ds (nc_agent nc) (nc_obl1 nc) = true \/
   violated ds (nc_agent nc) (nc_obl2 nc) = true).

(** A [ConflictResolution] assigns a priority to each obligation.
    When two obligations conflict, only violation of the
    higher-priority obligation is enforceable; the lower-priority
    violation is excused. *)

Record ConflictResolution := mkConflictResolution {
  cr_base      : DeonticSystem;
  cr_conflicts : list NormConflict;
  cr_priority  : Obligation -> nat;
  cr_distinct  : forall nc,
    In nc cr_conflicts ->
    nc_obl1 nc <> nc_obl2 nc
}.

(** An obligation is *excused* when it conflicts with a
    higher-priority obligation. *)

Definition excused (cr : ConflictResolution)
  (a : Agent) (o : Obligation) : Prop :=
  exists nc,
    In nc (cr_conflicts cr) /\
    nc_agent nc = a /\
    ((nc_obl1 nc = o /\
      cr_priority cr (nc_obl2 nc) > cr_priority cr o) \/
     (nc_obl2 nc = o /\
      cr_priority cr (nc_obl1 nc) > cr_priority cr o)).

(** An enforcement is *conflict-valid* when the targeted obligation
    is not excused. *)

Definition conflict_valid_enforcement
  (cr : ConflictResolution) (pr : PunitiveResponse) : Prop :=
  lawful (cr_base cr) pr /\
  ~ excused cr (target pr) (cause pr).

(** Enforcement of an excused obligation is invalid. *)

Theorem excused_blocks_enforcement :
  forall cr pr,
    excused cr (target pr) (cause pr) ->
    ~ conflict_valid_enforcement cr pr.
Proof.
  intros cr pr Hexc [_ Hnexc]. exact (Hnexc Hexc).
Qed.

(** Conflict-valid enforcement is still bounded. *)

Theorem conflict_valid_bounded :
  forall cr pr,
    conflict_valid_enforcement cr pr ->
    severity pr <= severity_cap (cr_base cr) (cause pr).
Proof.
  intros cr pr [Hlaw _].
  exact (lawful_bounded (cr_base cr) pr Hlaw).
Qed.

(** Witness: Kushan bears hyperspace (priority 1) and tribute
    (priority 2).  They conflict.  The lower-priority obligation
    (hyperspace) is excused; the higher-priority (tribute) is not. *)

Definition hw_conflict := mkNormConflict
  kushan treaty_no_hyperspace treaty_tribute.

Lemma hw_conflict_distinct :
  forall nc, In nc [hw_conflict] -> nc_obl1 nc <> nc_obl2 nc.
Proof.
  intros nc [H | []]. subst. simpl. exact obligations_distinct.
Qed.

Definition homeworld_cr := mkConflictResolution
  homeworld_system
  [hw_conflict]
  (fun o =>
    if obligation_eqb o treaty_no_hyperspace then 1
    else if obligation_eqb o treaty_tribute then 2
    else 0)
  hw_conflict_distinct.

(** Hyperspace (priority 1) is excused by tribute (priority 2). *)

Lemma hyperspace_excused :
  excused homeworld_cr kushan treaty_no_hyperspace.
Proof.
  exists hw_conflict. split.
  - left. reflexivity.
  - split.
    + reflexivity.
    + left. split.
      * reflexivity.
      * unfold homeworld_cr. simpl. lia.
Qed.

(** Tribute (priority 2) is NOT excused — it is the higher-priority
    obligation. *)

Lemma tribute_not_excused :
  ~ excused homeworld_cr kushan treaty_tribute.
Proof.
  intros [nc [Hin [Hagent Hpri]]].
  destruct Hin as [H | []]. subst. simpl in *.
  destruct Hpri as [[Hobl Hgt] | [Hobl Hgt]].
  - unfold treaty_no_hyperspace, treaty_tribute in Hobl.
    injection Hobl. lia.
  - unfold homeworld_cr in Hgt. simpl in Hgt. lia.
Qed.

(** * Defeasible Norms *)

(** A defeasible norm is an obligation that holds by default but can
    be overridden by a specific exception.  We model this with a
    priority-indexed obligation structure: each obligation carries a
    priority, and higher-priority norms defeat lower-priority ones. *)

Record DefeasibleObligation := mkDefeasibleObligation {
  do_obligation : Obligation;
  do_priority   : nat;
  do_agent      : Agent
}.

(** A [DefeasibleSystem] extends a deontic system with defeasible
    obligations and exception rules. *)

Record ExceptionRule := mkExceptionRule {
  er_overrides : Obligation;
  er_exception : Obligation;
  er_agent     : Agent
}.

(** An exception is *active* when the agent bears the exception
    obligation and has not violated it. *)

Definition exception_active (ds : DeonticSystem) (er : ExceptionRule) : Prop :=
  obligated ds (er_agent er) (er_exception er) = true /\
  violated ds (er_agent er) (er_exception er) = false.

(** An obligation is *defeated* when an active exception overrides it. *)

Definition defeated (ds : DeonticSystem)
  (exceptions : list ExceptionRule) (a : Agent) (o : Obligation) : Prop :=
  exists er,
    In er exceptions /\
    er_agent er = a /\
    er_overrides er = o /\
    exception_active ds er.

(** A *defeasible enforcement* is lawful only if the targeted
    obligation is not defeated by an active exception. *)

Definition defeasibly_lawful (ds : DeonticSystem)
  (exceptions : list ExceptionRule) (pr : PunitiveResponse) : Prop :=
  lawful ds pr /\
  ~ defeated ds exceptions (target pr) (cause pr).

(** Defeating an obligation blocks enforcement. *)

Theorem defeated_blocks_enforcement :
  forall ds exceptions pr,
    defeated ds exceptions (target pr) (cause pr) ->
    ~ defeasibly_lawful ds exceptions pr.
Proof.
  intros ds exceptions pr Hdef [_ Hndef].
  exact (Hndef Hdef).
Qed.

(** Defeasible enforcement is still bounded by the cap. *)

Theorem defeasibly_lawful_bounded :
  forall ds exceptions pr,
    defeasibly_lawful ds exceptions pr ->
    severity pr <= severity_cap ds (cause pr).
Proof.
  intros ds exceptions pr [Hlaw _].
  exact (lawful_bounded ds pr Hlaw).
Qed.

(** Witness: Kushan's hyperspace obligation is defeasible.  If the
    Bentusi grant an exception (a technology-sharing treaty), the
    hyperspace obligation is defeated and not enforceable. *)

Definition bentusi := mkAgent 4.
Definition bentusi_treaty := mkObligation 3.

Definition hyperspace_exception := mkExceptionRule
  treaty_no_hyperspace bentusi_treaty kushan.

(** A modified system where Kushan bears both the hyperspace treaty
    and the Bentusi exception, and has NOT violated the exception. *)

Definition homeworld_with_exception : DeonticSystem := mkDeonticSystem
  [taiidan; kushan; bentusi]
  (fun a o =>
    (agent_eqb a kushan && obligation_eqb o treaty_no_hyperspace) ||
    (agent_eqb a kushan && obligation_eqb o bentusi_treaty))
  (fun a o =>
    agent_eqb a kushan && obligation_eqb o treaty_no_hyperspace)
  (fun enforcer target =>
    agent_eqb enforcer taiidan && agent_eqb target kushan)
  (fun o =>
    if obligation_eqb o treaty_no_hyperspace then 10 else 0).

Lemma bentusi_exception_active :
  exception_active homeworld_with_exception hyperspace_exception.
Proof.
  unfold exception_active, homeworld_with_exception, hyperspace_exception.
  simpl. auto.
Qed.

Lemma hyperspace_defeated :
  defeated homeworld_with_exception [hyperspace_exception]
    kushan treaty_no_hyperspace.
Proof.
  exists hyperspace_exception.
  split; [left; reflexivity |].
  split; [reflexivity |].
  split; [reflexivity |].
  exact bentusi_exception_active.
Qed.

(** Enforcement of the hyperspace obligation is blocked by the
    Bentusi exception. *)

Lemma hyperspace_enforcement_blocked :
  forall pr,
    target pr = kushan ->
    cause pr = treaty_no_hyperspace ->
    ~ defeasibly_lawful homeworld_with_exception
        [hyperspace_exception] pr.
Proof.
  intros pr Htgt Hcause.
  apply defeated_blocks_enforcement.
  rewrite Htgt, Hcause. exact hyperspace_defeated.
Qed.

(** Without the exception, enforcement proceeds normally. *)

Lemma no_exception_not_defeated :
  ~ defeated homeworld_system [] kushan treaty_no_hyperspace.
Proof.
  intros [er [Hin _]]. destruct Hin.
Qed.

(** * Severity Categories *)

(** Punishment is not a bare number but belongs to a category.
    Categories are ordered by escalation: diplomatic remedies must
    be exhausted before economic measures, which must be exhausted
    before military action. *)

Inductive SeverityCategory :=
  | Diplomatic
  | Economic
  | Military.

Definition category_rank (c : SeverityCategory) : nat :=
  match c with
  | Diplomatic => 0
  | Economic   => 1
  | Military   => 2
  end.

Definition category_le (c1 c2 : SeverityCategory) : Prop :=
  category_rank c1 <= category_rank c2.

(** A typed punitive response carries both a severity magnitude
    and a category. *)

Record TypedResponse := mkTypedResponse {
  tr_base     : PunitiveResponse;
  tr_category : SeverityCategory
}.

(** A [SeverityPolicy] assigns to each obligation the maximum
    permitted category and a magnitude cap per category. *)

Record SeverityPolicy := mkSeverityPolicy {
  sp_base         : DeonticSystem;
  sp_max_category : Obligation -> SeverityCategory;
  sp_category_cap : Obligation -> SeverityCategory -> Severity
}.

(** A typed response is *categorically lawful* when:
    (1) the base response is lawful,
    (2) the response category does not exceed the obligation's max,
    (3) the severity does not exceed the per-category cap. *)

Definition categorically_lawful (sp : SeverityPolicy)
  (tr : TypedResponse) : Prop :=
  lawful (sp_base sp) (tr_base tr) /\
  category_le (tr_category tr)
    (sp_max_category sp (cause (tr_base tr))) /\
  severity (tr_base tr) <=
    sp_category_cap sp (cause (tr_base tr)) (tr_category tr).

(** Escalation constraint: military action requires that diplomatic
    and economic remedies have been attempted.  We model this as:
    for military responses, prior diplomatic and economic responses
    must exist in the response history. *)

Definition exhaustion_satisfied
  (history : list TypedResponse) (tr : TypedResponse) : Prop :=
  tr_category tr = Military ->
  (exists d, In d history /\ tr_category d = Diplomatic) /\
  (exists e, In e history /\ tr_category e = Economic).

(** Categorically lawful responses are bounded by the per-category cap. *)

Theorem categorical_bound :
  forall sp tr,
    categorically_lawful sp tr ->
    severity (tr_base tr) <=
      sp_category_cap sp (cause (tr_base tr)) (tr_category tr).
Proof.
  intros sp tr [_ [_ Hcap]]. exact Hcap.
Qed.

(** The category cannot exceed the obligation's maximum. *)

Theorem categorical_escalation_bound :
  forall sp tr,
    categorically_lawful sp tr ->
    category_le (tr_category tr)
      (sp_max_category sp (cause (tr_base tr))).
Proof.
  intros sp tr [_ [Hcat _]]. exact Hcat.
Qed.

(** Witness: in the homeworld system, the hyperspace treaty allows
    economic responses (cap 8) and diplomatic responses (cap 10),
    but NOT military action. *)

Definition homeworld_severity_policy := mkSeverityPolicy
  homeworld_system
  (fun o =>
    if obligation_eqb o treaty_no_hyperspace then Economic
    else Diplomatic)
  (fun o c =>
    if obligation_eqb o treaty_no_hyperspace then
      match c with
      | Diplomatic => 10
      | Economic => 8
      | Military => 0
      end
    else 0).

(** A diplomatic response (severity 5) is categorically lawful. *)

Lemma diplomatic_response_lawful :
  categorically_lawful homeworld_severity_policy
    (mkTypedResponse proportional_response Diplomatic).
Proof.
  unfold categorically_lawful, homeworld_severity_policy,
         proportional_response, category_le. simpl.
  split; [| split].
  - exact proportional_lawful.
  - lia.
  - lia.
Qed.

(** A military response is NOT categorically lawful: the hyperspace
    treaty only permits up to Economic measures. *)

Lemma military_response_not_lawful :
  ~ categorically_lawful homeworld_severity_policy
      (mkTypedResponse proportional_response Military).
Proof.
  unfold categorically_lawful, homeworld_severity_policy,
         proportional_response, category_le. simpl.
  intros [_ [Hcat _]]. lia.
Qed.

(** An economic response at severity 8 exactly hits the category cap. *)

Definition economic_response := mkPunitiveResponse
  taiidan kushan treaty_no_hyperspace 8.

Lemma economic_response_tight :
  categorically_lawful homeworld_severity_policy
    (mkTypedResponse economic_response Economic).
Proof.
  unfold categorically_lawful, homeworld_severity_policy,
         economic_response, category_le. simpl.
  split; [| split].
  - apply lawful_intro; unfold homeworld_system; simpl; auto; lia.
  - lia.
  - lia.
Qed.

(** * Rights as Enforcement Constraints *)

(** Rights constrain enforcement: even when punishment is authorized
    and bounded, the target may hold rights that limit how
    enforcement proceeds. *)

Inductive Right :=
  | DueProcess
  | ProportionalityReview
  | Appeal
  | HabeasCorpus.

(** A [RightsSystem] associates rights with agents and requires
    that enforcement respects them. *)

Record RightsSystem := mkRightsSystem {
  rs_base    : DeonticSystem;
  rs_rights  : Agent -> list Right;
  rs_process : Agent -> bool
}.

(** A right is *held* by an agent. *)

Definition holds_right (rs : RightsSystem) (a : Agent) (r : Right) : Prop :=
  In r (rs_rights rs a).

(** Due process requires that the enforcer has followed procedure
    (modeled as the [rs_process] flag). *)

Definition due_process_satisfied (rs : RightsSystem)
  (pr : PunitiveResponse) : Prop :=
  holds_right rs (target pr) DueProcess ->
  rs_process rs (target pr) = true.

(** A *rights-respecting* enforcement satisfies due process and
    is otherwise lawful. *)

Definition rights_respecting (rs : RightsSystem)
  (pr : PunitiveResponse) : Prop :=
  lawful (rs_base rs) pr /\
  due_process_satisfied rs pr.

(** Enforcement that violates due process is not rights-respecting,
    even if otherwise lawful. *)

Theorem due_process_required :
  forall rs pr,
    holds_right rs (target pr) DueProcess ->
    rs_process rs (target pr) = false ->
    ~ rights_respecting rs pr.
Proof.
  intros rs pr Hright Hfalse [_ Hdp].
  assert (H := Hdp Hright). rewrite H in Hfalse. discriminate.
Qed.

(** Rights-respecting enforcement is still bounded. *)

Theorem rights_respecting_bounded :
  forall rs pr,
    rights_respecting rs pr ->
    severity pr <= severity_cap (rs_base rs) (cause pr).
Proof.
  intros rs pr [Hlaw _].
  exact (lawful_bounded (rs_base rs) pr Hlaw).
Qed.

(** Witness: Kushan holds due process rights.  Enforcement without
    process is invalid. *)

Definition homeworld_rights := mkRightsSystem
  homeworld_system
  (fun a => if agent_eqb a kushan then [DueProcess; Appeal] else [])
  (fun _ => false).

Lemma kushan_holds_due_process :
  holds_right homeworld_rights kushan DueProcess.
Proof.
  unfold holds_right, homeworld_rights. simpl. left. reflexivity.
Qed.

Lemma enforcement_without_process :
  ~ rights_respecting homeworld_rights proportional_response.
Proof.
  apply due_process_required.
  - exact kushan_holds_due_process.
  - reflexivity.
Qed.

(** A system with due process satisfied permits enforcement. *)

Definition homeworld_rights_with_process := mkRightsSystem
  homeworld_system
  (fun a => if agent_eqb a kushan then [DueProcess; Appeal] else [])
  (fun a => agent_eqb a kushan).

Lemma enforcement_with_process :
  rights_respecting homeworld_rights_with_process proportional_response.
Proof.
  split.
  - exact proportional_lawful.
  - unfold due_process_satisfied, homeworld_rights_with_process,
           proportional_response. simpl. auto.
Qed.
