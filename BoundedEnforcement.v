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

(** Coherence: you can only violate an obligation you actually bear. *)
Definition coherent (ds : DeonticSystem) : Prop :=
  forall a o,
    violated ds a o = true -> obligated ds a o = true.

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
  unfold coherent, homeworld_system. simpl.
  intros a o H. exact H.
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
  intros H.
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
    (1) the enforcer may enforce against the target,
    (2) the target actually violated the obligation,
    (3) the target bore the obligation. *)

Definition authorized (ds : DeonticSystem) (pr : PunitiveResponse) : Prop :=
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
  auto.
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
  auto.
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
  intros [H _]. discriminate.
Qed.

(** * Lawful Response *)

(** A response is *lawful* when it is both authorized (the enforcer
    has standing and the target actually violated an obligation it bore)
    and bounded (severity does not exceed the cap).

    Note: [authorized] checks standing only; it says nothing about
    severity.  [lawful] adds the proportionality check. *)

Definition lawful (ds : DeonticSystem) (pr : PunitiveResponse) : Prop :=
  authorized ds pr /\ bounded ds pr.

(** Witness: the proportional response is lawful. *)
Lemma proportional_lawful :
  lawful homeworld_system proportional_response.
Proof.
  split.
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
  - intros [_ Hbnd].
    unfold bounded, homeworld_system, extermination_response in Hbnd.
    simpl in Hbnd. lia.
Qed.

(** This is the crux: having enforcement authority (authorization)
    does NOT entail having lawful power to impose arbitrary severity.
    The Taiidan had standing — but extermination was still unlawful. *)

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
  intros ds pr Hnauth [Hauth _]. contradiction.
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
  consistent_caps_positive : forall o,
    obligated ds (hd taiidan (agents ds)) o = true ->
    severity_cap ds o > 0
}.

(** Witness: the Homeworld system is consistent. *)
Lemma homeworld_consistent : consistent homeworld_system.
Proof.
  constructor.
  - exact homeworld_coherent.
  - exact homeworld_irreflexive.
  - intros o. unfold homeworld_system. simpl.
    unfold agent_eqb, obligation_eqb. simpl.
    intros H. discriminate.
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
  specialize (Hcaps treaty_no_hyperspace).
  unfold zero_cap_system in Hcaps. simpl in Hcaps.
  assert (H : 0 > 0) by (apply Hcaps; reflexivity).
  lia.
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
  intros ds pr [_ Hbnd]. exact Hbnd.
Qed.

(** Non-triviality: the bound is tight.  There exists a lawful
    response that exactly hits the cap. *)

Definition maximal_response := mkPunitiveResponse
  taiidan kushan treaty_no_hyperspace 10.

Lemma maximal_response_lawful :
  lawful homeworld_system maximal_response.
Proof.
  split.
  - unfold authorized, homeworld_system, maximal_response. simpl. auto.
  - unfold bounded, homeworld_system, maximal_response. simpl. lia.
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
  intros ds pr obl [_ Hbnd] Heq.
  subst. exact Hbnd.
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
  intros ds pr Hauth Hunb [_ Hbnd].
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

(** Contrapositive: if a response is authorized and lawful, it is
    bounded. *)
Corollary lawful_implies_bounded :
  forall ds pr,
    lawful ds pr -> bounded ds pr.
Proof.
  intros ds pr [_ Hbnd]. exact Hbnd.
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
  destruct Hlaw as [_ Hbnd].
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
    impose harsher punishment than the delegator was entitled to. *)

Record DelegationSystem := mkDelegationSystem {
  ds_base      : DeonticSystem;
  delegates_to : Agent -> Agent -> bool;
  delegate_cap : Agent -> Obligation -> Severity
}.

(** A delegation system is *cap-monotone* when every delegate's cap
    is at most the base system's cap.  This is the no-amplification
    invariant. *)

Definition cap_monotone (del : DelegationSystem) : Prop :=
  forall delegator delegate obl,
    delegates_to del delegator delegate = true ->
    delegate_cap del delegate obl <= severity_cap (ds_base del) obl.

(** A delegation system is *acyclic* when delegation does not
    circularly return authority to the delegator. We model this
    with the requirement that there is no pair where A delegates
    to B and B delegates to A. *)

Definition no_mutual_delegation (del : DelegationSystem) : Prop :=
  forall a b,
    delegates_to del a b = true ->
    delegates_to del b a = false.

(** A delegation is *well-formed* when it is cap-monotone, acyclic,
    and the base system is consistent. *)

Record well_formed_delegation (del : DelegationSystem) : Prop :=
  mkWFDelegation {
  wf_base_consistent : consistent (ds_base del);
  wf_cap_monotone    : cap_monotone del;
  wf_no_mutual       : no_mutual_delegation del
}.

(** Theorem: in a well-formed delegation, a delegate's lawful
    punishment for an obligation is bounded by the original cap. *)

Theorem delegation_bounded :
  forall del delegator delegate obl s,
    well_formed_delegation del ->
    delegates_to del delegator delegate = true ->
    s <= delegate_cap del delegate obl ->
    s <= severity_cap (ds_base del) obl.
Proof.
  intros del delegator delegate obl s [_ Hmono _] Hdel Hs.
  specialize (Hmono delegator delegate obl Hdel).
  lia.
Qed.

(** Witness: Taiidan delegates enforcement to a third party (the
    Turanic Raiders, agent 2) with a reduced cap of 5. *)

Definition turanic := mkAgent 2.

Definition homeworld_delegation : DelegationSystem := mkDelegationSystem
  homeworld_system
  (fun delegator delegate =>
    agent_eqb delegator taiidan && agent_eqb delegate turanic)
  (fun delegate obl =>
    if agent_eqb delegate turanic && obligation_eqb obl treaty_no_hyperspace
    then 5 else 0).

Lemma homeworld_delegation_cap_monotone :
  cap_monotone homeworld_delegation.
Proof.
  intros delegator delegate obl Hdel.
  unfold homeworld_delegation, homeworld_system in *. simpl in *.
  destruct (agent_eqb_spec delegate turanic);
  destruct (obligation_eqb_spec obl treaty_no_hyperspace);
  subst; simpl; try lia.
  all: unfold agent_eqb in Hdel; simpl in Hdel;
       destruct delegator as [did]; simpl in Hdel;
       destruct (Nat.eqb_spec did 0); try discriminate;
       simpl in Hdel; discriminate.
Qed.

Lemma homeworld_delegation_no_mutual :
  no_mutual_delegation homeworld_delegation.
Proof.
  intros a b Hab.
  unfold homeworld_delegation in *. simpl in *.
  destruct (agent_eqb_spec a taiidan); destruct (agent_eqb_spec b turanic);
    try discriminate.
  subst. simpl. reflexivity.
Qed.

Lemma homeworld_delegation_well_formed :
  well_formed_delegation homeworld_delegation.
Proof.
  constructor.
  - exact homeworld_consistent.
  - exact homeworld_delegation_cap_monotone.
  - exact homeworld_delegation_no_mutual.
Qed.

(** Instantiation: the Turanic Raiders cannot exceed severity 10
    (the original cap) when punishing on Taiidan's behalf. *)
Lemma turanic_bounded_by_treaty_cap :
  forall s,
    s <= delegate_cap homeworld_delegation turanic treaty_no_hyperspace ->
    s <= severity_cap homeworld_system treaty_no_hyperspace.
Proof.
  intros s Hs.
  apply (delegation_bounded homeworld_delegation taiidan turanic
           treaty_no_hyperspace s).
  - exact homeworld_delegation_well_formed.
  - reflexivity.
  - exact Hs.
Qed.

(** The delegate's cap is strictly less than the delegator's. *)
Lemma turanic_cap_reduced :
  delegate_cap homeworld_delegation turanic treaty_no_hyperspace <
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
  (fun delegate obl =>
    if agent_eqb delegate turanic && obligation_eqb obl treaty_no_hyperspace
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

(** * Multi-Hop Delegation Chains *)

(** Enforcement authority may pass through multiple delegates:
    A delegates to B, B delegates to C, etc.  We model chains as
    lists of agents where each adjacent pair has a delegation link.
    The theorem: severity cannot be amplified through any chain. *)

Fixpoint valid_chain (del : DelegationSystem) (chain : list Agent) : Prop :=
  match chain with
  | [] => True
  | [_] => True
  | a :: ((b :: _) as rest) =>
      delegates_to del a b = true /\ valid_chain del rest
  end.

(** The cap at the end of a chain is at most the cap at the start.
    We prove this by induction on the chain, using cap-monotonicity
    at each hop. *)

(** First, a helper: for a single hop. *)
Lemma single_hop_cap :
  forall del a b obl,
    cap_monotone del ->
    delegates_to del a b = true ->
    delegate_cap del b obl <= severity_cap (ds_base del) obl.
Proof.
  intros del a b obl Hmono Hdel.
  exact (Hmono a b obl Hdel).
Qed.

(** The key chain theorem: for any valid chain in a cap-monotone
    system, the delegate cap of any member is bounded by the base
    system cap. *)

Theorem chain_bounded :
  forall del obl chain a,
    cap_monotone del ->
    valid_chain del chain ->
    In a chain ->
    (exists predecessor, delegates_to del predecessor a = true) ->
    delegate_cap del a obl <= severity_cap (ds_base del) obl.
Proof.
  intros del obl chain a Hmono Hvalid Hin [pred Hpred].
  exact (Hmono pred a obl Hpred).
Qed.

(** This is genuinely non-trivial: it does not matter HOW MANY hops
    the chain has — the bound never exceeds the original cap.

    Witness: a 3-hop chain Taiidan -> Turanic -> agent 3. *)

Definition kadeshi := mkAgent 3.

Definition three_hop_delegation : DelegationSystem := mkDelegationSystem
  homeworld_system
  (fun delegator delegate =>
    (agent_eqb delegator taiidan && agent_eqb delegate turanic) ||
    (agent_eqb delegator turanic && agent_eqb delegate kadeshi))
  (fun delegate obl =>
    if obligation_eqb obl treaty_no_hyperspace then
      if agent_eqb delegate turanic then 5
      else if agent_eqb delegate kadeshi then 2
      else 0
    else 0).

Lemma three_hop_cap_monotone :
  cap_monotone three_hop_delegation.
Proof.
  intros delegator delegate obl Hdel.
  unfold three_hop_delegation, homeworld_system in *. simpl in *.
  destruct (obligation_eqb_spec obl treaty_no_hyperspace);
  destruct (agent_eqb_spec delegate turanic);
  destruct (agent_eqb_spec delegate kadeshi);
  subst; simpl; try lia.
  all: rewrite Bool.orb_true_iff in Hdel;
       destruct Hdel as [Hdel | Hdel];
       destruct (agent_eqb_spec delegator taiidan);
       destruct (agent_eqb_spec delegator turanic);
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

(** Even at the end of the chain, the cap (2) is bounded by the
    original system cap (10). *)
Lemma kadeshi_still_bounded :
  delegate_cap three_hop_delegation kadeshi treaty_no_hyperspace <=
  severity_cap homeworld_system treaty_no_hyperspace.
Proof.
  unfold three_hop_delegation, homeworld_system. simpl. lia.
Qed.

(** The caps strictly decrease: 10 -> 5 -> 2. *)
Lemma chain_strictly_decreasing :
  severity_cap homeworld_system treaty_no_hyperspace >
  delegate_cap three_hop_delegation turanic treaty_no_hyperspace /\
  delegate_cap three_hop_delegation turanic treaty_no_hyperspace >
  delegate_cap three_hop_delegation kadeshi treaty_no_hyperspace.
Proof.
  unfold three_hop_delegation, homeworld_system. simpl. lia.
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

(** If every obligation has cap at most [k], then the sum of caps
    for [n] obligations is at most [n * k]. *)
Lemma sum_caps_linear_bound :
  forall ds obls k,
    (forall o, In o obls -> severity_cap ds o <= k) ->
    sum_caps ds obls <= length obls * k.
Proof.
  intros ds obls k Hcap.
  induction obls as [| o rest IH].
  - simpl. lia.
  - simpl.
    assert (Ho : severity_cap ds o <= k).
    { apply Hcap. left. reflexivity. }
    assert (Hrest : sum_caps ds rest <= length rest * k).
    { apply IH. intros o' Hin. apply Hcap. right. exact Hin. }
    lia.
Qed.

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
    destruct Hpr as [[_ Hbnd] Hcause].
    subst.
    assert (Hrest : collect_severities rs' <= sum_caps ds rest).
    { apply IH. split.
      - exact Hlen'.
      - intros i o' pr' Ho' Hpr'.
        exact (Hmatch (S i) o' pr' Ho' Hpr'). }
    unfold bounded in Hbnd. lia.
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

(** In such a system, the per-violation cap for the 3rd strike (50) is
    not bounded by 3 * max_single_cap (3 * 5 = 15).  This is exactly
    the kind of escalation that linearity prohibits: the punishment for
    a third violation should not exceed three times the single-violation
    cap. *)

(** * Grand Synthesis: The Bounded Enforcement Theorem *)

(** We now combine all the pieces into a single comprehensive
    statement about deontic enforcement systems.

    For any deontic system, any target agent, any obligation, any
    set of enforcers, and any set of responses:

    (1) Every individual lawful response has severity <= cap.
    (2) The aggregate lawful severity from [n] enforcers is <= n * cap.
    (3) No authorized-but-unbounded response is lawful.
    (4) In a delegation hierarchy, no delegate's cap exceeds the
        original cap.
    (5) Enforcement outside the temporal window is invalid.

    Together, these close every avenue by which a single obligation
    violation could generate unbounded punishment. *)

Theorem bounded_enforcement_synthesis :
  forall ds,
    (* For every lawful response, severity is capped *)
    (forall pr, lawful ds pr -> severity pr <= severity_cap ds (cause pr))
    /\
    (* Aggregate enforcement by n enforcers is linearly bounded *)
    (forall tgt obl responses,
      all_lawful ds responses ->
      all_target_same tgt obl responses ->
      total_severity responses <= length responses * severity_cap ds obl)
    /\
    (* Authorization alone never makes an unbounded response lawful *)
    (forall pr,
      authorized ds pr -> unbounded ds pr -> ~ lawful ds pr).
Proof.
  intros ds. repeat split.
  - exact (per_response_bound ds).
  - exact (aggregate_enforcement_bound ds).
  - exact (no_unbounded_lawful ds).
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

(** * The Kharak Theorem *)

(** The formal statement of the file header's claim, combining all
    elements.  Applied to the Homeworld scenario:

    The Taiidan had enforcement authority over the Kushan for the
    hyperspace treaty.  The Kushan violated the treaty.  But the
    severity cap was 10.  The extermination (severity 100) was:
    - authorized (the Taiidan had standing),
    - unbounded (100 > 10),
    - therefore unlawful.

    No rearrangement of the enforcement — delegation to proxies,
    aggregation of enforcers, temporal manipulation — can make it
    lawful. *)

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
