# BoundedEnforcement.v — Cure List

Ordered by logical dependency. Later phases depend on earlier ones.

## Phase 1: Remove dead code and redundancy

- [x] **1.1** Delete `lawful_implies_bounded` — identical to `per_response_bound`. *(was #3)*
- [x] **1.2** Delete `sum_caps_linear_bound` or wire it into a theorem. Currently proved and never applied. *(was #36)*
- [x] **1.3** Make `agents` field load-bearing: `authorized` now requires `In` membership from `DeonticSystem`, or make at least one predicate/theorem reference it. No definition or proof ever inspects agent membership. *(was #30, #31)*

## Phase 2: Fix foundational definitions

- [x] **2.1** Rewrite `consistent_caps_positive` to quantify over all agents: `forall a o, In a (agents ds) -> obligated ds a o = true -> severity_cap ds o > 0`. The current formulation checks only `hd taiidan (agents ds)`, which is one arbitrary agent. *(was #7)*
- [x] **2.2** After fixing 2.1, re-prove `homeworld_consistent` non-vacuously. The current proof is vacuously true because `obligated homeworld_system taiidan _ = false` for all obligations, so the premise of `consistent_caps_positive` is never satisfied. *(was #22, #23)*
- [x] **2.3** Strengthen `authorized` to require `In (enforcer pr) (agents ds)` and `In (target pr) (agents ds)`. Currently an agent outside the population can have `may_enforce` return true. *(was #30)*
- [x] **2.4** Strengthen `coherent` to also require: obligations with nonzero caps have at least one bearer, and `may_enforce` only holds between agents in the population. *(was #18)*

## Phase 3: Make `consistent` load-bearing

- [x] **3.1** Add `consistent_authorized_positive_cap` theorem using `consistent` as hypothesis to `no_unbounded_lawful`, `aggregate_enforcement_bound`, or another central theorem where it actually constrains the result. Currently defined and witnessed but never required anywhere. *(was #6)*

## Phase 4: Fix the delegation model

- [x] **4.1** Make `delegate_cap` depend on the delegation pair: change signature to `Agent -> Agent -> Obligation -> Severity` so distinct delegators can grant different caps to the same delegate. *(was #26)*
- [x] **4.2** Replace `no_mutual_delegation` with inductive `reachable` + `acyclic` with proper acyclicity of the delegation graph. The current check blocks A<->B but permits A->B->C->A. Define reachability and require irreflexivity of the transitive closure. *(was #25)*
- [x] **4.3** Redefine `cap_monotone` + add `chain_cap` with `Nat.min` at each hop to be relative: `delegate_cap del delegator delegate obl <= delegate_cap del origin delegator obl` (or the base cap when the delegator is the original authority). The current definition maps every delegate directly to the base cap, making chain structure irrelevant. *(was #5)*
- [x] **4.4** `chain_bounded` now proved by real induction on chain to actually use `valid_chain` and `In a chain` in the proof. Currently both hypotheses are dead. The proof should proceed by induction on the chain, applying relative cap-monotonicity at each hop. *(was #4)*
- [ ] **4.5** Prove that irreflexive enforcement is preserved under delegation: if `irreflexive_enforcement ds` and the delegation is well-formed, then no agent can be punished via a delegation chain originating from itself. *(was #24)*
- [ ] **4.6** Add temporal scoping or explicit revocation to delegation. Currently `delegates_to` is a static boolean with no mechanism to expire or retract authority. *(was #27)*

## Phase 5: Connect the modules

- [x] **5.1** Define `temporally_lawful` combining `lawful` and `temporally_valid`. Prove that a response can be `lawful` (authorized + bounded) yet temporally invalid (enforcement after expiration), and that `temporally_lawful` excludes this. *(was #10)*
- [x] **5.2** Define `lawful_delegated` + `delegation_no_laundering` theorem requiring both base-system boundedness and delegate-cap boundedness. Prove that delegation cannot launder an unbounded response into a lawful one. *(was #11)*
- [x] **5.3** Extend the synthesis theorem to 5 conjuncts (delegation + temporal) to include temporal validity and delegation boundedness as conjuncts. The formal statement should match the informal claims. *(was #12)*
- [ ] **5.4** Prove a single combined theorem: for the homeworld system, no combination of delegation, aggregation, and temporal manipulation makes the extermination response lawful. *(was #13)*

## Phase 6: Bound aggregate enforcement

- [ ] **6.1** Add an enforcer population bound or jurisdiction partition so that aggregate punishment is finitely bounded, not just linear in an unbounded n. Options: cap the number of enforcers per obligation, or require non-overlapping enforcement jurisdictions. *(was #8)*
- [ ] **6.2** Add a *ne bis in idem* (double jeopardy) property: at most one enforcer may respond per violation, or at most one response per enforcer-violation pair. Prove that it implies a tighter aggregate bound. *(was #9)*

## Phase 7: Make core theorems non-tautological

- [ ] **7.1** Separate the definition of `lawful` from its characterization. Define lawful via an independent criterion (e.g., derivability in a deontic proof system, or satisfaction of a lawfulness predicate that doesn't literally conjoin `bounded`), then *prove* that lawful responses are bounded. The current `lawful := authorized ∧ bounded` makes `lawful → bounded` a projection and `unbounded → ¬lawful` trivial arithmetic. *(was #1, #2)*
- [ ] **7.2** After 7.1, the synthesis theorem and Kharak theorem will have actual proof content rather than being repackaged `exact` calls. *(was #32, #33)*

## Phase 8: Add missing results

- [x] **8.1** Prove completeness (`authorized_bounded_lawful`): `forall ds a o, authorized ds (mkPunitiveResponse e a o s) -> s <= severity_cap ds o -> lawful ds (mkPunitiveResponse e a o s)`. Everything within bounds and authorized IS lawful. *(was #35)*
- [x] **8.2** Define `linear_caps` property + `three_strikes_not_linear` theorem and prove that `three_strikes_system` violates it. Currently the counterexample is an orphaned observation connected to no named property. *(was #14)*
- [x] **8.3** Build `embargo_system` as second witness with consistency proof + lawful/unlawful examples (distinct from `homeworld_system`) and instantiate the main theorems in it. All current witnesses use one configuration. *(was #34)*

## Phase 9: Structural improvements

- [ ] **9.1** Replace the propositional `all_target_same` side condition with a dependent type or indexed list that structurally guarantees same target/obligation. *(was #20)*
- [ ] **9.2** Replace positional `nth_error` matching in `responses_match_obligations` with a relational pairing (list of obligation-response pairs). *(was #21)*
- [x] **9.3** Add `lawfulb`/`authorizedb`/`boundedb` with reflection lemmas + computational tests (`lawfulb`, `authorizedb`, `boundedb`) with reflection lemmas. Enable computation-time classification of concrete responses. *(was #19)*
- [ ] **9.4** Separate enforcement window from obligation duration. Add a `statute_of_limitations` field so enforcement can extend beyond obligation expiry. *(was #29)*
- [ ] **9.5** The `well_formed_temporal` condition `created_at < expires_at` permits degenerate single-tick obligations. Either document this as intentional or add a minimum-duration parameter. *(was #28)*

## Phase 10: Deontic logic depth

- [ ] **10.1** Add deontic modalities (OBL, PERM, FORB) as an inductive type or Kripke-style semantics. The current file uses boolean predicates with no modal structure. *(was #15)*
- [ ] **10.2** Model normative conflict: when two obligations impose contradictory requirements on the same agent, define and resolve the conflict (priority ordering, specificity, temporal precedence). *(was #16)*
- [ ] **10.3** Add defeasible norms: obligations that can be overridden by higher-priority norms or exceptions. Replace the current absolute booleans with a priority-indexed structure. *(was #17)*
- [ ] **10.4** Add a severity typing discipline distinguishing categories of punishment (fine, sanction, military action, etc.) with ordering constraints between categories. *(was #37)*
