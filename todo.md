# BoundedEnforcement.v — Remaining Cures

1. Prove that irreflexive enforcement is preserved under delegation: if `irreflexive_enforcement ds` and the delegation is well-formed, then no agent can be punished via a delegation chain originating from itself.
2. Add temporal scoping or explicit revocation to delegation. Currently `delegates_to` is a static boolean with no mechanism to expire or retract authority.
3. Prove a single combined theorem: for the homeworld system, no combination of delegation, aggregation, and temporal manipulation makes the extermination response lawful.
4. Add an enforcer population bound or jurisdiction partition so that aggregate punishment is finitely bounded, not just linear in an unbounded n.
5. Add a *ne bis in idem* (double jeopardy) property: at most one enforcer may respond per violation, or at most one response per enforcer-violation pair. Prove that it implies a tighter aggregate bound.
6. Separate the definition of `lawful` from its characterization. Define lawful via an independent criterion (e.g., derivability in a deontic proof system), then *prove* that lawful responses are bounded. The current `lawful := authorized ∧ bounded` makes `lawful → bounded` a projection and `unbounded → ¬lawful` trivial arithmetic.
7. After 6, the synthesis theorem and Kharak theorem will have actual proof content rather than being repackaged `exact` calls.
8. Replace the propositional `all_target_same` side condition with a dependent type or indexed list that structurally guarantees same target/obligation.
9. Replace positional `nth_error` matching in `responses_match_obligations` with a relational pairing (list of obligation-response pairs).
10. Separate enforcement window from obligation duration. Add a `statute_of_limitations` field so enforcement can extend beyond obligation expiry.
11. The `well_formed_temporal` condition `created_at < expires_at` permits degenerate single-tick obligations. Either document this as intentional or add a minimum-duration parameter.
12. Add deontic modalities (OBL, PERM, FORB) as an inductive type or Kripke-style semantics.
13. Model normative conflict: when two obligations impose contradictory requirements on the same agent, define and resolve the conflict (priority ordering, specificity, temporal precedence).
14. Add defeasible norms: obligations that can be overridden by higher-priority norms or exceptions. Replace the current absolute booleans with a priority-indexed structure.
15. Add a severity typing discipline distinguishing categories of punishment (fine, sanction, military action, etc.) with ordering constraints between categories.
