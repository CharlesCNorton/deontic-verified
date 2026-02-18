# BoundedEnforcement.v — Remaining Cures

1. Fix the duplicate third conjunct in `modally_consistent` (currently identical to the first). Replace with `forall a o, ns a o = FORB -> ns a o <> OBL` or delete it.
2. Remove the hardcoded `mkAgent 0` in the FORB clause of `grounded`. Universally quantify over the target agent or parametrize over a distinguished target.
3. Strengthen `grounded` so that FORB entails `obligated ds a o = false` outright, eliminating the disjunction that forces `forbidden_no_violation` to take `obligated = false` as an external hypothesis.
4. Prove `modally_consistent homeworld_norms` and connect the modality section to the lawful/bounded framework so that OBL/PERM/FORB have consequences for enforcement.
5. Deduplicate or separate the constraints in `ne_bis_in_idem`: either drop the redundant `NoDup` (since `length <= 1` already implies it) or generalize to multi-enforcer single-response-per-enforcer by dropping the length constraint.
6. Require `NoDup (agents ds)` in `coherent` or `consistent` so that population-size reasoning is sound.
7. Prove the pigeonhole link: derive `length responses <= length (agents ds)` from `distinct_enforcers` + `enforcers_in_population`, then remove the bare hypothesis from `population_bounded_aggregate`.
8. Prove `acyclic three_hop_delegation` and establish `well_formed_delegation three_hop_delegation`.
9. Eliminate the dead `authorized` hypothesis in `no_unbounded_lawful`, or restructure the statement so authorization does real work (e.g., prove the contrapositive: lawful implies bounded, so unbounded implies not lawful, with authorization as context for why the question matters).
10. Add a second witness system with qualitatively different structure: cyclic enforcement attempt (shown inconsistent), multi-hop delegation with branching, or temporal window overlap.
11. Derive severity caps from a primitive proportionality relation between violation harm and punishment magnitude, rather than taking the cap as an axiomatic field of `DeonticSystem`.
12. Replace `violated : Agent -> Obligation -> bool` with a graded violation type admitting partial compliance, mitigating circumstances, and culpability levels (intentional, negligent, reckless, strict liability). Make severity a function of culpability, not just obligation.
13. Model contrary-to-duty obligations: "if you violate obligation A, you must do B." Add second-order norms triggered by violations.
14. Model normative conflict: when two obligations impose contradictory requirements on the same agent, define and resolve the conflict (priority ordering, specificity, temporal precedence).
15. Add defeasible norms: obligations that can be overridden by higher-priority norms or exceptions. Replace the current absolute booleans with a priority-indexed structure.
16. Add a severity typing discipline distinguishing categories of punishment (fine, sanction, military action, etc.) with ordering constraints between categories and exhaustion requirements (e.g., military action requires exhaustion of diplomatic remedies).
17. Add rights as constraints on enforcement: due process, proportionality review, appeal, habeas corpus. Enforcement authority should be bounded not just by severity caps but by procedural obligations owed to the target.
18. Add an epistemic layer: evidence, burden of proof, presumption of innocence, adjudication error. Enforcement should be conditioned on an evidence predicate, not the God's-eye `violated`.
19. Add procedural requirements to enforcement authority: jurisdiction, standing, judicial review, separation of powers. Derive `may_enforce` from institutional structure rather than taking it as a primitive boolean.
20. Add collective responsibility: joint liability, corporate personhood, complicity, vicarious responsibility. Extend `Agent` beyond atomic individuals.
21. Add reparative and restorative remedies alongside punitive response: compensation, restitution, rehabilitation. Distinguish retributive from corrective enforcement.
22. Model obligation creation, amendment, revocation, and supersession. Extend the temporal layer from static windows to dynamic norm change.
23. Add delegation revocation: allow delegation to be withdrawn, suspended, or made conditional, not just expired.
24. Add enforcement cost: make punishment non-free so that the model captures resource constraints on whether and how much enforcement occurs.
25. Model recidivism and enforcement history: repeated violations, escalating responses, rehabilitation credit. Ground the "three strikes" counterexample in a dynamic model of offense history.
26. Add multi-agent enforcement coordination: game-theoretic reasoning about strategic enforcement behavior when multiple enforcers respond to the same violation.
27. Distinguish severity-zero punishment from no punishment. Either make `Severity` positive (`S n`) or add a separate `enforced : bool` flag.
28. Require `enforcer <> target` in `authorized` or `lawful` directly, rather than relying on `may_enforce` returning false for self-pairs as a convention maintained outside the type.
29. Add `Notation` or `Ltac` automation for the recurring `unfold; simpl; destruct; subst; try discriminate; try lia` pattern. Reduce proof fragility.
30. Add `Extraction` directives for the Boolean decision procedures (`lawfulb`, `authorizedb`, `boundedb`) so the computational content is usable outside Coq.
31. Use the module/functor system to parametrize over carrier types (agent, obligation representations), enabling instantiation beyond nat-indexed records.
32. Extend the temporal model beyond discrete `nat` time: continuous or dense time, concurrency, uncertainty about event ordering, procedural timelines, appeal periods.
