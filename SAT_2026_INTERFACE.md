# 2026 subexponential 3-SAT interface integration

## Source and formalized result

Anthropic, A 2^{o(n)} Time Algorithm for 3-SAT (2026):
https://github.com/anthropics/formal-math/tree/main/eth

Its Lean interface, eth/MainResults.lean, states MainResults.mainTheorem,
a 2026 counting theorem with a subexponential time bound, and
MainResults.ethIsFalse. This does not prove polynomial-time SAT or P = NP.

https://github.com/anthropics/formal-math/blob/main/eth/MainResults.lean

## Boundary identified and repaired locally

The new evalLiteral_paper_spec, evalClause_paper_spec, evalCNF_paper_spec,
and satisfiable_paper_iff theorems establish the exact equivalence between
the paper's existential literal/clause SAT semantics and this project's
Boolean evaluator for every input. The canonical_search_paper_semantics
theorem transfers the complete n-query canonical reduction into the
paper-style satisfiability predicate, including the m+n clause-size bound.

The paper uses the Boolean CNF type List (List (Fin n × Bool)), identical
to PvsNP.UnitRestriction.CNF n. Its IsKCNF predicate requires every clause
to have width at most k and the clause list to be Nodup.

The earlier impose inserts a unit clause directly. If the same unit
already occurs in the formula, this breaks Nodup, so that intermediate
formula cannot be supplied directly to the paper's counting theorem.

The new imposeCanonical function uses Mathlib List.dedup. Kernel-checked
Lean theorems prove semantic equivalence for every assignment,
distinct clauses, and preserved width for k >= 1. A concrete formal
counterexample establishes the failure of raw impose to preserve Nodup.

The formal WidthNodup predicate exactly mirrors the syntactic k-CNF conditions.
The canonical_sat_split theorem and chooseCanonicalBranch_sat require a correct
decision oracle only on valid WidthNodup formulas. The recursive canonicalRun
and canonical_full_search extend this domain guarantee through every query,
preserve satisfiability, use exactly n oracle calls, and prove uniqueness
of the final satisfying assignment on all original n variables (k >= 1).

An independent Rust regression test witnesses that boundary and checks
normalization on all assignments of its small fixture. The CI also runs
the larger Lean-generated differential evaluator tests.

## Remaining prerequisites before importing the paper theorem

The paper's counting theorem additionally assumes n >= 4, at least two
clauses, all declared variables occurring, and specific input encodings.
The new AllVariablesOccur and HasTwoDistinctClauses predicates have been
formally shown to survive every canonical restriction. The final
canonicalRun_paper_preconditions theorem combines these invariants with
WidthNodup and derives that the resulting formula still has >= 2 clauses.
The canonicalRun_length_le theorem additionally shows that if the initial
formula has m clauses, every n-step run ends with at most m+n clauses.
It reuses Mathlib's List.dedup_sublist and is a symbolic size bound,
not an assumed runtime bound on the SAT decision oracle.
The published proof uses Lean and Mathlib v4.33.1; this project uses
v4.35.0 and separately imports a TM0 complexity library. This addition
formally bridges input shape and normalization, not the external proof
term or full machine-model complexity bound.

The paper's 2^{o(n)} bound is asymptotic. The existing local Lean
theorems on exact n oracle calls and n unit clauses give a route to
transfer a compatible subexponential decision procedure to witness
reconstruction. No polynomial-time runtime is inferred.

## Counting-to-decision theorem

The `evaluatorCount_eq_paperCount` theorem equates the Boolean evaluator
count with the 2026-style satisfying-assignment count. The positive-count
characterization yields `countDecision_correct`, while
`counting_oracle_canonical_search` specializes the verified full-search
theorem to any count oracle that correctly counts valid k-CNF inputs.
This is conditional on the counting oracle; it does not establish the
external algorithm's Turing-machine time bound.
