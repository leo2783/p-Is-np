# P vs NP — verified Lean research

This repository is a machine-checkable research workspace. **It does not establish
P = NP or P ≠ NP.** The source code separates genuine proofs from assumptions
and from empirical tests.

## Formal foundations

Lean 4.35.0, Mathlib 4.35.0 and the independent `starpos/lean-np-complete`
v0.5.0 library supply precise TM0 complexity classes and Cook–Levin.

- `PvsNP_FormalClasses.lean`: SAT is in P iff P = NP, and SAT is not in
  P iff P ≠ NP; similarly for 3SAT. Uses actual Turing-machine complexity
  notions from NPComplete, not placeholder sets.
- `PvsNP.lean`: an independent abstract derivation of the same implication,
  explicitly listing its NP-completeness and closure hypotheses.

## Verified restricted-model results

- `PvsNP_BlackBox.lean`: exact deterministic query complexity of OR is
  N for N bits; also proves a general full-sensitivity lower bound and
  the one-query existential-witness side of the black-box separation.
- `PvsNP_Counting.lean`: circuit-description encoding, total evaluation,
  and Shannon's counting lower bound. In particular, at least one 8-input
  Boolean function is impossible for the encoded at-most-10-gate circuits.
- `PvsNP_ExplicitCircuit.lean`: odd parity of three inputs cannot be
  expressed by a single unrestricted binary Boolean gate; two XOR gates suffice.
- `PvsNP_TwoCNF_Expressivity.lean`: 3-bit odd parity has a 3-CNF encoding
  but has no equivalent 2-CNF on its three inputs.
- `PvsNP_MajorityClosure.lean`: 2-CNF solution sets preserve coordinatewise
  majority for any finite number of variables.
- `PvsNP_Projected2CNF.lean`: extends the majority argument through
  existentially quantified auxiliary variables, precluding even 2-CNF
  gadgets for odd 3-bit parity.

## Non-exhaustive witness extraction

- `PvsNP_SelfReduction.lean`: a greedy search-to-decision reduction on Boolean
  witnesses. Assuming a correct decision oracle for satisfiable partial
  assignments, a length-`n` satisfying witness is constructed with exactly
  `n` oracle calls, including a machine-checked cost counter. This is the
  combinatorial self-reduction; polynomial running time still depends on
  the time to evaluate and prepare the oracle queries.

- `PvsNP_UnitRestriction.lean`: semantics of unit clauses on concrete CNF formulas,
  a non-enumerative SAT splitting equivalence, order-independent restrictions,
  and inconsistency of contradictory units. These lemmas justify the CNF
  restriction step used by a SAT search-to-decision reduction. A concrete
  SAT-oracle algorithm keeps its restricted CNF satisfiable while fixing all
  variables in exactly `n` oracle calls and adding exactly `n` unit clauses.

- `PvsNP_Resolution.lean`: propositional resolution rule soundness and
  inductive derivation soundness, including a proof that a satisfiable
  clause set admits no empty-clause resolution refutation. The proof
  operates symbolically without enumerating all assignments.

## Independent executable checks

`rust/src/main.rs` tests deterministic OR minimax complexity,
a 2-SAT implication-graph algorithm against exhaustive enumeration over
50,816 formulas, parity/circuit counting, and 2-CNF majority closure.

Run the proofs under GitHub Actions, or locally:

```bash
lake update
lake exe cache get
for file in PvsNP.lean PvsNP_BlackBox.lean PvsNP_Counting.lean \
  PvsNP_ExplicitCircuit.lean PvsNP_TwoCNF_Expressivity.lean \
  PvsNP_MajorityClosure.lean PvsNP_Projected2CNF.lean; do
  lake env lean "$file"
done
lake build NPComplete
lake env lean PvsNP_FormalClasses.lean
cargo test --manifest-path rust/Cargo.toml
```

## The remaining mathematical gap

Proving that **SAT has no deterministic polynomial-time decider** would
settle P ≠ NP. Conversely, finding and proving a polynomial-time SAT decider
would settle P = NP. The circuit-counting proof concerns an unspecified hard
function. It supplies no SAT-specific asymptotic lower bound. The black-box
query lower bound applies only to algorithms that cannot examine formula
structure, and thus cannot imply a general SAT time lower bound.

Formal kernel validation establishes precisely the theorems stated in
source files; it does not upgrade their assumptions or restricted models.
