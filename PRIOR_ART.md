# Prior art and reproducibility audit (2026-11-23)

The files listed here independently formalize restricted results. Their
mathematical claims had established predecessors before 2026. Re-proving
these statements in Lean does not constitute a new complexity-theoretic
separation. The references below are historical citations, not imported
Lean proof terms; a direct library reuse must be verified separately.

| Family | Project files | Prior established result | Current scope |
| --- | --- | --- | --- |
| Deterministic Boolean query bounds | `PvsNP_BlackBox.lean` | Buhrman and de Wolf (2002), *Complexity Measures and Decision Tree Complexity: A Survey*, Theoretical Computer Science 288(1):21–43, https://doi.org/10.1016/S0304-3975(01)00144-X | Exact OR query depth and a zero-input sensitivity bound in an explicitly defined decision-tree model |
| Counting bounds for Boolean circuits | `PvsNP_Counting.lean` | Shannon (1949), *The Synthesis of Two-Terminal Switching Circuits*, Bell System Technical Journal 28(1):59–98; historical overview: https://www.scottaaronson.com/papers/pnp-kindle.pdf | Abstract counting plus a total code interpreter, with a concrete finite lower-bound instance |
| Bijunctive / majority closure | `PvsNP_MajorityClosure.lean`, `PvsNP_TwoCNF_Expressivity.lean`, `PvsNP_Projected2CNF.lean` | Schaefer (1978), *The Complexity of Satisfiability Problems*, STOC, https://doi.org/10.1145/800133.804350, notably the majority characterization of bijunctive Boolean relations | Uniform 2-CNF closure and parity non-definability, including existential projection |
| SAT search-to-decision | `PvsNP_SelfReduction.lean`, `PvsNP_UnitRestriction.lean`, `PvsNP_ThreeSAT_Restriction.lean` | Arora and Barak (2009), *Computational Complexity: A Modern Approach*, §2.5, decision versus search | Exact-query correctness and native 3-SAT unit-clause search, conditional on an accurate decision oracle |
| Propositional resolution soundness | `PvsNP_Resolution.lean` | Robinson (1965), *A Machine-Oriented Logic Based on the Resolution Principle*, JACM 12(1):23–41; see the 2009 Stanford Encyclopedia overview: https://plato.stanford.edu/archives/fall2009/entries/reasoning-automated/ | Inductive soundness, empty-refutation soundness, and equisatisfiability on addition of derived clauses |

## Existing machine-checked dependency

`PvsNP_FormalClasses.lean` **imports `NPComplete`** from
`starpos/lean-np-complete` v0.5.0, including its proved 3-SAT
NP-completeness results. That dependency is a genuine Lean import;
the five references above are literature attributions. In addition,
Mathlib already provides SAT/LRAT-oriented infrastructure under
`Mathlib.Tactic.Sat.FromLRAT`; this project has not proved that its
custom resolution syntax directly interoperates with that checker.

## Score audit

The user set the score to 30 after an earlier 30-point deduction.
Subsequent previously reported milestones reached 38 points
(including a completed +10 branch). The rule added on 2026-11-23
requires -1 for each established pre-2026 theorem family omitted
from the prior-art inventory. Five separately identified families
above were omitted when first formalized, so the audited score is:

`38 - 5 = 33`

Each family is counted once: corollaries and minor rearrangements are
not charged again without distinct historical precedence evidence.
This is an attribution/score correction, not a claim of a P vs NP proof.
Pending GitHub CI results do not count as successes or failures until
their final conclusions are available.
