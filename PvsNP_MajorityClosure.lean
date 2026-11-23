import Mathlib

/-!
# Majority closure for arbitrary 2-CNF formulas

A Boolean relation definable by a 2-CNF formula is preserved under
coordinatewise majority. This is the bijunctive polymorphism property.
The proof is uniform in the number of variables and clauses.

This theorem does not prove P ≠ NP.
-/

namespace PvsNP.MajorityClosure

def majority (a b c : Bool) : Bool :=
  (a && b) || (a && c) || (b && c)

theorem majority_preserves_or :
    ∀ a₁ a₂ a₃ b₁ b₂ b₃ : Bool,
      (a₁ || b₁) = true →
      (a₂ || b₂) = true →
      (a₃ || b₃) = true →
      (majority a₁ a₂ a₃ || majority b₁ b₂ b₃) = true := by
  decide

def pointwiseMajority {n : ℕ}
    (x y z : Fin n → Bool) : Fin n → Bool :=
  fun i => majority (x i) (y i) (z i)

abbrev Literal (n : ℕ) := Fin n × Bool
abbrev Clause (n : ℕ) := Literal n × Literal n

def evalLiteral {n : ℕ} (l : Literal n) (x : Fin n → Bool) : Bool :=
  if l.2 then x l.1 else !(x l.1)

def evalClause {n : ℕ} (c : Clause n) (x : Fin n → Bool) : Bool :=
  evalLiteral c.1 x || evalLiteral c.2 x

def evalCNF {n : ℕ} (cs : List (Clause n)) (x : Fin n → Bool) : Bool :=
  cs.all (fun c => evalClause c x)

theorem literal_preserves_majority {n : ℕ}
    (l : Literal n) (x y z : Fin n → Bool) :
    evalLiteral l (pointwiseMajority x y z) =
      majority (evalLiteral l x) (evalLiteral l y) (evalLiteral l z) := by
  rcases l with ⟨i, pol⟩
  cases pol <;>
    cases hx : x i <;>
    cases hy : y i <;>
    cases hz : z i <;>
    simp [evalLiteral, pointwiseMajority, majority, hx, hy, hz]

theorem clause_preserves_majority {n : ℕ}
    (c : Clause n) (x y z : Fin n → Bool)
    (hx : evalClause c x = true)
    (hy : evalClause c y = true)
    (hz : evalClause c z = true) :
    evalClause c (pointwiseMajority x y z) = true := by
  simpa only [evalClause, literal_preserves_majority] using
    (majority_preserves_or
      (evalLiteral c.1 x) (evalLiteral c.1 y) (evalLiteral c.1 z)
      (evalLiteral c.2 x) (evalLiteral c.2 y) (evalLiteral c.2 z)
      hx hy hz)

theorem twoCNF_preserves_majority {n : ℕ}
    (cs : List (Clause n)) (x y z : Fin n → Bool)
    (hx : evalCNF cs x = true)
    (hy : evalCNF cs y = true)
    (hz : evalCNF cs z = true) :
    evalCNF cs (pointwiseMajority x y z) = true := by
  induction cs with
  | nil => rfl
  | cons c rest ih =>
      have ax : evalClause c x = true ∧ evalCNF rest x = true := by
        simpa [evalCNF, Bool.and_eq_true] using hx
      have ay : evalClause c y = true ∧ evalCNF rest y = true := by
        simpa [evalCNF, Bool.and_eq_true] using hy
      have az : evalClause c z = true ∧ evalCNF rest z = true := by
        simpa [evalCNF, Bool.and_eq_true] using hz
      have hc := clause_preserves_majority c x y z ax.1 ay.1 az.1
      have hr := ih ax.2 ay.2 az.2
      change (evalClause c (pointwiseMajority x y z) &&
        evalCNF rest (pointwiseMajority x y z)) = true
      simp [hc, hr]

end PvsNP.MajorityClosure
