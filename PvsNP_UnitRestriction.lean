import Mathlib

/-!
# Unit-clause restriction for finite Boolean CNF formulas

Adding a unit clause fixes one variable to a chosen Boolean value.
We prove the exact semantic equivalence, disjunction of the two
restrictions (SAT splitting), order independence, and inconsistency
of contradictory units. No truth-table enumeration is used.
-/

namespace PvsNP.UnitRestriction

abbrev Literal (n : ℕ) := Fin n × Bool
abbrev Clause (n : ℕ) := List (Literal n)
abbrev CNF (n : ℕ) := List (Clause n)

def evalLiteral {n : ℕ} (lit : Literal n) (x : Fin n → Bool) : Bool :=
  if lit.2 then x lit.1 else !(x lit.1)

def evalClause {n : ℕ} (clause : Clause n) (x : Fin n → Bool) : Bool :=
  clause.any (fun lit => evalLiteral lit x)

def evalCNF {n : ℕ} (phi : CNF n) (x : Fin n → Bool) : Bool :=
  phi.all (fun clause => evalClause clause x)

def Satisfiable {n : ℕ} (phi : CNF n) : Prop :=
  ∃ x : Fin n → Bool, evalCNF phi x = true

def impose {n : ℕ} (phi : CNF n) (i : Fin n) (bit : Bool) : CNF n :=
  [(i, bit)] :: phi

theorem evalCNF_impose_iff {n : ℕ}
    (phi : CNF n) (i : Fin n) (bit : Bool) (x : Fin n → Bool) :
    evalCNF (impose phi i bit) x = true ↔
      evalCNF phi x = true ∧ x i = bit := by
  cases bit <;> cases hx : x i <;>
    simp [impose, evalCNF, evalClause, evalLiteral, hx]

theorem satisfiable_impose_iff {n : ℕ}
    (phi : CNF n) (i : Fin n) (bit : Bool) :
    Satisfiable (impose phi i bit) ↔
      ∃ x : Fin n → Bool, evalCNF phi x = true ∧ x i = bit := by
  simp only [Satisfiable, evalCNF_impose_iff]

theorem sat_split {n : ℕ} (phi : CNF n) (i : Fin n) :
    Satisfiable phi ↔
      Satisfiable (impose phi i false) ∨
      Satisfiable (impose phi i true) := by
  constructor
  · rintro ⟨x, hx⟩
    cases hb : x i with
    | false =>
        left
        exact ⟨x, (evalCNF_impose_iff phi i false x).mpr ⟨hx, hb⟩⟩
    | true =>
        right
        exact ⟨x, (evalCNF_impose_iff phi i true x).mpr ⟨hx, hb⟩⟩
  · rintro (⟨x, hx⟩ | ⟨x, hx⟩)
    · exact ⟨x, ((evalCNF_impose_iff phi i false x).mp hx).1⟩
    · exact ⟨x, ((evalCNF_impose_iff phi i true x).mp hx).1⟩

theorem restriction_order_independent {n : ℕ}
    (phi : CNF n) (i j : Fin n) (a b : Bool) :
    Satisfiable (impose (impose phi i a) j b) ↔
      Satisfiable (impose (impose phi j b) i a) := by
  constructor
  · rintro ⟨x, hx⟩
    rcases (evalCNF_impose_iff (impose phi i a) j b x).mp hx with ⟨hpre, hj⟩
    rcases (evalCNF_impose_iff phi i a x).mp hpre with ⟨hphi, hi⟩
    refine ⟨x, (evalCNF_impose_iff (impose phi j b) i a x).mpr ?_⟩
    exact ⟨(evalCNF_impose_iff phi j b x).mpr ⟨hphi, hj⟩, hi⟩
  · rintro ⟨x, hx⟩
    rcases (evalCNF_impose_iff (impose phi j b) i a x).mp hx with ⟨hpre, hi⟩
    rcases (evalCNF_impose_iff phi j b x).mp hpre with ⟨hphi, hj⟩
    refine ⟨x, (evalCNF_impose_iff (impose phi i a) j b x).mpr ?_⟩
    exact ⟨(evalCNF_impose_iff phi i a x).mpr ⟨hphi, hi⟩, hj⟩

theorem conflicting_units_unsatisfiable {n : ℕ}
    (phi : CNF n) (i : Fin n) :
    ¬ Satisfiable (impose (impose phi i false) i true) := by
  rintro ⟨x, hx⟩
  rcases (evalCNF_impose_iff (impose phi i false) i true x).mp hx with
    ⟨hpre, htrue⟩
  have hfalse : x i = false :=
    ((evalCNF_impose_iff phi i false x).mp hpre).2
  rw [hfalse] at htrue
  cases htrue

end PvsNP.UnitRestriction
