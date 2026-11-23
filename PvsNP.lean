import Mathlib

/-!
# P versus NP: conditional reductions and finite Boolean results

This file does not settle P versus NP.
-/

namespace PvsNP
universe u

theorem sat_in_P_iff_P_eq_NP
    {Language : Type u}
    (P NP : Set Language) (SAT : Language)
    (Reduces : Language → Language → Prop)
    (hPsub : P ⊆ NP)
    (hSAT : SAT ∈ NP)
    (hComplete : ∀ L, L ∈ NP → Reduces L SAT)
    (hClosed : ∀ {L K : Language}, Reduces L K → K ∈ P → L ∈ P) :
    SAT ∈ P ↔ P = NP := by
  constructor
  · intro hSatP
    apply Set.Subset.antisymm hPsub
    intro L hL
    exact hClosed (hComplete L hL) hSatP
  · intro hEq
    rw [hEq]
    exact hSAT

theorem sat_not_in_P_iff_P_ne_NP
    {Language : Type u}
    (P NP : Set Language) (SAT : Language)
    (Reduces : Language → Language → Prop)
    (hPsub : P ⊆ NP)
    (hSAT : SAT ∈ NP)
    (hComplete : ∀ L, L ∈ NP → Reduces L SAT)
    (hClosed : ∀ {L K : Language}, Reduces L K → K ∈ P → L ∈ P) :
    SAT ∉ P ↔ P ≠ NP := by
  constructor
  · intro hNotSat hEq
    have hSat : SAT ∈ P :=
      (sat_in_P_iff_P_eq_NP P NP SAT Reduces hPsub hSAT hComplete hClosed).mpr hEq
    exact hNotSat hSat
  · intro hNe hSat
    have hEq : P = NP :=
      (sat_in_P_iff_P_eq_NP P NP SAT Reduces hPsub hSAT hComplete hClosed).mp hSat
    exact hNe hEq

namespace TwoSAT

theorem clause_iff_implications (a b : Bool) :
    (a = true ∨ b = true) ↔
    (a = false → b = true) ∧ (b = false → a = true) := by
  cases a <;> cases b <;> simp

def positiveUnitFormula (n : ℕ) (x : Fin n → Bool) : Prop :=
  ∀ i, x i = true

theorem positiveUnitFormula_sat (n : ℕ) :
    ∃ x : Fin n → Bool, positiveUnitFormula n x := by
  refine ⟨fun _ => true, ?_⟩
  intro i
  rfl

end TwoSAT
end PvsNP
