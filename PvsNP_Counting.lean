import Mathlib

namespace PvsNP.Counting

theorem exists_function_outside_family
    {Inputs Circuits : Type*} [Fintype Inputs] [Fintype Circuits]
    (interpret : Circuits → (Inputs → Bool))
    (hsmall : Fintype.card Circuits < 2 ^ Fintype.card Inputs) :
    ∃ target : Inputs → Bool, ∀ c : Circuits, interpret c ≠ target := by
  classical
  by_contra hnone
  push_neg at hnone
  have hsurj : Function.Surjective interpret := by
    intro target
    obtain ⟨c, hc⟩ := hnone target
    exact ⟨c, hc⟩
  have hcount : Fintype.card (Inputs → Bool) ≤ Fintype.card Circuits :=
    Fintype.card_le_of_surjective interpret hsurj
  have hfunctions : Fintype.card (Inputs → Bool) = 2 ^ Fintype.card Inputs := by simp
  rw [hfunctions] at hcount
  omega

theorem exists_hard_n_bit_function
    (n descriptions : ℕ)
    (decode : Fin descriptions → (Fin (2 ^ n) → Bool))
    (hsmall : descriptions < 2 ^ (2 ^ n)) :
    ∃ f : Fin (2 ^ n) → Bool, ∀ c, decode c ≠ f := by
  apply exists_function_outside_family decode
  simpa using hsmall

end PvsNP.Counting

namespace PvsNP.Bridge
universe u

theorem SAT_superpoly_circuits_implies_P_ne_NP
    {Language : Type u} (P NP : Set Language) (SAT : Language)
    (satCircuitSize : ℕ → ℕ)
    (hSATnp : SAT ∈ NP)
    (hUniformToCircuits :
      SAT ∈ P → ∃ c k : ℕ, ∀ n, satCircuitSize n ≤ c * (n + 1) ^ k)
    (hSuperpolySAT :
      ∀ c k : ℕ, ∃ n, c * (n + 1) ^ k < satCircuitSize n) :
    P ≠ NP := by
  intro hEq
  have hSatP : SAT ∈ P := by
    rw [hEq]
    exact hSATnp
  obtain ⟨c, k, hUpper⟩ := hUniformToCircuits hSatP
  obtain ⟨n, hLower⟩ := hSuperpolySAT c k
  have hForN := hUpper n
  omega

end PvsNP.Bridge
