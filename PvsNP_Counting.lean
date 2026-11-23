import Mathlib

namespace PvsNP.Counting

theorem exists_function_outside_family
    {Inputs Circuits : Type*} [Fintype Inputs] [Fintype Circuits]
    (interpret : Circuits → (Inputs → Bool))
    (hsmall : Fintype.card Circuits < 2 ^ Fintype.card Inputs) :
    ∃ target : Inputs → Bool, ∀ c : Circuits, interpret c ≠ target := by
  classical
  by_contra hnone
  push Not at hnone
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


/-!
## Circuit-description counting

A description records s arbitrary binary Boolean truth tables and s pairs
of source wires, plus an output wire. It overcounts proper acyclic circuits,
which is safe for information-theoretic lower bounds. The decoder is abstract:
an explicit circuit evaluator is a separate formalization obligation.
-/

abbrev CircuitDescription (n s : ℕ) :=
  Fin (n + s) × (Fin s →
    (Fin (n + s) × Fin (n + s) × (Bool → Bool → Bool)))

theorem circuit_description_card (n s : ℕ) :
    Fintype.card (CircuitDescription n s) =
      (n + s) * (16 * (n + s) ^ 2) ^ s := by
  classical
  simp [CircuitDescription, Fintype.card_prod] <;> ring <;> simp

theorem circuit_description_counting (n s : ℕ)
    (decode : CircuitDescription n s → (Fin (2 ^ n) → Bool))
    (hsmall : (n + s) * (16 * (n + s) ^ 2) ^ s < 2 ^ (2 ^ n)) :
    ∃ f : Fin (2 ^ n) → Bool, ∀ d, decode d ≠ f := by
  apply exists_function_outside_family decode
  rw [circuit_description_card]
  simpa using hsmall

theorem hard_function_for_eight_input_and_ten_gates
    (decode : CircuitDescription 8 10 → (Fin (2 ^ 8) → Bool)) :
    ∃ f : Fin (2 ^ 8) → Bool, ∀ d, decode d ≠ f := by
  apply circuit_description_counting 8 10 decode
  norm_num

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
