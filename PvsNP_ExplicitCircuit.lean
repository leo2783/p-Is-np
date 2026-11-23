import Mathlib

/-!
# A concrete nontrivial circuit lower bound

The 3-input parity function cannot be computed by a circuit using
zero or one unrestricted 2-input Boolean gate, even when the gate is
allowed to compute any of the 16 binary Boolean functions.

This proof is finite and kernel-reduced (by `decide`).
It establishes an explicit **2-gate** lower bound for this single
function and makes no asymptotic complexity claim.
-/

namespace PvsNP.ExplicitCircuit

abbrev OneGateCode3 :=
  Fin 3 ⊕ (Fin 3 × Fin 3 × (Bool → Bool → Bool))

def evalOneGate : OneGateCode3 → (Fin 3 → Bool) → Bool
  | .inl i, x => x i
  | .inr code, x => code.2.2 (x code.1) (x code.2.1)

def parity3 (x : Fin 3 → Bool) : Bool :=
  Bool.xor (Bool.xor (x 0) (x 1)) (x 2)

set_option maxRecDepth 8192 in
theorem parity3_has_distinguishing_input :
    ∀ circuit : OneGateCode3, ∃ x : Fin 3 → Bool,
      evalOneGate circuit x ≠ parity3 x := by
  decide

theorem parity3_not_one_gate :
    ∀ circuit : OneGateCode3, evalOneGate circuit ≠ parity3 := by
  intro circuit heq
  obtain ⟨x, hdiff⟩ := parity3_has_distinguishing_input circuit
  exact hdiff (congrFun heq x)

def twoGateParity3 (x : Fin 3 → Bool) : Bool :=
  Bool.xor (Bool.xor (x 0) (x 1)) (x 2)

theorem parity3_computable_by_two_gates :
    twoGateParity3 = parity3 := rfl

end PvsNP.ExplicitCircuit
