import Mathlib

/-!
# A three-variable expressivity lower bound for 2-CNF

Any 2-CNF formula is closed under the pointwise majority operation
on satisfying assignments. Three one-hot assignments are witnesses:
if all three satisfy a 2-CNF, then the all-zero assignment must satisfy.
Three-bit odd parity violates this closure.

This is a restricted expressivity result, not a separation of P and NP.
-/

namespace PvsNP.TwoCNF

abbrev Literal := Fin 3 × Bool
abbrev Clause := Literal × Literal

def evalLiteral (lit : Literal) (x : Fin 3 → Bool) : Bool :=
  if lit.2 then x lit.1 else !x lit.1

def evalClause (c : Clause) (x : Fin 3 → Bool) : Bool :=
  evalLiteral c.1 x || evalLiteral c.2 x

def evalCNF (cs : List Clause) (x : Fin 3 → Bool) : Bool :=
  cs.all (fun c => evalClause c x)

def zero : Fin 3 → Bool := fun _ => false
def oneHot (k : Fin 3) (i : Fin 3) : Bool := decide (i = k)

def parity3 (x : Fin 3 → Bool) : Bool :=
  Bool.xor (Bool.xor (x 0) (x 1)) (x 2)

theorem clause_majority_closure :
    ∀ c : Clause,
      evalClause c (oneHot 0) = true →
      evalClause c (oneHot 1) = true →
      evalClause c (oneHot 2) = true →
      evalClause c zero = true := by
  decide

theorem cnf_majority_closure (cs : List Clause) :
    evalCNF cs (oneHot 0) = true →
    evalCNF cs (oneHot 1) = true →
    evalCNF cs (oneHot 2) = true →
    evalCNF cs zero = true := by
  induction cs with
  | nil =>
      intro _ _ _
      rfl
  | cons c rest ih =>
      intro h0 h1 h2
      have a0 : evalClause c (oneHot 0) = true ∧ evalCNF rest (oneHot 0) = true := by
        simpa [evalCNF, Bool.and_eq_true] using h0
      have a1 : evalClause c (oneHot 1) = true ∧ evalCNF rest (oneHot 1) = true := by
        simpa [evalCNF, Bool.and_eq_true] using h1
      have a2 : evalClause c (oneHot 2) = true ∧ evalCNF rest (oneHot 2) = true := by
        simpa [evalCNF, Bool.and_eq_true] using h2
      have hc : evalClause c zero = true :=
        clause_majority_closure c a0.1 a1.1 a2.1
      have hr : evalCNF rest zero = true :=
        ih a0.2 a1.2 a2.2
      change (evalClause c zero && evalCNF rest zero) = true
      simp [hc, hr]

theorem parity_one_hot (k : Fin 3) : parity3 (oneHot k) = true := by
  fin_cases k <;> decide

theorem parity_zero : parity3 zero = false := by decide

theorem three_bit_parity_not_representable_by_2CNF (cs : List Clause) :
    (fun x => evalCNF cs x) ≠ parity3 := by
  intro h
  have a0 : evalCNF cs (oneHot 0) = true := by
    simpa [parity_one_hot] using congrFun h (oneHot 0)
  have a1 : evalCNF cs (oneHot 1) = true := by
    simpa [parity_one_hot] using congrFun h (oneHot 1)
  have a2 : evalCNF cs (oneHot 2) = true := by
    simpa [parity_one_hot] using congrFun h (oneHot 2)
  have hz : evalCNF cs zero = true := cnf_majority_closure cs a0 a1 a2
  have hzero : evalCNF cs zero = false := by
    simpa [parity_zero] using congrFun h zero
  cases hzero.symm.trans hz


/-!
The same three-bit parity function does have a 3-CNF representation:
one clause excludes each of the four even-parity assignments.
-/
def oddParity3CNF (x : Fin 3 → Bool) : Bool :=
  (x 0 || x 1 || x 2) &&
  (x 0 || !(x 1) || !(x 2)) &&
  (!(x 0) || x 1 || !(x 2)) &&
  (!(x 0) || !(x 1) || x 2)

theorem three_bit_parity_representable_by_3CNF :
    oddParity3CNF = parity3 := by
  funext x
  cases h0 : x 0 <;>
    cases h1 : x 1 <;>
    cases h2 : x 2 <;>
    simp [oddParity3CNF, parity3, h0, h1, h2]

end PvsNP.TwoCNF
