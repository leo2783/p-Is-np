import Mathlib

/-!
# Existential projection preserves majority closure for 2-CNF

Allowing arbitrarily many auxiliary existential Boolean variables does not
enable a 2-CNF gadget to express three-variable parity.
This does not separate unrestricted P and NP.
-/
namespace PvsNP.Projection

def majority (a b c : Bool) : Bool :=
  (a && b) || (a && c) || (b && c)

def pwMajority {α : Type} (x y z : α → Bool) : α → Bool :=
  fun i => majority (x i) (y i) (z i)

theorem majority_preserves_or :
    ∀ a₁ a₂ a₃ b₁ b₂ b₃ : Bool,
      (a₁ || b₁) = true →
      (a₂ || b₂) = true →
      (a₃ || b₃) = true →
      (majority a₁ a₂ a₃ || majority b₁ b₂ b₃) = true := by
  decide

abbrev Lit (α : Type) := α × Bool
abbrev Clause (α : Type) := Lit α × Lit α

def evalLit {α : Type} (l : Lit α) (x : α → Bool) : Bool :=
  if l.2 then x l.1 else !(x l.1)

def evalClause {α : Type} (c : Clause α) (x : α → Bool) : Bool :=
  evalLit c.1 x || evalLit c.2 x

def evalCNF {α : Type} (cs : List (Clause α)) (x : α → Bool) : Bool :=
  cs.all (fun c => evalClause c x)

theorem lit_majority {α : Type} (l : Lit α) (x y z : α → Bool) :
    evalLit l (pwMajority x y z) =
      majority (evalLit l x) (evalLit l y) (evalLit l z) := by
  rcases l with ⟨i, pol⟩
  cases pol <;> cases hx : x i <;> cases hy : y i <;> cases hz : z i <;>
    simp [evalLit, pwMajority, majority, hx, hy, hz]

theorem clause_majority {α : Type} (c : Clause α) (x y z : α → Bool)
    (hx : evalClause c x = true)
    (hy : evalClause c y = true)
    (hz : evalClause c z = true) :
    evalClause c (pwMajority x y z) = true := by
  simpa only [evalClause, lit_majority] using
    (majority_preserves_or
      (evalLit c.1 x) (evalLit c.1 y) (evalLit c.1 z)
      (evalLit c.2 x) (evalLit c.2 y) (evalLit c.2 z) hx hy hz)

theorem cnf_majority {α : Type} (cs : List (Clause α)) (x y z : α → Bool)
    (hx : evalCNF cs x = true)
    (hy : evalCNF cs y = true)
    (hz : evalCNF cs z = true) :
    evalCNF cs (pwMajority x y z) = true := by
  induction cs with
  | nil => rfl
  | cons c rest ih =>
      have ax : evalClause c x = true ∧ evalCNF rest x = true := by
        simpa [evalCNF, Bool.and_eq_true] using hx
      have ay : evalClause c y = true ∧ evalCNF rest y = true := by
        simpa [evalCNF, Bool.and_eq_true] using hy
      have az : evalClause c z = true ∧ evalCNF rest z = true := by
        simpa [evalCNF, Bool.and_eq_true] using hz
      have hc := clause_majority c x y z ax.1 ay.1 az.1
      have hr := ih ax.2 ay.2 az.2
      change (evalClause c (pwMajority x y z) &&
        evalCNF rest (pwMajority x y z)) = true
      simp [hc, hr]

def combine {α β : Type} (x : α → Bool) (y : β → Bool) : Sum α β → Bool
  | .inl a => x a
  | .inr b => y b

theorem combine_majority {α β : Type}
    (x₁ x₂ x₃ : α → Bool) (y₁ y₂ y₃ : β → Bool) :
    combine (pwMajority x₁ x₂ x₃) (pwMajority y₁ y₂ y₃) =
      pwMajority (combine x₁ y₁) (combine x₂ y₂) (combine x₃ y₃) := by
  funext i
  cases i <;> rfl

def projected2CNF {α β : Type} (cs : List (Clause (Sum α β)))
    (x : α → Bool) : Prop :=
  ∃ y : β → Bool, evalCNF cs (combine x y) = true

theorem projected2CNF_majority {α β : Type} (cs : List (Clause (Sum α β)))
    (x₁ x₂ x₃ : α → Bool)
    (h₁ : projected2CNF cs x₁)
    (h₂ : projected2CNF cs x₂)
    (h₃ : projected2CNF cs x₃) :
    projected2CNF cs (pwMajority x₁ x₂ x₃) := by
  rcases h₁ with ⟨y₁, hy₁⟩
  rcases h₂ with ⟨y₂, hy₂⟩
  rcases h₃ with ⟨y₃, hy₃⟩
  refine ⟨pwMajority y₁ y₂ y₃, ?_⟩
  rw [combine_majority]
  exact cnf_majority cs (combine x₁ y₁) (combine x₂ y₂) (combine x₃ y₃)
    hy₁ hy₂ hy₃

def oneHot (k : Fin 3) (i : Fin 3) : Bool := decide (i = k)
def zero : Fin 3 → Bool := fun _ => false

def parity3 (x : Fin 3 → Bool) : Bool :=
  Bool.xor (Bool.xor (x 0) (x 1)) (x 2)

theorem oneHot_parity (k : Fin 3) : parity3 (oneHot k) = true := by
  fin_cases k <;> decide

theorem hot_majority_zero :
    pwMajority (oneHot 0) (oneHot 1) (oneHot 2) = zero := by
  funext i
  fin_cases i <;> decide

theorem parity3_not_projected2CNF {β : Type}
    (cs : List (Clause (Sum (Fin 3) β))) :
    ¬ ∀ x : Fin 3 → Bool, projected2CNF cs x ↔ parity3 x = true := by
  intro heq
  have h0 : projected2CNF cs (oneHot 0) := (heq _).mpr (oneHot_parity 0)
  have h1 : projected2CNF cs (oneHot 1) := (heq _).mpr (oneHot_parity 1)
  have h2 : projected2CNF cs (oneHot 2) := (heq _).mpr (oneHot_parity 2)
  have hproj := projected2CNF_majority cs (oneHot 0) (oneHot 1)
    (oneHot 2) h0 h1 h2
  rw [hot_majority_zero] at hproj
  have hpar : parity3 zero = true := (heq _).mp hproj
  have hnot : parity3 zero = false := by decide
  cases hnot.symm.trans hpar

end PvsNP.Projection
