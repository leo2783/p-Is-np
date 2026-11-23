import Mathlib

/-! Deterministic decision-tree lower bounds for black-box Boolean OR. -/
namespace PvsNP.BlackBox

inductive Tree (n : ℕ) where
  | output : Bool → Tree n
  | ask : Fin n → Tree n → Tree n → Tree n

def eval {n : ℕ} : Tree n → (Fin n → Bool) → Bool
  | .output b, _ => b
  | .ask i onFalse onTrue, x =>
      if x i then eval onTrue x else eval onFalse x

def zeroQueries {n : ℕ} : Tree n → List (Fin n)
  | .output _ => []
  | .ask i onFalse _ => i :: zeroQueries onFalse

def height {n : ℕ} : Tree n → ℕ
  | .output _ => 0
  | .ask _ onFalse onTrue => Nat.succ (max (height onFalse) (height onTrue))

def zeroInput {n : ℕ} : Fin n → Bool := fun _ => false
def spike {n : ℕ} (k : Fin n) (i : Fin n) : Bool := decide (i = k)
def SolvesOR {n : ℕ} (t : Tree n) : Prop :=
  ∀ x : Fin n → Bool, eval t x = true ↔ ∃ i : Fin n, x i = true

theorem eval_same_of_zero_queries {n : ℕ} :
    ∀ (t : Tree n) (x : Fin n → Bool),
      (∀ i, i ∈ zeroQueries t → x i = false) →
      eval t x = eval t zeroInput := by
  intro t
  induction t with
  | output b =>
      intro x hx
      rfl
  | ask i onFalse onTrue ihFalse ihTrue =>
      intro x hx
      have hi : x i = false := hx i (by simp [zeroQueries])
      have htail : ∀ j, j ∈ zeroQueries onFalse → x j = false := by
        intro j hj
        exact hx j (by simp [zeroQueries, hj])
      calc
        eval (Tree.ask i onFalse onTrue) x = eval onFalse x := by
          simp [eval, hi]
        _ = eval onFalse zeroInput := ihFalse x htail
        _ = eval (Tree.ask i onFalse onTrue) zeroInput := by
          simp [eval, zeroInput]

theorem every_index_queried {n : ℕ} (t : Tree n) (h : SolvesOR t)
    (k : Fin n) : k ∈ zeroQueries t := by
  by_contra hk
  have heq : eval t (spike k) = eval t zeroInput := by
    apply eval_same_of_zero_queries
    intro i hi
    have hne : i ≠ k := by
      intro e
      apply hk
      exact e ▸ hi
    simp [spike, hne]
  have hzero : eval t zeroInput = false := by
    cases hv : eval t zeroInput with
    | false => rfl
    | true =>
        obtain ⟨i, hi⟩ := (h zeroInput).mp hv
        simp [zeroInput] at hi
  have hone : eval t (spike k) = true := by
    apply (h (spike k)).mpr
    exact ⟨k, by simp [spike]⟩
  have impossible : true = false := by
    calc
      true = eval t (spike k) := hone.symm
      _ = eval t zeroInput := heq
      _ = false := hzero
  cases impossible

theorem query_count_lower_bound {n : ℕ} (t : Tree n) (h : SolvesOR t) :
    n ≤ (zeroQueries t).length := by
  classical
  have hsub : (Finset.univ : Finset (Fin n)) ⊆ (zeroQueries t).toFinset := by
    intro i _
    simpa using every_index_queried t h i
  calc
    n = (Finset.univ : Finset (Fin n)).card := by simp
    _ ≤ (zeroQueries t).toFinset.card := Finset.card_le_card hsub
    _ ≤ (zeroQueries t).length := List.toFinset_card_le (zeroQueries t)

theorem zero_queries_le_height {n : ℕ} (t : Tree n) :
    (zeroQueries t).length ≤ height t := by
  induction t with
  | output b => simp [zeroQueries, height]
  | ask i onFalse onTrue ihFalse ihTrue =>
      change Nat.succ (zeroQueries onFalse).length ≤
        Nat.succ (max (height onFalse) (height onTrue))
      exact Nat.succ_le_succ (le_trans ihFalse (le_max_left _ _))

theorem depth_lower_bound {n : ℕ} (t : Tree n) (h : SolvesOR t) :
    n ≤ height t := by
  exact le_trans (query_count_lower_bound t h) (zero_queries_le_height t)

theorem exponential_query_lower_bound (n : ℕ) (t : Tree (2 ^ n))
    (h : SolvesOR t) : 2 ^ n ≤ height t :=
  depth_lower_bound t h


/-! ## Matching upper bound for sequential OR, with exact optimal depth -/
def sequentialOr {n : ℕ} : List (Fin n) → Tree n
  | [] => .output false
  | i :: rest => .ask i (sequentialOr rest) (.output true)

theorem sequentialOr_correct_on_list {n : ℕ}
    (indices : List (Fin n)) (x : Fin n → Bool) :
    eval (sequentialOr indices) x = true ↔
      ∃ i ∈ indices, x i = true := by
  induction indices with
  | nil => simp [sequentialOr, eval]
  | cons i rest ih =>
      cases h : x i with
      | false => simp [sequentialOr, eval, h, ih]
      | true => simp [sequentialOr, eval, h]

theorem sequentialOr_solves (n : ℕ) :
    SolvesOR (sequentialOr (Finset.univ : Finset (Fin n)).toList) := by
  intro x
  rw [sequentialOr_correct_on_list]
  simp

theorem sequentialOr_height {n : ℕ} (indices : List (Fin n)) :
    height (sequentialOr indices) = indices.length := by
  induction indices with
  | nil => rfl
  | cons i rest ih => simp [sequentialOr, height, ih]

theorem deterministic_or_optimal (n : ℕ) :
    (∃ t : Tree n, SolvesOR t ∧ height t = n) ∧
    (∀ t : Tree n, SolvesOR t → n ≤ height t) := by
  constructor
  · refine ⟨sequentialOr (Finset.univ : Finset (Fin n)).toList,
      sequentialOr_solves n, ?_⟩
    simp [sequentialOr_height]
  · intro t ht
    exact depth_lower_bound t ht

theorem exponential_or_optimal (n : ℕ) :
    (∃ t : Tree (2 ^ n), SolvesOR t ∧ height t = 2 ^ n) ∧
    (∀ t : Tree (2 ^ n), SolvesOR t → 2 ^ n ≤ height t) :=
  deterministic_or_optimal (2 ^ n)


/-!
## General zero-input sensitivity lower bound

The OR lower bound is one instance of a more general theorem: if flipping
any one input bit at zero changes a function's answer, every correct
deterministic black-box decision tree has depth at least n.
-/
def ZeroInputSensitive {n : ℕ}
    (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ k : Fin n, f (spike k) ≠ f zeroInput

theorem full_zero_sensitivity_requires_linear_depth {n : ℕ}
    (f : (Fin n → Bool) → Bool)
    (hf : ZeroInputSensitive f)
    (t : Tree n)
    (hcorrect : ∀ x, eval t x = f x) :
    n ≤ height t := by
  have hqueries : ∀ k : Fin n, k ∈ zeroQueries t := by
    intro k
    by_contra hk
    have hsame : eval t (spike k) = eval t zeroInput := by
      apply eval_same_of_zero_queries
      intro i hi
      have hne : i ≠ k := by
        intro e
        apply hk
        exact e ▸ hi
      simp [spike, hne]
    apply hf k
    calc
      f (spike k) = eval t (spike k) := (hcorrect _).symm
      _ = eval t zeroInput := hsame
      _ = f zeroInput := hcorrect _
  classical
  have hsub : (Finset.univ : Finset (Fin n)) ⊆ (zeroQueries t).toFinset := by
    intro k _
    simpa using hqueries k
  calc
    n = (Finset.univ : Finset (Fin n)).card := by simp
    _ ≤ (zeroQueries t).toFinset.card := Finset.card_le_card hsub
    _ ≤ (zeroQueries t).length := List.toFinset_card_le (zeroQueries t)
    _ ≤ height t := zero_queries_le_height t

end PvsNP.BlackBox
