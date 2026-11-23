import NPComplete

/-!
# Unit restrictions for NPComplete's native 3-SAT syntax

A repeated-literal 3-clause acts as a unit constraint. The original
3-SAT formula is satisfiable precisely when either fixed-value branch
is satisfiable, and bounded instances stay bounded when the selected
variable is within the declared number of variables.

All statements use NPComplete.SAT.ThreeCNF and ThreeSAT directly.
-/

namespace PvsNP.NativeThreeSAT

open NPComplete.SAT

def unitLiteral (i : Nat) (bit : Bool) : Literal :=
  if bit then Literal.pos i else Literal.neg i

def unitClause (i : Nat) (bit : Bool) : ThreeClause :=
  { l1 := unitLiteral i bit
    l2 := unitLiteral i bit
    l3 := unitLiteral i bit }

def restrict (f : ThreeCNF) (i : Nat) (bit : Bool) : ThreeCNF :=
  { f with clauses := unitClause i bit :: f.clauses }

theorem unitClause_satisfied_iff
    (a : Literal.Assignment) (i : Nat) (bit : Bool) :
    (unitClause i bit).Satisfied a ↔ a i = bit := by
  cases bit <;> cases ha : a i <;>
    simp [unitClause, unitLiteral, ThreeClause.Satisfied, Literal.eval, ha]

theorem restrict_satisfied_iff
    (a : Literal.Assignment) (f : ThreeCNF) (i : Nat) (bit : Bool) :
    (restrict f i bit).Satisfied a ↔ f.Satisfied a ∧ a i = bit := by
  constructor
  · intro h
    constructor
    · intro c hc
      exact h c (List.mem_cons_of_mem _ hc)
    · apply (unitClause_satisfied_iff a i bit).mp
      exact h (unitClause i bit) (by simp [restrict])
  · rintro ⟨hf, hbit⟩
    intro c hc
    have hmem : c = unitClause i bit ∨ c ∈ f.clauses := by
      simpa [restrict] using hc
    rcases hmem with rfl | hc
    · exact (unitClause_satisfied_iff a i bit).mpr hbit
    · exact hf c hc

theorem threeSAT_restrict_iff (f : ThreeCNF) (i : Nat) (bit : Bool) :
    ThreeSAT (restrict f i bit) ↔
      ∃ a : Literal.Assignment, f.Satisfied a ∧ a i = bit := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, (restrict_satisfied_iff a f i bit).mp ha⟩
  · rintro ⟨a, hf, hi⟩
    exact ⟨a, (restrict_satisfied_iff a f i bit).mpr ⟨hf, hi⟩⟩

theorem threeSAT_split (f : ThreeCNF) (i : Nat) :
    ThreeSAT f ↔
      ThreeSAT (restrict f i false) ∨
      ThreeSAT (restrict f i true) := by
  constructor
  · rintro ⟨a, hf⟩
    cases hi : a i with
    | false =>
        left
        exact ⟨a, (restrict_satisfied_iff a f i false).mpr ⟨hf, hi⟩⟩
    | true =>
        right
        exact ⟨a, (restrict_satisfied_iff a f i true).mpr ⟨hf, hi⟩⟩
  · rintro (⟨a, ha⟩ | ⟨a, ha⟩)
    · exact ⟨a, ((restrict_satisfied_iff a f i false).mp ha).1⟩
    · exact ⟨a, ((restrict_satisfied_iff a f i true).mp ha).1⟩

theorem unitClause_var_of_mem (i : Nat) (bit : Bool)
    (l : Literal) (hl : l ∈ (unitClause i bit).literals) :
    l.var = i := by
  have h : l = unitLiteral i bit := by
    simpa [unitClause, ThreeClause.literals] using hl
  subst l
  cases bit <;> rfl

theorem restrict_bounded (f : ThreeCNF) (hf : f.Bounded)
    (i : Nat) (hi : i < f.numVars) (bit : Bool) :
    (restrict f i bit).Bounded := by
  intro c hc l hl
  have hmem : c = unitClause i bit ∨ c ∈ f.clauses := by
    simpa [restrict] using hc
  rcases hmem with rfl | hc
  · have hvar : l.var = i := unitClause_var_of_mem i bit l hl
    simpa [restrict, hvar] using hi
  · exact hf c hc l hl


/-!
## Greedy self-reduction on the native 3-SAT representation

One decision query selects a satisfiable Boolean branch. Repeating
this operation over all declared variables yields a satisfiable
restricted formula. Its satisfying assignments agree on the original
variable domain, and the query count and formula growth are linear.
No full assignment enumeration is involved.
-/

def branchBit (query : ThreeCNF → Bool) (f : ThreeCNF) (i : Nat) : Bool :=
  if query (restrict f i false) then false else true

def branchStep (query : ThreeCNF → Bool) (f : ThreeCNF) (i : Nat) : ThreeCNF :=
  restrict f i (branchBit query f i)

theorem branchStep_sat (query : ThreeCNF → Bool)
    (hquery : ∀ f, query f = true ↔ ThreeSAT f)
    (f : ThreeCNF) (i : Nat) (hsat : ThreeSAT f) :
    ThreeSAT (branchStep query f i) := by
  have hsplit := (threeSAT_split f i).mp hsat
  unfold branchStep branchBit
  cases hq : query (restrict f i false) with
  | false =>
      have hn : ¬ ThreeSAT (restrict f i false) := by
        intro hfalse
        have hyes : query (restrict f i false) = true := (hquery _).mpr hfalse
        rw [hq] at hyes
        cases hyes
      simpa [hq] using hsplit.resolve_left hn
  | true =>
      have hf : ThreeSAT (restrict f i false) := (hquery _).mp hq
      simpa [hq] using hf

theorem branchStep_bounded (query : ThreeCNF → Bool)
    (f : ThreeCNF) (hf : f.Bounded) (i : Nat) (hi : i < f.numVars) :
    (branchStep query f i).Bounded := by
  exact restrict_bounded f hf i hi (branchBit query f i)

theorem branchStep_numVars (query : ThreeCNF → Bool)
    (f : ThreeCNF) (i : Nat) :
    (branchStep query f i).numVars = f.numVars := rfl

theorem branchStep_clauses (query : ThreeCNF → Bool)
    (f : ThreeCNF) (i : Nat) :
    (branchStep query f i).clauses.length = f.clauses.length + 1 := by
  simp [branchStep, restrict]

theorem branchStep_entails (query : ThreeCNF → Bool)
    (f : ThreeCNF) (i : Nat) (a : Literal.Assignment)
    (h : (branchStep query f i).Satisfied a) : f.Satisfied a :=
  ((restrict_satisfied_iff a f i (branchBit query f i)).mp h).1

theorem branchStep_fixes (query : ThreeCNF → Bool)
    (f : ThreeCNF) (i : Nat) (a : Literal.Assignment)
    (h : (branchStep query f i).Satisfied a) :
    a i = branchBit query f i :=
  ((restrict_satisfied_iff a f i (branchBit query f i)).mp h).2

def refineWithCost (query : ThreeCNF → Bool) :
    ThreeCNF → List Nat → ThreeCNF × Nat
  | f, [] => (f, 0)
  | f, i :: rest =>
      let result := refineWithCost query (branchStep query f i) rest
      (result.1, result.2 + 1)

theorem refine_sat (query : ThreeCNF → Bool)
    (hquery : ∀ f, query f = true ↔ ThreeSAT f) :
    ∀ (indices : List Nat) (f : ThreeCNF),
      ThreeSAT f → ThreeSAT (refineWithCost query f indices).1 := by
  intro indices
  induction indices with
  | nil =>
      intro f hf
      simpa [refineWithCost] using hf
  | cons i rest ih =>
      intro f hf
      have hnext := branchStep_sat query hquery f i hf
      simpa [refineWithCost] using ih (branchStep query f i) hnext

theorem refine_calls (query : ThreeCNF → Bool) :
    ∀ (indices : List Nat) (f : ThreeCNF),
      (refineWithCost query f indices).2 = indices.length := by
  intro indices
  induction indices with
  | nil =>
      intro f
      rfl
  | cons i rest ih =>
      intro f
      calc
        (refineWithCost query f (i :: rest)).2 =
            (refineWithCost query (branchStep query f i) rest).2 + 1 := by
              simp [refineWithCost]
        _ = rest.length + 1 := by rw [ih]
        _ = (i :: rest).length := by simp

theorem refine_clauses (query : ThreeCNF → Bool) :
    ∀ (indices : List Nat) (f : ThreeCNF),
      (refineWithCost query f indices).1.clauses.length =
        f.clauses.length + indices.length := by
  intro indices
  induction indices with
  | nil =>
      intro f
      simp [refineWithCost]
  | cons i rest ih =>
      intro f
      calc
        (refineWithCost query f (i :: rest)).1.clauses.length =
            (refineWithCost query (branchStep query f i) rest).1.clauses.length := by
              simp [refineWithCost]
        _ = (branchStep query f i).clauses.length + rest.length := ih _
        _ = f.clauses.length + (i :: rest).length := by
              rw [branchStep_clauses]
              simp
              omega

theorem refine_entails (query : ThreeCNF → Bool) :
    ∀ (indices : List Nat) (f : ThreeCNF) (a : Literal.Assignment),
      (refineWithCost query f indices).1.Satisfied a → f.Satisfied a := by
  intro indices
  induction indices with
  | nil =>
      intro f a h
      simpa [refineWithCost] using h
  | cons i rest ih =>
      intro f a h
      have hchild : (branchStep query f i).Satisfied a :=
        ih (branchStep query f i) a (by simpa [refineWithCost] using h)
      exact branchStep_entails query f i a hchild

theorem refine_unique_indices (query : ThreeCNF → Bool) :
    ∀ (indices : List Nat) (f : ThreeCNF) (a b : Literal.Assignment),
      (refineWithCost query f indices).1.Satisfied a →
      (refineWithCost query f indices).1.Satisfied b →
      ∀ i, i ∈ indices → a i = b i := by
  intro indices
  induction indices with
  | nil =>
      intro f a b ha hb i hi
      simp at hi
  | cons j rest ih =>
      intro f a b ha hb i hi
      have ha' : (refineWithCost query (branchStep query f j) rest).1.Satisfied a := by
        simpa [refineWithCost] using ha
      have hb' : (refineWithCost query (branchStep query f j) rest).1.Satisfied b := by
        simpa [refineWithCost] using hb
      have hi' : i = j ∨ i ∈ rest := by simpa using hi
      rcases hi' with hij | hrest
      · subst i
        have hsa : (branchStep query f j).Satisfied a :=
          refine_entails query rest (branchStep query f j) a ha'
        have hsb : (branchStep query f j).Satisfied b :=
          refine_entails query rest (branchStep query f j) b hb'
        exact (branchStep_fixes query f j a hsa).trans
          (branchStep_fixes query f j b hsb).symm
      · exact ih (branchStep query f j) a b ha' hb' i hrest

theorem refine_bounded (query : ThreeCNF → Bool) :
    ∀ (indices : List Nat) (f : ThreeCNF),
      f.Bounded → (∀ i, i ∈ indices → i < f.numVars) →
      (refineWithCost query f indices).1.Bounded := by
  intro indices
  induction indices with
  | nil =>
      intro f hf _
      simpa [refineWithCost] using hf
  | cons i rest ih =>
      intro f hf hbound
      have hi : i < f.numVars := hbound i (by simp)
      have hstep : (branchStep query f i).Bounded :=
        branchStep_bounded query f hf i hi
      have hrest : ∀ j, j ∈ rest → j < (branchStep query f i).numVars := by
        intro j hj
        have hbefore : j < f.numVars := hbound j (by simp [hj])
        simpa [branchStep_numVars] using hbefore
      simpa [refineWithCost] using ih (branchStep query f i) hstep hrest

/-!
A complete pass through all declared variables adds exactly one
unit restriction per variable. All satisfying assignments of the
result agree on the original finite variable domain.
-/
theorem all_variables_fixed (query : ThreeCNF → Bool)
    (hquery : ∀ f, query f = true ↔ ThreeSAT f)
    (f : ThreeCNF) (hsat : ThreeSAT f) (hbounded : f.Bounded) :
    ThreeSAT (refineWithCost query f (List.range f.numVars)).1 ∧
    (refineWithCost query f (List.range f.numVars)).2 = f.numVars ∧
    (refineWithCost query f (List.range f.numVars)).1.clauses.length =
      f.clauses.length + f.numVars ∧
    (refineWithCost query f (List.range f.numVars)).1.Bounded ∧
    ∀ a b : Literal.Assignment,
      (refineWithCost query f (List.range f.numVars)).1.Satisfied a →
      (refineWithCost query f (List.range f.numVars)).1.Satisfied b →
      ∀ i, i < f.numVars → a i = b i := by
  have hlen : (List.range f.numVars).length = f.numVars := by simp
  constructor
  · exact refine_sat query hquery (List.range f.numVars) f hsat
  constructor
  · simpa [hlen] using refine_calls query (List.range f.numVars) f
  constructor
  · simpa [hlen] using refine_clauses query (List.range f.numVars) f
  constructor
  · apply refine_bounded query (List.range f.numVars) f hbounded
    intro i hi
    exact List.mem_range.mp hi
  · intro a b ha hb i hi
    exact refine_unique_indices query (List.range f.numVars) f a b ha hb i
      (List.mem_range.mpr hi)

end PvsNP.NativeThreeSAT
