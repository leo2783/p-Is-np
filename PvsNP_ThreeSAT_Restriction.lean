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

end PvsNP.NativeThreeSAT
