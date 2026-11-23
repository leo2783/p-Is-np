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


/-!
## Non-enumerative SAT-oracle branch selection

A correct SAT decision oracle chooses one satisfiable unit restriction
at each step. The algorithm takes exactly one oracle answer per variable
and adds exactly one clause per step.
-/
def chooseBranch {n : ℕ} (query : CNF n → Bool)
    (phi : CNF n) (i : Fin n) : CNF n :=
  if query (impose phi i false) then
    impose phi i false
  else
    impose phi i true

theorem chooseBranch_sat {n : ℕ}
    (query : CNF n → Bool)
    (hquery : ∀ phi, query phi = true ↔ Satisfiable phi)
    (phi : CNF n) (i : Fin n) (hphi : Satisfiable phi) :
    Satisfiable (chooseBranch query phi i) := by
  have hsplit := (sat_split phi i).mp hphi
  cases hq : query (impose phi i false) with
  | true =>
      have hfalse : Satisfiable (impose phi i false) := (hquery _).mp hq
      simpa [chooseBranch, hq] using hfalse
  | false =>
      have hnot : ¬ Satisfiable (impose phi i false) := by
        intro hfalse
        have hyes : query (impose phi i false) = true := (hquery _).mpr hfalse
        rw [hq] at hyes
        cases hyes
      have htrue : Satisfiable (impose phi i true) := hsplit.resolve_left hnot
      simpa [chooseBranch, hq] using htrue

theorem chooseBranch_length {n : ℕ}
    (query : CNF n → Bool) (phi : CNF n) (i : Fin n) :
    (chooseBranch query phi i).length = phi.length + 1 := by
  cases hq : query (impose phi i false) with
  | false =>
      have hstep : chooseBranch query phi i = impose phi i true := by
        simp [chooseBranch, hq]
      rw [hstep]
      simp [impose, Nat.add_comm]
  | true =>
      have hstep : chooseBranch query phi i = impose phi i false := by
        simp [chooseBranch, hq]
      rw [hstep]
      simp [impose, Nat.add_comm]

def restrictWithCost {n : ℕ} (query : CNF n → Bool) :
    CNF n → List (Fin n) → CNF n × ℕ
  | phi, [] => (phi, 0)
  | phi, i :: rest =>
      let next := chooseBranch query phi i
      let result := restrictWithCost query next rest
      (result.1, result.2 + 1)

theorem restrictions_sat {n : ℕ}
    (query : CNF n → Bool)
    (hquery : ∀ phi, query phi = true ↔ Satisfiable phi) :
    ∀ (indices : List (Fin n)) (phi : CNF n),
      Satisfiable phi →
      Satisfiable (restrictWithCost query phi indices).1 := by
  intro indices
  induction indices with
  | nil =>
      intro phi h
      simpa [restrictWithCost] using h
  | cons i rest ih =>
      intro phi h
      have hnext := chooseBranch_sat query hquery phi i h
      simpa [restrictWithCost] using ih (chooseBranch query phi i) hnext

theorem restrictions_calls {n : ℕ}
    (query : CNF n → Bool) :
    ∀ (indices : List (Fin n)) (phi : CNF n),
      (restrictWithCost query phi indices).2 = indices.length := by
  intro indices
  induction indices with
  | nil =>
      intro phi
      rfl
  | cons i rest ih =>
      intro phi
      calc
        (restrictWithCost query phi (i :: rest)).2 =
            (restrictWithCost query (chooseBranch query phi i) rest).2 + 1 := by
              simp [restrictWithCost]
        _ = rest.length + 1 := by rw [ih]
        _ = (i :: rest).length := by simp

theorem restrictions_size {n : ℕ}
    (query : CNF n → Bool) :
    ∀ (indices : List (Fin n)) (phi : CNF n),
      (restrictWithCost query phi indices).1.length =
        phi.length + indices.length := by
  intro indices
  induction indices with
  | nil =>
      intro phi
      simp [restrictWithCost]
  | cons i rest ih =>
      intro phi
      calc
        (restrictWithCost query phi (i :: rest)).1.length =
            (restrictWithCost query (chooseBranch query phi i) rest).1.length := by
              simp [restrictWithCost]
        _ = (chooseBranch query phi i).length + rest.length := ih _
        _ = phi.length + (i :: rest).length := by
              rw [chooseBranch_length]
              simp
              omega

theorem restrict_all_variables {n : ℕ}
    (query : CNF n → Bool)
    (hquery : ∀ phi, query phi = true ↔ Satisfiable phi)
    (phi : CNF n) (hsat : Satisfiable phi) :
    Satisfiable
        (restrictWithCost query phi (Finset.univ : Finset (Fin n)).toList).1 ∧
    (restrictWithCost query phi (Finset.univ : Finset (Fin n)).toList).2 = n ∧
    (restrictWithCost query phi (Finset.univ : Finset (Fin n)).toList).1.length =
      phi.length + n := by
  let vars : List (Fin n) := (Finset.univ : Finset (Fin n)).toList
  have hlen : vars.length = n := by simp [vars]
  constructor
  · exact restrictions_sat query hquery vars phi hsat
  constructor
  · simpa [hlen] using restrictions_calls query vars phi
  · simpa [hlen] using restrictions_size query vars phi


/-!
## Differential fixtures from the formally specified CNF evaluator

The test generator is deterministic and parameterized by an input seed.
The correctness theorem \`evalCNF_impose_iff\` above is the specification;
the rows below expose actual Lean evaluator results for Rust differential
tests. Finite tests supplement, and do not replace, the theorem.
-/
private def fixtureIndex (k : Nat) : Fin 4 :=
  ⟨k % 4, Nat.mod_lt k (by decide)⟩

private def fixtureFormula (seed : Nat) : CNF 4 :=
  (List.range ((seed * 17 + 1) % 7)).map fun c =>
    (List.range ((seed + c * 3) % 5)).map fun j =>
      (fixtureIndex (seed * 13 + c * 5 + j * 7),
        (seed + 11 * c + 3 * j) % 2 == 0)

private def fixtureAssignment (mask : Nat) (i : Fin 4) : Bool :=
  mask / (2 ^ i.val) % 2 == 1

private def encodeFixtureLiteral (lit : Literal 4) : String :=
  let v := toString (lit.1.val + 1)
  if lit.2 then v else "-" ++ v

private def encodeFixtureClause (clause : Clause 4) : String :=
  match clause with
  | [] => "_"
  | _ => String.intercalate "," (clause.map encodeFixtureLiteral)

private def encodeFixtureFormula (phi : CNF 4) : String :=
  match phi with
  | [] => "~"
  | _ => String.intercalate ";" (phi.map encodeFixtureClause)

def emitFixtures : IO Unit := do
  IO.println "seed\tmask\tvariable\tbit\tcnf\tbefore\tafter"
  for seed in List.range 96 do
    let phi := fixtureFormula seed
    let encoded := encodeFixtureFormula phi
    for mask in List.range 16 do
      let assignment := fixtureAssignment mask
      for variable in List.range 4 do
        let i := fixtureIndex variable
        for bit in ([false, true] : List Bool) do
          let before := evalCNF phi assignment
          let after := evalCNF (impose phi i bit) assignment
          IO.println s!"{seed}\t{mask}\t{variable}\t{bit}\t{encoded}\t{before}\t{after}"

end PvsNP.UnitRestriction

-- Exported only when invoked with 'lean --run'.
def main : IO Unit := PvsNP.UnitRestriction.emitFixtures
