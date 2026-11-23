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
      simp [impose]
  | true =>
      have hstep : chooseBranch query phi i = impose phi i false := by
        simp [chooseBranch, hq]
      rw [hstep]
      simp [impose]

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
## Clause normalization for a 2026 subexponential 3-SAT interface

The 2026 IsKCNF interface requires clauses without duplicates.
Adding a unit clause may break this input invariant. The
existing Mathlib List.dedup theorem permits a semantic-preserving
normalization. The external subexponential theorem is not imported.
-/

def canonicalizeCNF {n : ℕ} (phi : CNF n) : CNF n := phi.dedup

theorem canonicalize_nodup {n : ℕ} (phi : CNF n) :
    (canonicalizeCNF phi).Nodup := by
  simpa only [canonicalizeCNF] using List.nodup_dedup phi

theorem canonicalize_eval_true_iff {n : ℕ}
    (phi : CNF n) (a : Fin n → Bool) :
    evalCNF (canonicalizeCNF phi) a = true ↔ evalCNF phi a = true := by
  simp only [evalCNF, List.all_eq_true]
  constructor
  · intro h c hc
    exact h c (by simpa only [canonicalizeCNF, List.mem_dedup] using hc)
  · intro h c hc
    exact h c (by simpa only [canonicalizeCNF, List.mem_dedup] using hc)

def imposeCanonical {n : ℕ}
    (phi : CNF n) (i : Fin n) (bit : Bool) : CNF n :=
  canonicalizeCNF (impose phi i bit)

theorem imposeCanonical_eval_true_iff {n : ℕ}
    (phi : CNF n) (i : Fin n) (bit : Bool) (a : Fin n → Bool) :
    evalCNF (imposeCanonical phi i bit) a = true ↔
      evalCNF phi a = true ∧ a i = bit := by
  exact (canonicalize_eval_true_iff (impose phi i bit) a).trans
    (evalCNF_impose_iff phi i bit a)

theorem imposeCanonical_nodup {n : ℕ}
    (phi : CNF n) (i : Fin n) (bit : Bool) :
    (imposeCanonical phi i bit).Nodup :=
  canonicalize_nodup (impose phi i bit)

theorem imposeCanonical_preserves_width {n k : ℕ}
    (phi : CNF n) (i : Fin n) (bit : Bool)
    (hk : 1 ≤ k)
    (hwidth : ∀ c, c ∈ phi → c.length ≤ k) :
    (∀ c, c ∈ imposeCanonical phi i bit → c.length ≤ k) ∧
      (imposeCanonical phi i bit).Nodup := by
  constructor
  · intro c hc
    have hmem : c ∈ impose phi i bit := by
      simpa only [imposeCanonical, canonicalizeCNF, List.mem_dedup] using hc
    have hcase : c = [(i, bit)] ∨ c ∈ phi := by
      simpa [impose] using hmem
    rcases hcase with rfl | h
    · simpa using hk
    · exact hwidth c h
  · exact imposeCanonical_nodup phi i bit

theorem raw_impose_can_duplicate :
    ¬ (impose ([[(0, true)]] : CNF 1) (0 : Fin 1) true).Nodup := by
  decide


/-!
## Valid-input decision-oracle reduction

The 2026 SAT interface accepts only formulas with bounded clause width
and no duplicate clauses. The abstract decision oracle below is required
to be correct only on this class of inputs. This theorem closes a
precondition gap in an otherwise standard search-to-decision reduction.
-/

def WidthNodup {n : ℕ} (k : ℕ) (phi : CNF n) : Prop :=
  (∀ c, c ∈ phi → c.length ≤ k) ∧ phi.Nodup

theorem imposeCanonical_widthNodup {n k : ℕ}
    (phi : CNF n) (i : Fin n) (bit : Bool)
    (hk : 1 ≤ k) (hphi : WidthNodup k phi) :
    WidthNodup k (imposeCanonical phi i bit) :=
  imposeCanonical_preserves_width phi i bit hk hphi.1

theorem canonicalize_satisfiable_iff {n : ℕ} (phi : CNF n) :
    Satisfiable (canonicalizeCNF phi) ↔ Satisfiable phi := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, (canonicalize_eval_true_iff phi a).mp ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, (canonicalize_eval_true_iff phi a).mpr ha⟩

theorem canonical_sat_split {n : ℕ} (phi : CNF n) (i : Fin n) :
    Satisfiable phi ↔
      Satisfiable (imposeCanonical phi i false) ∨
      Satisfiable (imposeCanonical phi i true) := by
  constructor
  · intro hsat
    rcases (sat_split phi i).mp hsat with hf | ht
    · left
      exact (canonicalize_satisfiable_iff (impose phi i false)).mpr hf
    · right
      exact (canonicalize_satisfiable_iff (impose phi i true)).mpr ht
  · intro h
    apply (sat_split phi i).mpr
    rcases h with hf | ht
    · left
      exact (canonicalize_satisfiable_iff (impose phi i false)).mp hf
    · right
      exact (canonicalize_satisfiable_iff (impose phi i true)).mp ht

def chooseCanonicalBranch {n : ℕ}
    (query : CNF n → Bool) (phi : CNF n) (i : Fin n) : CNF n :=
  if query (imposeCanonical phi i false) then
    imposeCanonical phi i false
  else
    imposeCanonical phi i true

theorem chooseCanonicalBranch_widthNodup {n k : ℕ}
    (query : CNF n → Bool) (phi : CNF n) (i : Fin n)
    (hk : 1 ≤ k) (hphi : WidthNodup k phi) :
    WidthNodup k (chooseCanonicalBranch query phi i) := by
  unfold chooseCanonicalBranch
  cases hq : query (imposeCanonical phi i false) with
  | false =>
      simpa [hq] using imposeCanonical_widthNodup phi i true hk hphi
  | true =>
      simpa [hq] using imposeCanonical_widthNodup phi i false hk hphi

theorem chooseCanonicalBranch_sat {n k : ℕ}
    (query : CNF n → Bool)
    (hquery : ∀ phi, WidthNodup k phi →
      (query phi = true ↔ Satisfiable phi))
    (phi : CNF n) (i : Fin n)
    (hk : 1 ≤ k) (hphi : WidthNodup k phi)
    (hsat : Satisfiable phi) :
    Satisfiable (chooseCanonicalBranch query phi i) := by
  have hsplit := (canonical_sat_split phi i).mp hsat
  have hvalid : WidthNodup k (imposeCanonical phi i false) :=
    imposeCanonical_widthNodup phi i false hk hphi
  unfold chooseCanonicalBranch
  cases hq : query (imposeCanonical phi i false) with
  | true =>
      have hf : Satisfiable (imposeCanonical phi i false) :=
        (hquery _ hvalid).mp hq
      simpa [hq] using hf
  | false =>
      have hn : ¬ Satisfiable (imposeCanonical phi i false) := by
        intro hf
        have hyes : query (imposeCanonical phi i false) = true :=
          (hquery _ hvalid).mpr hf
        rw [hq] at hyes
        cases hyes
      have ht : Satisfiable (imposeCanonical phi i true) :=
        hsplit.resolve_left hn
      simpa [hq] using ht


/-!
## Fully restricted valid-input self-reduction

The recursive algorithm queries only the bounded-width, duplicate-free
CNF domain. It needs exactly one decision-oracle call per fixed variable,
and satisfying assignments of the final formula agree on all fixed bits.
-/

def canonicalRun {n : ℕ} (query : CNF n → Bool) :
    CNF n → List (Fin n) → CNF n × ℕ
  | phi, [] => (phi, 0)
  | phi, i :: rest =>
      let result := canonicalRun query (chooseCanonicalBranch query phi i) rest
      (result.1, result.2 + 1)

theorem canonicalRun_valid {n k : ℕ}
    (query : CNF n → Bool) (hk : 1 ≤ k) :
    ∀ (indices : List (Fin n)) (phi : CNF n),
      WidthNodup k phi →
      WidthNodup k (canonicalRun query phi indices).1 := by
  intro indices
  induction indices with
  | nil =>
      intro phi h
      simpa [canonicalRun] using h
  | cons i rest ih =>
      intro phi h
      have hnext := chooseCanonicalBranch_widthNodup query phi i hk h
      simpa [canonicalRun] using ih (chooseCanonicalBranch query phi i) hnext

theorem canonicalRun_sat {n k : ℕ}
    (query : CNF n → Bool)
    (hquery : ∀ phi, WidthNodup k phi →
      (query phi = true ↔ Satisfiable phi))
    (hk : 1 ≤ k) :
    ∀ (indices : List (Fin n)) (phi : CNF n),
      WidthNodup k phi → Satisfiable phi →
      Satisfiable (canonicalRun query phi indices).1 := by
  intro indices
  induction indices with
  | nil =>
      intro phi _ hsat
      simpa [canonicalRun] using hsat
  | cons i rest ih =>
      intro phi hvalid hsat
      have hnextValid := chooseCanonicalBranch_widthNodup query phi i hk hvalid
      have hnextSat :=
        chooseCanonicalBranch_sat query hquery phi i hk hvalid hsat
      simpa [canonicalRun] using
        ih (chooseCanonicalBranch query phi i) hnextValid hnextSat

theorem canonicalRun_calls {n : ℕ} (query : CNF n → Bool) :
    ∀ (indices : List (Fin n)) (phi : CNF n),
      (canonicalRun query phi indices).2 = indices.length := by
  intro indices
  induction indices with
  | nil =>
      intro phi
      rfl
  | cons i rest ih =>
      intro phi
      calc
        (canonicalRun query phi (i :: rest)).2 =
            (canonicalRun query (chooseCanonicalBranch query phi i) rest).2 + 1 := by
              simp [canonicalRun]
        _ = rest.length + 1 := by rw [ih]
        _ = (i :: rest).length := by simp

theorem canonicalBranch_entails {n : ℕ} (query : CNF n → Bool)
    (phi : CNF n) (i : Fin n) (a : Fin n → Bool)
    (ha : evalCNF (chooseCanonicalBranch query phi i) a = true) :
    evalCNF phi a = true := by
  cases hq : query (imposeCanonical phi i false) with
  | false =>
      have h : evalCNF (imposeCanonical phi i true) a = true := by
        simpa [chooseCanonicalBranch, hq] using ha
      exact ((imposeCanonical_eval_true_iff phi i true a).mp h).1
  | true =>
      have h : evalCNF (imposeCanonical phi i false) a = true := by
        simpa [chooseCanonicalBranch, hq] using ha
      exact ((imposeCanonical_eval_true_iff phi i false a).mp h).1

theorem canonicalBranch_agreement {n : ℕ} (query : CNF n → Bool)
    (phi : CNF n) (i : Fin n) (a b : Fin n → Bool)
    (ha : evalCNF (chooseCanonicalBranch query phi i) a = true)
    (hb : evalCNF (chooseCanonicalBranch query phi i) b = true) :
    a i = b i := by
  cases hq : query (imposeCanonical phi i false) with
  | false =>
      have ha' : evalCNF (imposeCanonical phi i true) a = true := by
        simpa [chooseCanonicalBranch, hq] using ha
      have hb' : evalCNF (imposeCanonical phi i true) b = true := by
        simpa [chooseCanonicalBranch, hq] using hb
      exact ((imposeCanonical_eval_true_iff phi i true a).mp ha').2.trans
        (((imposeCanonical_eval_true_iff phi i true b).mp hb').2).symm
  | true =>
      have ha' : evalCNF (imposeCanonical phi i false) a = true := by
        simpa [chooseCanonicalBranch, hq] using ha
      have hb' : evalCNF (imposeCanonical phi i false) b = true := by
        simpa [chooseCanonicalBranch, hq] using hb
      exact ((imposeCanonical_eval_true_iff phi i false a).mp ha').2.trans
        (((imposeCanonical_eval_true_iff phi i false b).mp hb').2).symm

theorem canonicalRun_entails {n : ℕ} (query : CNF n → Bool) :
    ∀ (indices : List (Fin n)) (phi : CNF n) (a : Fin n → Bool),
      evalCNF (canonicalRun query phi indices).1 a = true →
      evalCNF phi a = true := by
  intro indices
  induction indices with
  | nil =>
      intro phi a h
      simpa [canonicalRun] using h
  | cons i rest ih =>
      intro phi a h
      have hchild :
          evalCNF (chooseCanonicalBranch query phi i) a = true :=
        ih (chooseCanonicalBranch query phi i) a
          (by simpa [canonicalRun] using h)
      exact canonicalBranch_entails query phi i a hchild

theorem canonicalRun_agreement {n : ℕ} (query : CNF n → Bool) :
    ∀ (indices : List (Fin n)) (phi : CNF n) (a b : Fin n → Bool),
      evalCNF (canonicalRun query phi indices).1 a = true →
      evalCNF (canonicalRun query phi indices).1 b = true →
      ∀ i, i ∈ indices → a i = b i := by
  intro indices
  induction indices with
  | nil =>
      intro phi a b ha hb i hi
      simp at hi
  | cons j rest ih =>
      intro phi a b ha hb i hi
      have ha' :
          evalCNF (canonicalRun query (chooseCanonicalBranch query phi j) rest).1 a = true := by
        simpa [canonicalRun] using ha
      have hb' :
          evalCNF (canonicalRun query (chooseCanonicalBranch query phi j) rest).1 b = true := by
        simpa [canonicalRun] using hb
      rcases List.mem_cons.mp hi with hij | hrest
      · subst i
        have hfirstA : evalCNF (chooseCanonicalBranch query phi j) a = true :=
          canonicalRun_entails query rest (chooseCanonicalBranch query phi j) a ha'
        have hfirstB : evalCNF (chooseCanonicalBranch query phi j) b = true :=
          canonicalRun_entails query rest (chooseCanonicalBranch query phi j) b hb'
        exact canonicalBranch_agreement query phi j a b hfirstA hfirstB
      · exact ih (chooseCanonicalBranch query phi j) a b ha' hb' i hrest

theorem canonical_full_search {n k : ℕ}
    (query : CNF n → Bool)
    (hquery : ∀ phi, WidthNodup k phi →
      (query phi = true ↔ Satisfiable phi))
    (hk : 1 ≤ k) (phi : CNF n)
    (hvalid : WidthNodup k phi) (hsat : Satisfiable phi) :
    WidthNodup k
        (canonicalRun query phi (Finset.univ : Finset (Fin n)).toList).1 ∧
    Satisfiable
        (canonicalRun query phi (Finset.univ : Finset (Fin n)).toList).1 ∧
    (canonicalRun query phi (Finset.univ : Finset (Fin n)).toList).2 = n ∧
    ∀ a b : Fin n → Bool,
      evalCNF (canonicalRun query phi (Finset.univ : Finset (Fin n)).toList).1 a = true →
      evalCNF (canonicalRun query phi (Finset.univ : Finset (Fin n)).toList).1 b = true →
      ∀ i : Fin n, a i = b i := by
  let vars : List (Fin n) := (Finset.univ : Finset (Fin n)).toList
  have hlen : vars.length = n := by simp [vars]
  constructor
  · exact canonicalRun_valid query hk vars phi hvalid
  constructor
  · exact canonicalRun_sat query hquery hk vars phi hvalid hsat
  constructor
  · simpa [hlen] using canonicalRun_calls query vars phi
  · intro a b ha hb i
    exact canonicalRun_agreement query vars phi a b ha hb i (by simp [vars])


/-!
## Additional input hypotheses for the 2026 counting result

Besides width and clause uniqueness, that theorem assumes every
declared variable occurs and at least two clauses are present.
Their preservation follows from exact clause membership under
canonicalization, rather than enumerating satisfying assignments.
-/

def AllVariablesOccur {n : ℕ} (phi : CNF n) : Prop :=
  ∀ v : Fin n, ∃ clause : Clause n, clause ∈ phi ∧
    ∃ lit : Literal n, lit ∈ clause ∧ lit.1 = v

def HasTwoDistinctClauses {n : ℕ} (phi : CNF n) : Prop :=
  ∃ c d : Clause n, c ≠ d ∧ c ∈ phi ∧ d ∈ phi

theorem imposeCanonical_allVariablesOccur {n : ℕ}
    (phi : CNF n) (i : Fin n) (bit : Bool)
    (hall : AllVariablesOccur phi) :
    AllVariablesOccur (imposeCanonical phi i bit) := by
  intro v
  obtain ⟨clause, hclause, lit, hlit, hvar⟩ := hall v
  refine ⟨clause, ?_, lit, hlit, hvar⟩
  have hm : clause ∈ impose phi i bit := List.mem_cons_of_mem _ hclause
  simpa only [imposeCanonical, canonicalizeCNF, List.mem_dedup] using hm

theorem imposeCanonical_twoDistinct {n : ℕ}
    (phi : CNF n) (i : Fin n) (bit : Bool)
    (htwo : HasTwoDistinctClauses phi) :
    HasTwoDistinctClauses (imposeCanonical phi i bit) := by
  obtain ⟨c, d, hne, hc, hd⟩ := htwo
  refine ⟨c, d, hne, ?_, ?_⟩
  · have h : c ∈ impose phi i bit := List.mem_cons_of_mem _ hc
    simpa only [imposeCanonical, canonicalizeCNF, List.mem_dedup] using h
  · have h : d ∈ impose phi i bit := List.mem_cons_of_mem _ hd
    simpa only [imposeCanonical, canonicalizeCNF, List.mem_dedup] using h

theorem twoDistinct_minClauses {n : ℕ}
    (phi : CNF n) (htwo : HasTwoDistinctClauses phi) :
    2 ≤ phi.length := by
  obtain ⟨c, d, hne, hc, hd⟩ := htwo
  cases phi with
  | nil =>
      simp at hc
  | cons first rest =>
      cases rest with
      | nil =>
          have hec : c = first := by simpa using hc
          have hed : d = first := by simpa using hd
          exact False.elim (hne (hec.trans hed.symm))
      | cons second tail =>
          simp

theorem canonicalBranch_allVariablesOccur {n : ℕ}
    (query : CNF n → Bool) (phi : CNF n) (i : Fin n)
    (hall : AllVariablesOccur phi) :
    AllVariablesOccur (chooseCanonicalBranch query phi i) := by
  cases hq : query (imposeCanonical phi i false) with
  | false =>
      simpa [chooseCanonicalBranch, hq] using
        imposeCanonical_allVariablesOccur phi i true hall
  | true =>
      simpa [chooseCanonicalBranch, hq] using
        imposeCanonical_allVariablesOccur phi i false hall

theorem canonicalBranch_twoDistinct {n : ℕ}
    (query : CNF n → Bool) (phi : CNF n) (i : Fin n)
    (htwo : HasTwoDistinctClauses phi) :
    HasTwoDistinctClauses (chooseCanonicalBranch query phi i) := by
  cases hq : query (imposeCanonical phi i false) with
  | false =>
      simpa [chooseCanonicalBranch, hq] using
        imposeCanonical_twoDistinct phi i true htwo
  | true =>
      simpa [chooseCanonicalBranch, hq] using
        imposeCanonical_twoDistinct phi i false htwo

theorem canonicalRun_allVariablesOccur {n : ℕ}
    (query : CNF n → Bool) :
    ∀ (indices : List (Fin n)) (phi : CNF n),
      AllVariablesOccur phi →
      AllVariablesOccur (canonicalRun query phi indices).1 := by
  intro indices
  induction indices with
  | nil =>
      intro phi h
      simpa [canonicalRun] using h
  | cons i rest ih =>
      intro phi h
      have hnext := canonicalBranch_allVariablesOccur query phi i h
      simpa [canonicalRun] using ih (chooseCanonicalBranch query phi i) hnext

theorem canonicalRun_twoDistinct {n : ℕ}
    (query : CNF n → Bool) :
    ∀ (indices : List (Fin n)) (phi : CNF n),
      HasTwoDistinctClauses phi →
      HasTwoDistinctClauses (canonicalRun query phi indices).1 := by
  intro indices
  induction indices with
  | nil =>
      intro phi h
      simpa [canonicalRun] using h
  | cons i rest ih =>
      intro phi h
      have hnext := canonicalBranch_twoDistinct query phi i h
      simpa [canonicalRun] using ih (chooseCanonicalBranch query phi i) hnext

theorem canonicalRun_paper_preconditions {n k : ℕ}
    (query : CNF n → Bool) (phi : CNF n)
    (indices : List (Fin n))
    (hk : 1 ≤ k) (hvalid : WidthNodup k phi)
    (hall : AllVariablesOccur phi)
    (htwo : HasTwoDistinctClauses phi) :
    WidthNodup k (canonicalRun query phi indices).1 ∧
    AllVariablesOccur (canonicalRun query phi indices).1 ∧
    2 ≤ (canonicalRun query phi indices).1.length := by
  constructor
  · exact canonicalRun_valid query hk indices phi hvalid
  constructor
  · exact canonicalRun_allVariablesOccur query indices phi hall
  · exact twoDistinct_minClauses (canonicalRun query phi indices).1
      (canonicalRun_twoDistinct query indices phi htwo)

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
  IO.println "seed\tmask\tvariable\tbit\tcnf\tbefore\tafter\tcanonicalAfter\tcanonicalCount"
  for seed in List.range 96 do
    let phi := fixtureFormula seed
    let encoded := encodeFixtureFormula phi
    for mask in List.range 16 do
      let assignment := fixtureAssignment mask
      for column in List.range 4 do
        let i := fixtureIndex column
        for bit in ([false, true] : List Bool) do
          let before := evalCNF phi assignment
          let after := evalCNF (impose phi i bit) assignment
          let canonical := imposeCanonical phi i bit
          let canonicalAfter := evalCNF canonical assignment
          let canonicalCount := canonical.length
          IO.println s!"{seed}\t{mask}\t{column}\t{bit}\t{encoded}\t{before}\t{after}\t{canonicalAfter}\t{canonicalCount}"

end PvsNP.UnitRestriction

-- Exported only when invoked with 'lean --run'.
def main : IO Unit := PvsNP.UnitRestriction.emitFixtures
