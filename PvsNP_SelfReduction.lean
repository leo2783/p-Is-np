import Mathlib

/-!
# Constructive search-to-decision reduction for Boolean witnesses

Given a correct decision procedure for the existence of a completion
of a partial Boolean assignment, greedily fix each next bit. The
algorithm makes exactly n oracle calls to recover a length-n witness.

This theorem does not assume that the oracle is polynomial-time;
its correctness is an explicit hypothesis. The result is the
combinatorial core of SAT self-reducibility, and does not settle P vs NP.
-/

namespace PvsNP.SelfReduction

def HasCompletion (accepts : List Bool → Prop)
    (prefix : List Bool) (remaining : ℕ) : Prop :=
  ∃ suffix : List Bool, suffix.length = remaining ∧ accepts (prefix ++ suffix)

theorem completion_succ_iff
    (accepts : List Bool → Prop) (prefix : List Bool) (n : ℕ) :
    HasCompletion accepts prefix (n + 1) ↔
      HasCompletion accepts (prefix ++ [false]) n ∨
      HasCompletion accepts (prefix ++ [true]) n := by
  constructor
  · rintro ⟨suffix, hlen, haccept⟩
    cases suffix with
    | nil =>
        simp at hlen
    | cons b tail =>
        have htail : tail.length = n := by
          simp at hlen
          omega
        cases b with
        | false =>
            left
            refine ⟨tail, htail, ?_⟩
            simpa [List.append_assoc] using haccept
        | true =>
            right
            refine ⟨tail, htail, ?_⟩
            simpa [List.append_assoc] using haccept
  · rintro (⟨tail, hlen, haccept⟩ | ⟨tail, hlen, haccept⟩)
    · refine ⟨false :: tail, by simp [hlen], ?_⟩
      simpa [List.append_assoc] using haccept
    · refine ⟨true :: tail, by simp [hlen], ?_⟩
      simpa [List.append_assoc] using haccept

/-!
Each recursive level tests one possible extension (false), and
chooses true only if that test fails. The second component counts
oracle invocations, independently of the oracle's implementation.
-/
def greedyWithCost (query : List Bool → ℕ → Bool) :
    List Bool → ℕ → List Bool × ℕ
  | prefix, 0 => (prefix, 0)
  | prefix, n + 1 =>
      let result :=
        if query (prefix ++ [false]) n then
          greedyWithCost query (prefix ++ [false]) n
        else
          greedyWithCost query (prefix ++ [true]) n
      (result.1, result.2 + 1)

theorem greedy_cost (query : List Bool → ℕ → Bool) :
    ∀ n : ℕ, ∀ prefix : List Bool,
      (greedyWithCost query prefix n).2 = n := by
  intro n
  induction n with
  | zero =>
      intro prefix
      rfl
  | succ n ih =>
      intro prefix
      cases hq : query (prefix ++ [false]) n with
      | false =>
          calc
            (greedyWithCost query prefix (n + 1)).2 =
                (greedyWithCost query (prefix ++ [true]) n).2 + 1 := by
                  simp [greedyWithCost, hq]
            _ = n + 1 := by rw [ih]
      | true =>
          calc
            (greedyWithCost query prefix (n + 1)).2 =
                (greedyWithCost query (prefix ++ [false]) n).2 + 1 := by
                  simp [greedyWithCost, hq]
            _ = n + 1 := by rw [ih]

theorem greedy_length (query : List Bool → ℕ → Bool) :
    ∀ n : ℕ, ∀ prefix : List Bool,
      (greedyWithCost query prefix n).1.length = prefix.length + n := by
  intro n
  induction n with
  | zero =>
      intro prefix
      simp [greedyWithCost]
  | succ n ih =>
      intro prefix
      cases hq : query (prefix ++ [false]) n with
      | false =>
          calc
            (greedyWithCost query prefix (n + 1)).1.length =
                (greedyWithCost query (prefix ++ [true]) n).1.length := by
                  simp [greedyWithCost, hq]
            _ = (prefix ++ [true]).length + n := ih _
            _ = prefix.length + (n + 1) := by simp [List.length_append]; omega
      | true =>
          calc
            (greedyWithCost query prefix (n + 1)).1.length =
                (greedyWithCost query (prefix ++ [false]) n).1.length := by
                  simp [greedyWithCost, hq]
            _ = (prefix ++ [false]).length + n := ih _
            _ = prefix.length + (n + 1) := by simp [List.length_append]; omega

theorem greedy_correct
    (accepts : List Bool → Prop) (query : List Bool → ℕ → Bool)
    (hquery : ∀ prefix n,
      query prefix n = true ↔ HasCompletion accepts prefix n) :
    ∀ n : ℕ, ∀ prefix : List Bool,
      HasCompletion accepts prefix n →
      accepts (greedyWithCost query prefix n).1 := by
  intro n
  induction n with
  | zero =>
      intro prefix hext
      obtain ⟨suffix, hlen, haccept⟩ := hext
      cases suffix with
      | nil =>
          simpa [greedyWithCost] using haccept
      | cons bit tail =>
          simp at hlen
  | succ n ih =>
      intro prefix hext
      have hsplit := (completion_succ_iff accepts prefix n).mp hext
      cases hq : query (prefix ++ [false]) n with
      | true =>
          have hleft : HasCompletion accepts (prefix ++ [false]) n :=
            (hquery _ _).mp hq
          simpa [greedyWithCost, hq] using ih (prefix ++ [false]) hleft
      | false =>
          have hnot : ¬ HasCompletion accepts (prefix ++ [false]) n := by
            intro hleft
            have hyes : query (prefix ++ [false]) n = true :=
              (hquery _ _).mpr hleft
            rw [hq] at hyes
            cases hyes
          have hright : HasCompletion accepts (prefix ++ [true]) n := by
            rcases hsplit with hleft | hright
            · exact False.elim (hnot hleft)
            · exact hright
          simpa [greedyWithCost, hq] using ih (prefix ++ [true]) hright

/-!
Search reduces to n sequential decision-oracle calls. For any
satisfiable n-bit instance the output has length n, is accepted,
and comes with an exact oracle-call count.
-/
theorem search_to_decision
    (accepts : List Bool → Prop) (query : List Bool → ℕ → Bool)
    (hquery : ∀ prefix n,
      query prefix n = true ↔ HasCompletion accepts prefix n)
    (n : ℕ)
    (hsat : ∃ witness : List Bool,
      witness.length = n ∧ accepts witness) :
    (greedyWithCost query [] n).1.length = n ∧
    accepts (greedyWithCost query [] n).1 ∧
    (greedyWithCost query [] n).2 = n := by
  have hstart : HasCompletion accepts [] n := by
    rcases hsat with ⟨witness, hlen, haccept⟩
    exact ⟨witness, hlen, by simpa using haccept⟩
  constructor
  · simpa using greedy_length query n []
  constructor
  · exact greedy_correct accepts query hquery n [] hstart
  · exact greedy_cost query n []

end PvsNP.SelfReduction
