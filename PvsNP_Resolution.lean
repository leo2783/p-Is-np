import Mathlib

/-!
# Soundness of propositional resolution

Resolution derives C ∨ D from (p ∨ C) and (¬p ∨ D).
We prove the soundness of the inference rule, then establish that
every clause in an inductive resolution derivation is entailed by
the initial clauses. A satisfiable CNF therefore has no
empty-clause resolution derivation.

These are general symbolic proofs; no truth-table enumeration is used.
-/

namespace PvsNP.Resolution

abbrev Literal (n : ℕ) := Fin n × Bool
abbrev Clause (n : ℕ) := List (Literal n)

def evalLiteral {n : ℕ} (lit : Literal n) (x : Fin n → Bool) : Bool :=
  if lit.2 then x lit.1 else !(x lit.1)

def evalClause {n : ℕ} (clause : Clause n) (x : Fin n → Bool) : Bool :=
  clause.any (fun lit => evalLiteral lit x)

theorem evalClause_append {n : ℕ}
    (left right : Clause n) (x : Fin n → Bool) :
    evalClause (left ++ right) x =
      (evalClause left x || evalClause right x) := by
  simp [evalClause, List.any_append]

theorem resolution_sound {n : ℕ}
    (i : Fin n) (left right : Clause n) (x : Fin n → Bool)
    (hpos : evalClause ((i, true) :: left) x = true)
    (hneg : evalClause ((i, false) :: right) x = true) :
    evalClause (left ++ right) x = true := by
  cases hx : x i with
  | false =>
      have hl : evalClause left x = true := by
        simpa [evalClause, evalLiteral, hx] using hpos
      rw [evalClause_append, hl]
      rfl
  | true =>
      have hr : evalClause right x = true := by
        simpa [evalClause, evalLiteral, hx] using hneg
      rw [evalClause_append, hr]
      simp

inductive Derives {n : ℕ} (premises : List (Clause n)) :
    Clause n → Prop where
  | initial {clause : Clause n} (hin : clause ∈ premises) :
      Derives premises clause
  | resolution (i : Fin n) (left right : Clause n)
      (hleft : Derives premises ((i, true) :: left))
      (hright : Derives premises ((i, false) :: right)) :
      Derives premises (left ++ right)

theorem derivation_sound {n : ℕ}
    (premises : List (Clause n)) (x : Fin n → Bool)
    (hinput : ∀ clause, clause ∈ premises → evalClause clause x = true)
    {clause : Clause n} (h : Derives premises clause) :
    evalClause clause x = true := by
  induction h with
  | initial hmem =>
      exact hinput _ hmem
  | resolution i left right hleft hright ihleft ihright =>
      exact resolution_sound i left right x ihleft ihright

theorem no_empty_refutation_of_satisfiable {n : ℕ}
    (premises : List (Clause n))
    (hSat : ∃ x : Fin n → Bool,
      ∀ clause, clause ∈ premises → evalClause clause x = true) :
    ¬ Derives premises [] := by
  intro hempty
  obtain ⟨x, hinput⟩ := hSat
  have heval : evalClause ([] : Clause n) x = true :=
    derivation_sound premises x hinput hempty
  simp [evalClause] at heval

end PvsNP.Resolution
