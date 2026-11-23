import NPComplete

/-!
# P versus NP using actual Turing-machine complexity definitions

Here P/NP, NP membership of SAT and Cook-Levin are imported as
proved theorems from starpos/lean-np-complete v0.5.0, rather than
postulated as abstract assumptions.
-/

namespace PvsNP.FormalClasses

open NPComplete.CookLevin

theorem sat_in_P_iff_P_eq_NP :
    InP encodeCNF SAT ↔ PeqNP := by
  constructor
  · exact sat_InP_implies_PeqNP
  · intro h
    exact h encodeCNF SAT sat_inNP

theorem sat_not_in_P_iff_P_ne_NP :
    (¬ InP encodeCNF SAT) ↔ PneNP := by
  constructor
  · intro hnot hpeq
    exact hnot (sat_in_P_iff_P_eq_NP.mpr hpeq)
  · intro hpne hsat
    exact hpne (sat_in_P_iff_P_eq_NP.mp hsat)

end PvsNP.FormalClasses
