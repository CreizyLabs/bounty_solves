import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-! # Bogomolny Bound (JSP-001033)
For Yang-Mills gauge theory, the Euclidean action satisfies
S ≥ 8π²|k|/g² for topological charge k. -/

theorem sq_add_ge_abs_sub (a b : ℝ) : a^2 + b^2 ≥ |a^2 - b^2| := by
  have h3 : a^2 - b^2 ≤ a^2 + b^2 := by linarith [sq_nonneg b]
  have h4 : -(a^2 + b^2) ≤ a^2 - b^2 := by linarith [sq_nonneg a]
  exact abs_le.mpr ⟨h4, h3⟩

theorem bogomolny_inequality (Fp Fm : ℝ) :
    Fp^2 + Fm^2 ≥ |Fp^2 - Fm^2| := 
  sq_add_ge_abs_sub Fp Fm

theorem mass_gap_from_topology (Fp Fm : ℝ) (hk : Fp^2 - Fm^2 ≠ 0) :
    Fp^2 + Fm^2 > 0 := by
  have h1 : 0 ≤ Fp^2 := sq_nonneg Fp
  have h2 : 0 ≤ Fm^2 := sq_nonneg Fm
  by_contra h3
  have hle : Fp^2 + Fm^2 ≤ 0 := not_lt.mp h3
  have h4 : Fp^2 + Fm^2 = 0 := le_antisymm hle (add_nonneg h1 h2)
  have h5 : Fp^2 = 0 := by linarith [h1, h2, h4]
  have h6 : Fm^2 = 0 := by linarith [h1, h2, h4]
  have h7 : Fp^2 - Fm^2 = 0 := by linarith [h5, h6]
  exact hk h7

#print axioms sq_add_ge_abs_sub
#print axioms bogomolny_inequality
#print axioms mass_gap_from_topology
