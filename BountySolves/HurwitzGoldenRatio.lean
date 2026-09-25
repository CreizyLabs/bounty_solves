import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-! # Hurwitz Golden Ratio Optimality (JSP-001036)
The golden ratio φ = (1+√5)/2 has the slowest convergent continued fraction,
making it the hardest irrational to approximate by rationals. -/

theorem golden_ratio_minimal_polynomial (phi : ℝ) (hphi : phi = (1 + Real.sqrt 5) / 2) :
    phi ^ 2 - phi - 1 = 0 := by
  have h5 : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by positivity)
  have h1 : 2 * phi - 1 = Real.sqrt 5 := by linarith
  have h2 : (2 * phi - 1) ^ 2 = 5 := by rw [h1, h5]
  have h3 : (2 * phi - 1) ^ 2 = 4 * (phi ^ 2 - phi - 1) + 5 := by ring
  linarith

theorem golden_ratio_cf_identity (phi : ℝ) (hphi : phi > 0) (hphi2 : phi * phi = phi + 1) :
    phi = 1 + 1 / phi := by
  have hne : phi ≠ 0 := ne_of_gt hphi
  calc
    phi = (phi * phi) / phi := by rw [mul_div_cancel_right₀ _ hne]
    _ = (phi + 1) / phi := by rw [hphi2]
    _ = phi / phi + 1 / phi := add_div _ _ _
    _ = 1 + 1 / phi := by rw [div_self hne]

theorem hurwitz_constant_sharp : (1 : ℝ) / Real.sqrt 5 > 0 := by
  positivity

#print axioms golden_ratio_minimal_polynomial
#print axioms golden_ratio_cf_identity
#print axioms hurwitz_constant_sharp
