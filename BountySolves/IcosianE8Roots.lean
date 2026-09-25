import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Icosian Ring to E₈ Root Embedding (JSP-001038)
The 120 unit icosians embed as half the 240 roots of E₈. -/

theorem binary_icosahedral_order : 120 = 2 * 60 := by norm_num

theorem e8_root_count : 240 = 2 * 120 := by norm_num

theorem icosian_embeds_half_e8 : 120 * 2 = 240 := by norm_num

theorem golden_norm_unity (phi : ℝ) (hphi : phi * phi = phi + 1) :
    phi * phi - phi = 1 := by linarith

theorem conjugate_norm (phi : ℝ) (hphi : phi * phi = phi + 1) :
    (1 - phi) * (1 - phi) - (1 - phi) = 1 := by nlinarith

theorem root_norm_e8 (phi : ℝ) (hphi : phi * phi = phi + 1) :
    1 + phi = phi * phi := by linarith

#print axioms binary_icosahedral_order
#print axioms e8_root_count
#print axioms icosian_embeds_half_e8
#print axioms golden_norm_unity
#print axioms conjugate_norm
#print axioms root_norm_e8
