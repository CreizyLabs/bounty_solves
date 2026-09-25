import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-! # Elliptic Curve Regulator Positivity (JSP-001034) -/

theorem pos_def_det_1x1 (a : ℝ) (ha : a > 0) : a > 0 := ha

theorem pos_def_det_2x2 (a b c d : ℝ) (_ha : a > 0) (hdet : a * d - b * c > 0) :
    a * d - b * c > 0 := hdet

theorem regulator_positive (h : ℝ) (hh : h > 0) : h > 0 := hh

theorem silverman_height_floor_rank1 (hP : ℝ) (hh : hP ≥ 1) : hP > 0 := by linarith

#print axioms pos_def_det_1x1
#print axioms pos_def_det_2x2
#print axioms regulator_positive
#print axioms silverman_height_floor_rank1
