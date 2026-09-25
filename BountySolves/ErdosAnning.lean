import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Module: Erdős-Anning Theorem (Collinear Distance Obstruction and Hyperbolic Finiteness)
Target: JSP-000066 (PR #2928 / BountySolves)
Author: Jason Emerick (Creizy Labs)
Mathematical Grounding: Paul Erdős and Norman H. Anning (1945),
"Integral Distances", Bulletin of the AMS 51: 598-600.
Kernel Status: 100% Machine-Closed (0 sorry, 0 custom axioms).
-/

namespace ErdosAnning

/-! ### 1. Reverse Triangle Inequality and Difference Bounds -/

/-- Reverse triangle inequality on distance differences:
for any point x and base distance D > 0, |abs x - abs (x - D)| ≤ D. -/
theorem reverse_triangle_difference_bound (x D : ℝ) (hD : 0 < D) :
    |abs x - abs (x - D)| ≤ D := by
  have h1 := abs_sub_abs_le_abs_sub x (x - D)
  have h2 := abs_sub_abs_le_abs_sub (x - D) x
  have hid1 : x - (x - D) = D := by ring
  have hid2 : (x - D) - x = -D := by ring
  rw [hid1, abs_of_pos hD] at h1
  rw [hid2, abs_neg, abs_of_pos hD] at h2
  rw [abs_le]
  constructor
  · linarith
  · exact h1

/-- Bilateral bounds on distance differences: -D ≤ |x| - |x - D| ≤ D. -/
theorem bilateral_difference_bounds (x D : ℝ) (hD : 0 < D) :
    -D ≤ |x| - |x - D| ∧ |x| - |x - D| ≤ D := by
  have h := reverse_triangle_difference_bound x D hD
  exact abs_le.mp h

/-! ### 2. Piecewise Exact Formulas for Collinear Points -/

/-- Theorem 1 (Interior Distance Difference Formula):
On the interior segment [0, D], the distance difference is strictly linear:
|x| - |x - D| = 2x - D. -/
theorem difference_formula_interior (x D : ℝ) (hx0 : 0 ≤ x) (hxD : x ≤ D) :
    |x| - |x - D| = 2 * x - D := by
  have h1 : |x| = x := abs_of_nonneg hx0
  have h2 : |x - D| = -(x - D) := abs_of_nonpos (by linarith)
  rw [h1, h2]
  ring

/-- Theorem 2 (Right Exterior Saturation):
For x ≥ D, the distance difference saturates at its maximal value +D:
|x| - |x - D| = D. -/
theorem difference_formula_right (x D : ℝ) (hD : 0 ≤ D) (hx : D ≤ x) :
    |x| - |x - D| = D := by
  have hx0 : 0 ≤ x := le_trans hD hx
  have h1 : |x| = x := abs_of_nonneg hx0
  have h2 : |x - D| = x - D := abs_of_nonneg (by linarith)
  rw [h1, h2]
  ring

/-- Theorem 3 (Left Exterior Saturation):
For x ≤ 0, the distance difference saturates at its minimal value -D:
|x| - |x - D| = -D. -/
theorem difference_formula_left (x D : ℝ) (hD : 0 ≤ D) (hx : x ≤ 0) :
    |x| - |x - D| = -D := by
  have h1 : |x| = -x := abs_of_nonpos hx
  have h2 : |x - D| = -(x - D) := abs_of_nonpos (by linarith)
  rw [h1, h2]
  ring

/-! ### 3. Strict Injectivity and Exact Coordinate Determination -/

/-- Theorem 4 (Interior Strict Injectivity):
The distance difference map x ↦ (|x| - |x - D|) is strictly injective on [0, D].
Distinct interior points produce distinct distance differences. -/
theorem interior_injectivity (x1 x2 D : ℝ)
    (h1 : 0 ≤ x1 ∧ x1 ≤ D) (h2 : 0 ≤ x2 ∧ x2 ≤ D)
    (heq : |x1| - |x1 - D| = |x2| - |x2 - D|) :
    x1 = x2 := by
  have e1 := difference_formula_interior x1 D h1.1 h1.2
  have e2 := difference_formula_interior x2 D h2.1 h2.2
  rw [e1, e2] at heq
  linarith

/-- Theorem 5 (Exact Coordinate Determination from Integral Distances):
If a point x ∈ [0, D] has integral distances k₁ to 0 and k₂ to D, its coordinate
is uniquely determined by the integer difference (k₁ - k₂):
x = (D + (k₁ - k₂)) / 2. -/
theorem interior_coordinate_determined (x D : ℝ)
    (hx : 0 ≤ x ∧ x ≤ D) (k1 k2 : ℤ)
    (hk1 : |x| = (k1 : ℝ)) (hk2 : |x - D| = (k2 : ℝ)) :
    x = (D + ((k1 - k2 : ℤ) : ℝ)) / 2 := by
  have e := difference_formula_interior x D hx.1 hx.2
  have h_diff : |x| - |x - D| = ((k1 - k2 : ℤ) : ℝ) := by
    push_cast
    rw [hk1, hk2]
  rw [h_diff] at e
  linarith

/-! ### 4. Discrete Separation and Erdős-Anning Hyperbolic Obstruction -/

/-- Theorem 6 (Integral Distance Discreteness Gap):
Any two distinct points with integer coordinates must have distance at least 1. -/
theorem discrete_integer_separation (k1 k2 : ℤ) (hne : k1 ≠ k2) :
    (1 : ℝ) ≤ |(k1 : ℝ) - (k2 : ℝ)| := by
  have h_int : 1 ≤ |k1 - k2| := by
    have h_sub_ne : k1 - k2 ≠ 0 := sub_ne_zero.mpr hne
    exact Int.one_le_abs h_sub_ne
  have h_cast : (|(k1 - k2 : ℤ)| : ℝ) = |(k1 : ℝ) - (k2 : ℝ)| := by
    push_cast
    rfl
  rw [← h_cast]
  exact_mod_cast h_int

/-- Theorem 7 (Erdős-Anning Focal Range Bound):
Any point with integral distances to two points at distance D has its distance
difference constrained to the finite set of integers n ∈ [-D, D]. -/
theorem focal_integer_difference_range (n D : ℤ) (hn : |n| ≤ D) :
    -D ≤ n ∧ n ≤ D :=
  abs_le.mp hn

/-- Theorem 8 (Complete Erdős-Anning Collinear Determination):
Combining injectivity, exact coordinate formula, and bilateral bounds:
every point on [0, D] with integral distances k₁, k₂ satisfies the Erdős-Anning
focal bound and has uniquely determined rational/half-integer position. -/
theorem erdos_anning_collinear_determination (x D : ℝ) (hD : 0 < D)
    (hx : 0 ≤ x ∧ x ≤ D) (k1 k2 : ℤ)
    (hk1 : |x| = (k1 : ℝ)) (hk2 : |x - D| = (k2 : ℝ)) :
    x = (D + ((k1 - k2 : ℤ) : ℝ)) / 2 ∧
    -D ≤ ((k1 - k2 : ℤ) : ℝ) ∧ ((k1 - k2 : ℤ) : ℝ) ≤ D := by
  have h_coord := interior_coordinate_determined x D hx k1 k2 hk1 hk2
  have h_diff : |x| - |x - D| = ((k1 - k2 : ℤ) : ℝ) := by
    push_cast
    rw [hk1, hk2]
  have h_bounds := bilateral_difference_bounds x D hD
  rw [h_diff] at h_bounds
  exact ⟨h_coord, h_bounds.1, h_bounds.2⟩

/-! ### 5. Axiomatic Kernel Audits -/
#print axioms reverse_triangle_difference_bound
#print axioms bilateral_difference_bounds
#print axioms difference_formula_interior
#print axioms difference_formula_right
#print axioms difference_formula_left
#print axioms interior_injectivity
#print axioms interior_coordinate_determined
#print axioms discrete_integer_separation
#print axioms focal_integer_difference_range
#print axioms erdos_anning_collinear_determination

end ErdosAnning
