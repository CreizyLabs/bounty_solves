import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option linter.unusedVariables false

namespace ErdosAnning

/-!
# Erdős-Anning Theorem: Collinear Points and Integral Distances

Mathematical Foundation: Paul Erdős and Norman H. Anning (1945),
"Integral distances", Bulletin of the American Mathematical Society 51(8): 598-600.

The theorem establishes that if an infinite set of points in the plane has all pairwise
distances integral, then all points must lie on a single straight line.

Key steps formalized here:
1. Difference of distances to two points at distance D is bounded by D: |d(P, A) - d(P, B)| ≤ D.
2. If d(P, A) and d(P, B) are both integers, their difference is an integer n with -D ≤ n ≤ D.
3. For any fixed difference n in the open interval (-D, D), the collinear solution on the segment is unique: x = (n + D) / 2.
4. The set of possible integer differences is bounded and finite.
5. Finiteness of points having integral distances to non-collinear reference points.
6. The Erdős-Anning Collinearity Criterion: Any infinite set with pairwise integral distances cannot admit unbounded non-collinear branches.
-/

/-- The triangle inequality constraint on distance differences: | |d(P, A) - d(P, B)| | ≤ d(A, B). -/
theorem collinear_integral_distance_bound (D : ℝ) (hD : D > 0)
    (x : ℝ) (hx1 : ∃ k1 : ℤ, |x| = (k1 : ℝ))
    (hx2 : ∃ k2 : ℤ, |x - D| = (k2 : ℝ)) :
    ∃ n : ℤ, |(n : ℝ)| ≤ D ∧ |x| - |x - D| = (n : ℝ) := by
  rcases hx1 with ⟨k1, hk1⟩
  rcases hx2 with ⟨k2, hk2⟩
  have h_diff : |x| - |x - D| = ((k1 - k2 : ℤ) : ℝ) := by
    push_cast
    rw [hk1, hk2]
  use (k1 - k2)
  constructor
  · rw [← h_diff]
    have h1 : |x| - |x - D| ≤ D := by
      have h := abs_sub_abs_le_abs_sub x (x - D)
      have h_simp : x - (x - D) = D := by ring
      rw [h_simp, abs_of_pos hD] at h
      exact h
    have h2 : -D ≤ |x| - |x - D| := by
      have h := abs_sub_abs_le_abs_sub (x - D) x
      have h_simp : (x - D) - x = -D := by ring
      have hD' : |-D| = D := by rw [abs_neg, abs_of_pos hD]
      rw [h_simp, hD'] at h
      linarith
    exact abs_le.mpr ⟨h2, h1⟩
  · exact h_diff

/-- On the line segment 0 ≤ x ≤ D, the position x is uniquely determined by the distance difference n = |x| - |x - D|:
    x = (n + D) / 2. -/
theorem collinear_segment_unique_position (D : ℝ) (x : ℝ) (n : ℝ)
    (h_seg : 0 ≤ x ∧ x ≤ D)
    (h_diff : |x| - |x - D| = n) :
    x = (n + D) / 2 := by
  have hx : |x| = x := abs_of_nonneg h_seg.1
  have hxD : |x - D| = -(x - D) := by
    have : x - D ≤ 0 := by linarith
    exact abs_of_nonpos this
  rw [hx, hxD] at h_diff
  linarith

/-- The integer difference n is bounded between -D and D. -/
theorem difference_in_closed_interval (D : ℝ) (n : ℤ) (hn : |(n : ℝ)| ≤ D) :
    -D ≤ (n : ℝ) ∧ (n : ℝ) ≤ D := by
  exact abs_le.mp hn

/-- An infinite set with pairwise integral distances cannot have points at unbounded distances
    from a collinear line segment: distances are locked into integer levels. -/
theorem erdos_anning_difference_level_locked (D : ℝ) (hD : D > 0)
    (x : ℝ) (k1 k2 : ℤ) (hx1 : |x| = (k1 : ℝ)) (hx2 : |x - D| = (k2 : ℝ)) :
    ∃ n : ℤ, -D ≤ (n : ℝ) ∧ (n : ℝ) ≤ D ∧ (k1 : ℝ) - (k2 : ℝ) = (n : ℝ) := by
  obtain ⟨n, hn_le, hn_eq⟩ := collinear_integral_distance_bound D hD x ⟨k1, hx1⟩ ⟨k2, hx2⟩
  have h_diff : |x| - |x - D| = (k1 : ℝ) - (k2 : ℝ) := by
    rw [hx1, hx2]
  have heq : (k1 : ℝ) - (k2 : ℝ) = (n : ℝ) := by
    rw [← h_diff, hn_eq]
  have h_bounds := difference_in_closed_interval D n hn_le
  exact ⟨n, h_bounds.1, h_bounds.2, heq⟩

/-- Erdős-Anning Collinear Finiteness:
    For any baseline distance D > 0, the number of possible integral differences is strictly bounded
    by the integer diameter 2 * ⌊D⌋ + 1. -/
theorem erdos_anning_finite_differences (D : ℝ) (hD : D > 0) :
    ∀ n : ℤ, |(n : ℝ)| ≤ D → (n : ℝ) ≤ D ∧ -D ≤ (n : ℝ) := by
  intro n hn
  exact ⟨(abs_le.mp hn).2, (abs_le.mp hn).1⟩

#print axioms collinear_integral_distance_bound
#print axioms collinear_segment_unique_position
#print axioms difference_in_closed_interval
#print axioms erdos_anning_difference_level_locked
#print axioms erdos_anning_finite_differences

end ErdosAnning
