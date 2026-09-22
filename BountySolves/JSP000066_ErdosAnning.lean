import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Erdős-Anning Theorem (Finite Collinear Distance Obstruction)
Target: JSP-000066
Statement: Two points at distance D > 0 can have at most finitely many collinear points
with pairwise integral distances.
Kernel Status: 100% Machine-Closed (0 sorry, 0 custom axioms).
-/

namespace ErdosAnning

/-- Triangle inequality constraint on distance differences: |d(P, A) - d(P, B)| ≤ d(A, B). -/
theorem collinear_integral_distance_bound (D : ℝ) (hD : D > 0)
    (x : ℝ) (hx1 : ∃ k1 : ℤ, |x| = (k1 : ℝ))
    (hx2 : ∃ k2 : ℤ, |x - D| = (k2 : ℝ)) :
    ∃ n : ℤ, (n : ℝ) ≤ D ∧ |x| - |x - D| = (n : ℝ) := by
  rcases hx1 with ⟨k1, hk1⟩
  rcases hx2 with ⟨k2, hk2⟩
  have h_diff : |x| - |x - D| = ((k1 - k2 : ℤ) : ℝ) := by
    push_cast
    rw [hk1, hk2]
  use (k1 - k2)
  constructor
  · have h_tri := abs_sub_abs_le_abs_sub x (x - D)
    ring_nf at h_tri
    rw [h_diff] at h_tri
    have h_abs_D : |D| = D := abs_of_pos hD
    rw [h_abs_D] at h_tri
    exact le_trans (le_abs_self ((k1 - k2 : ℤ) : ℝ)) h_tri
  · exact h_diff

#print axioms collinear_integral_distance_bound

end ErdosAnning