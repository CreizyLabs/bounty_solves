/-
Copyright (c) 2026 Compendium Formal Verification Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Problem 70 (JSP-000070) & Problem 79 (JSP-000079): Exact Cauchy–Schwarz Algebraic Kernels

This standalone Mathlib 4 module formalizes the exact integer Cauchy–Schwarz algebraic
kernels underlying:
* **Problem 70 (Disjoint Sidon Sets)**: Non-zero differences inside disjoint Sidon subsets
  `A, B ⊆ {1, ..., N}` satisfy `|A|(|A| - 1) + |B|(|B| - 1) ≤ 2(N - 1)`, and the variance
  defect identity `2(a² + b²) - (a + b)² = (a - b)² ≥ 0` forces `(a + b)² ≤ 4N`.
* **Problem 79 (`C_4` Codegree Variance Bound)**: Any two vertices / degree fibers satisfy
  the exact quadratic Cauchy–Schwarz inequality bounding common-neighbor pairs.

## Verification Guarantees
* Zero `sorry`
* Zero `axiom`
* Zero floating-point approximations (exact `Int` polynomial identities and inequalities)
-/

namespace Problem70_And_79_CauchySchwarz

/-- Exact algebraic variance identity: `2*(a² + b²) - (a + b)² = (a - b)²`. -/
theorem two_squares_minus_sum_sq (a b : Int) :
    2 * (a * a + b * b) - (a + b) * (a + b) = (a - b) * (a - b) := by
  ring

/-- For any integer `z`, `z * z ≥ 0`. -/
theorem sq_nonneg (z : Int) : 0 ≤ z * z :=
  mul_self_nonneg z

/-- Theorem (JSP-000070 Cauchy–Schwarz Sidon Sum Bound):
    If `|A|² + |B|² ≤ 2*N`, then `(|A| + |B|)² ≤ 4*N`. -/
theorem disjoint_sidon_sum_sq_bound (a b N : Int)
    (h_diff : a * a + b * b ≤ 2 * N) :
    (a + b) * (a + b) ≤ 4 * N := by
  have h_id : 2 * (a * a + b * b) - (a + b) * (a + b) = (a - b) * (a - b) :=
    two_squares_minus_sum_sq a b
  have h_sq : 0 ≤ (a - b) * (a - b) := sq_nonneg (a - b)
  linarith

/-- Exact Disjoint Sidon Difference Packing Inequality:
    If `a*(a - 1) + b*(b - 1) ≤ 2*(N - 1)`, then `(a + b)*(a + b - 1) ≤ 4*N - 4 + (a + b)`. -/
theorem disjoint_sidon_ordered_differences_bound (a b N : Int)
    (h_pack : a * (a - 1) + b * (b - 1) ≤ 2 * (N - 1)) :
    (a + b) * (a + b) - 2 * (a + b) ≤ 4 * N - 4 := by
  have h_id : (a + b) * (a + b) - 2 * (a + b) =
      2 * (a * (a - 1) + b * (b - 1)) - (a - b) * (a - b) := by ring
  have h_sq : 0 ≤ (a - b) * (a - b) := sq_nonneg (a - b)
  linarith

/-- Theorem (JSP-000079 Four-Term Cauchy–Schwarz Codegree Kernel):
    For any four integer codegree/degree fibers `d1, d2, d3, d4`,
    `(d1 + d2 + d3 + d4)² ≤ 4 * (d1² + d2² + d3² + d4²)`. -/
theorem four_fiber_cauchy_schwarz (d1 d2 d3 d4 : Int) :
    (d1 + d2 + d3 + d4) * (d1 + d2 + d3 + d4) ≤
    4 * (d1 * d1 + d2 * d2 + d3 * d3 + d4 * d4) := by
  have h_id : 4 * (d1 * d1 + d2 * d2 + d3 * d3 + d4 * d4) -
      (d1 + d2 + d3 + d4) * (d1 + d2 + d3 + d4) =
      (d1 - d2) * (d1 - d2) + (d1 - d3) * (d1 - d3) + (d1 - d4) * (d1 - d4) +
      (d2 - d3) * (d2 - d3) + (d2 - d4) * (d2 - d4) + (d3 - d4) * (d3 - d4) := by ring
  have h12 : 0 ≤ (d1 - d2) * (d1 - d2) := sq_nonneg (d1 - d2)
  have h13 : 0 ≤ (d1 - d3) * (d1 - d3) := sq_nonneg (d1 - d3)
  have h14 : 0 ≤ (d1 - d4) * (d1 - d4) := sq_nonneg (d1 - d4)
  have h23 : 0 ≤ (d2 - d3) * (d2 - d3) := sq_nonneg (d2 - d3)
  have h24 : 0 ≤ (d2 - d4) * (d2 - d4) := sq_nonneg (d2 - d4)
  have h34 : 0 ≤ (d3 - d4) * (d3 - d4) := sq_nonneg (d3 - d4)
  linarith

end Problem70_And_79_CauchySchwarz
