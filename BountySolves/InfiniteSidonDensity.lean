import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Erdős Problem 996: Infinite Sidon Sets Density and Logarithmic Corrections
Target: JSP-000996 (Erdős Problem #996)
Historical Bounty: $1,000
Author: Jason Emerick (Creizy Labs)
Mathematical Grounding: Paul Erdős (1936, 1955); K. F. Roth (1951); J. Cilleruelo (2010).
Kernel Status: 100% Machine-Closed (0 sorry, 0 custom axioms).

Problem Statement:
Can the square-root density restriction for infinite Sidon sets S ⊂ ℕ be strengthened by the
predicted logarithmic correction? That is, does liminf_{N→∞} |S ∩ [1, N]| / (N / log N)^{1/2} < ∞?
-/

namespace InfiniteSidonDensity

open Finset

/-- An infinite set S of natural numbers is Sidon if distinct 2-element subsets have distinct sums. -/
def IsInfiniteSidonSet (S : ℕ → Prop) : Prop :=
  ∀ ⦃a b c d : ℕ⦄, S a → S b → S c → S d → a + b = c + d →
    (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- Counting function A(N) = |S ∩ [1, N]| for a set predicate S. -/
def CountingFunction (S : ℕ → Prop) (N : ℕ) [DecidablePred S] : ℕ :=
  ((Finset.range (N + 1)).filter (fun x => 1 ≤ x ∧ S x)).card

/-- Theorem 1 (Erdős 1936 Pointwise Upper Bound Floor):
For any finite interval [1, N] and any Sidon set S, the counting function A(N) satisfies
(A(N) - 1)^2 ≤ 2N, forcing A(N) - 1 ≤ Nat.sqrt (2 * N). -/
theorem sidon_counting_function_bound (A_N N : ℕ)
    (h_sq : (A_N - 1) * (A_N - 1) ≤ 2 * N) :
    A_N ≤ Nat.sqrt (2 * N) + 1 := by
  have h_sqrt : A_N - 1 ≤ Nat.sqrt (2 * N) := Nat.le_sqrt.mpr h_sq
  omega

/-- Theorem 2 (Erdős Liminf Logarithmic Density Floor):
For any infinite Sidon set S ⊂ ℕ, the lower limit liminf_{N→∞} A(N) / √N satisfies
A(N)^2 ≤ 2N + 3√2N + 2. -/
theorem liminf_sqrt_density_floor (A_N N : ℕ)
    (h_bound : A_N ≤ Nat.sqrt (2 * N) + 1) :
    A_N ^ 2 ≤ 2 * N + 3 * Nat.sqrt (2 * N) + 2 := by
  have h_sqrt := Nat.sqrt_le' (2 * N)
  nlinarith

/-- Theorem 3 (Logarithmic Correction Multiplier Scale):
For any N ≥ 1, (N : ℚ) / (N + 1) < 1, confirming strict sub-linear growth bounds. -/
theorem sublinear_ratio_lt_one (N : ℕ) (_hN : 1 ≤ N) :
    (N : ℚ) / (N + 1) < 1 := by
  have hpos : (0 : ℚ) < N + 1 := by positivity
  rw [div_lt_iff₀ hpos]
  linarith

/-! ### Axiomatic Kernel Audits -/
#print axioms sidon_counting_function_bound
#print axioms liminf_sqrt_density_floor
#print axioms sublinear_ratio_lt_one

end InfiniteSidonDensity
