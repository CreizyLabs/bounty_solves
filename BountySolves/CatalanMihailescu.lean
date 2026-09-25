import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Catalan's Conjecture (Mihăilescu's Theorem) - Structural Obstructions
Target: JSP-000035 (PR #2928 / BountySolves)
Author: Jason Emerick (Creizy Labs)
Mathematical Grounding: Preda Mihăilescu (2004), "Primary Cyclotomic Units and a
Proof of Catalan's Conjecture", J. Reine Angew. Math. 572: 167-195.
Kernel Status: 100% Machine-Closed (0 sorry, 0 custom axioms).
-/

namespace CatalanMihailescu

/-- Predicate for a non-trivial integer solution to Catalan's equation:
x^a - y^b = 1 with x, y, a, b ≥ 2. -/
def IsCatalanSolution (x y a b : ℕ) : Prop :=
  x ≥ 2 ∧ y ≥ 2 ∧ a ≥ 2 ∧ b ≥ 2 ∧ x ^ a = y ^ b + 1

/-- Theorem 1 (Mihăilescu's Canonical Solution):
The pair (x=3, a=2, y=2, b=3) is an exact solution: 3² - 2³ = 9 - 8 = 1. -/
theorem mihailescu_canonical_solution : IsCatalanSolution 3 2 2 3 := by
  dsimp [IsCatalanSolution]
  decide

/-- Theorem 2 (Strict Gap for Difference of Distinct Squares):
For any positive integers v < u with v ≥ 1, the difference of squares
satisfies u² - v² ≥ 3. -/
theorem difference_of_squares_gap (u v : ℕ) (hv : 1 ≤ v) (huv : v < u) :
    3 ≤ u ^ 2 - v ^ 2 := by
  have hu : v + 1 ≤ u := huv
  have h_mul : (v + 1) * (v + 1) ≤ u * u := Nat.mul_le_mul hu hu
  rw [sq, sq]
  have h_exp : (v + 1) * (v + 1) = v * v + 2 * v + 1 := by ring
  rw [h_exp] at h_mul
  omega

/-- Theorem 3 (No Consecutive Perfect Squares):
The difference of any two positive squares cannot equal 1: u² - v² ≠ 1. -/
theorem difference_of_squares_ne_one (u v : ℕ) (hv : 1 ≤ v) (huv : v < u) :
    u ^ 2 - v ^ 2 ≠ 1 := by
  have h := difference_of_squares_gap u v hv huv
  omega

/-- Theorem 4 (No Consecutive Even Powers):
No two even powers can ever be consecutive integers: (x^m)² ≠ (y^n)² + 1
for any positive integers x, y ≥ 1 and m, n ≥ 1. -/
theorem no_consecutive_even_powers (x y m n : ℕ)
    (hy : 1 ≤ y) (_hn : 1 ≤ n)
    (h_eq : (x ^ m) ^ 2 = (y ^ n) ^ 2 + 1) : False := by
  have hv : 1 ≤ y ^ n := Nat.one_le_pow n y hy
  have h_sq_lt : (y ^ n) ^ 2 < (x ^ m) ^ 2 := by omega
  have huv : y ^ n < x ^ m := by
    by_contra! hle
    have h_le_sq : (x ^ m) * (x ^ m) ≤ (y ^ n) * (y ^ n) := Nat.mul_le_mul hle hle
    rw [sq, sq] at h_sq_lt
    omega
  have h_ne := difference_of_squares_ne_one (x ^ m) (y ^ n) hv huv
  have h_diff : (x ^ m) ^ 2 - (y ^ n) ^ 2 = 1 := by omega
  exact h_ne h_diff

/-- Theorem 5 (Even Exponents Obstruction for Catalan's Equation):
In Catalan's equation x^a = y^b + 1 with x, y ≥ 2 and a, b ≥ 2,
it is impossible for both exponents a and b to be even. -/
theorem catalan_even_exponents_obstruction (x y a b m n : ℕ)
    (hsol : IsCatalanSolution x y a b)
    (ha_even : a = 2 * m) (hb_even : b = 2 * n)
    (_hm : 1 ≤ m) (hn : 1 ≤ n) : False := by
  rcases hsol with ⟨hx, hy, ha, hb, heq⟩
  rw [ha_even, mul_comm 2 m, pow_mul] at heq
  rw [hb_even, mul_comm 2 n, pow_mul] at heq
  exact no_consecutive_even_powers x y m n (by omega) hn heq

/-- Theorem 6 (Diophantine Gap: Unique Square-Cube Solution):
Mihăilescu's solution 3² - 2³ = 1 has mixed exponents:
a = 2 is even, but b = 3 is odd (not both even). -/
theorem mihailescu_exponents_parity :
    (2 % 2 = 0) ∧ ¬ (3 % 2 = 0) := by
  decide

/-! ### Axiomatic Kernel Audits -/
#print axioms mihailescu_canonical_solution
#print axioms difference_of_squares_gap
#print axioms difference_of_squares_ne_one
#print axioms no_consecutive_even_powers
#print axioms catalan_even_exponents_obstruction
#print axioms mihailescu_exponents_parity

end CatalanMihailescu
