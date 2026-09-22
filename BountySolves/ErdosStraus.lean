import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Erdős-Straus Conjecture Modular Sub-Families
Author: Jason Emerick (Creizy Labs)
Mathematical Grounding: Rational Egyptian Fraction Identities for 4/n.
Kernel Status: 100% Machine-Closed (0 sorry, 0 custom axioms).
-/

namespace ErdosStraus

/-- The Erdős-Straus Egyptian fraction decomposition relation:
`4 / n = 1 / x + 1 / y + 1 / z` for positive integers `x, y, z`. -/
def IsErdosStrausSolution (n x y z : ℕ) : Prop :=
  (4 : ℚ) / n = 1 / x + 1 / y + 1 / z

/-- Theorem 1 (Even Multiples of 4 Decomposition):
For any `n = 4k` (with `k ≥ 1`), `4 / (4k) = 1 / (2k) + 1 / (4k) + 1 / (4k)`. -/
theorem erdos_straus_mod4_zero (k : ℕ) (hk : 0 < k) :
    (4 : ℚ) / (4 * k) = 1 / (2 * (k : ℚ)) + 1 / (4 * (k : ℚ)) + 1 / (4 * (k : ℚ)) := by
  have hkq : (k : ℚ) ≠ 0 := by positivity
  field_simp
  ring

/-- Theorem 1b (Distinct Denominators for n = 4k):
For any `n = 4k` (with `k ≥ 1`), `4 / (4k) = 1 / (2k) + 1 / (3k) + 1 / (6k)`. -/
theorem erdos_straus_mod4_zero_distinct (k : ℕ) (hk : 0 < k) :
    (4 : ℚ) / (4 * k) = 1 / (2 * (k : ℚ)) + 1 / (3 * (k : ℚ)) + 1 / (6 * (k : ℚ)) := by
  have hkq : (k : ℚ) ≠ 0 := by positivity
  field_simp
  ring

/-- Theorem 2 (Residue Class 2 mod 4 Decomposition):
For any `n = 4k + 2`, `4 / (4k + 2) = 1 / (k + 1) + 1 / (2(k + 1)(2k + 1)) + 1 / (2(k + 1)(2k + 1))`. -/
theorem erdos_straus_mod4_two (k : ℕ) :
    (4 : ℚ) / (4 * (k : ℚ) + 2) =
      1 / ((k : ℚ) + 1) +
      1 / (2 * ((k : ℚ) + 1) * (2 * (k : ℚ) + 1)) +
      1 / (2 * ((k : ℚ) + 1) * (2 * (k : ℚ) + 1)) := by
  have h1 : (k : ℚ) + 1 ≠ 0 := by positivity
  have h2 : 2 * (k : ℚ) + 1 ≠ 0 := by positivity
  have h3 : 4 * (k : ℚ) + 2 ≠ 0 := by positivity
  field_simp
  ring

#print axioms erdos_straus_mod4_zero
#print axioms erdos_straus_mod4_zero_distinct
#print axioms erdos_straus_mod4_two

end ErdosStraus
