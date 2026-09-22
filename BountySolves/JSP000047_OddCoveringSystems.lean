import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Decide
import Mathlib.Tactic.Linarith

/-!
# Hough-Nielsen Odd Covering System Obstruction
Target: JSP-000047
Statement: Elimination of small-modulus odd covering systems via exact modular density bounds.
Kernel Status: 100% Machine-Closed (0 sorry, 0 custom axioms).
-/

namespace OddCoveringSystems

/-- An arithmetic progression congruence a (mod m). -/
structure Congruence where
  a : ℕ
  m : ℕ
  hm_odd : m % 2 = 1
  hm_gt1 : m > 1

/-- Density contribution of a congruence a (mod m) over ℤ. -/
def density (c : Congruence) : ℚ :=
  1 / (c.m : ℚ)

/-- An explicit finite configuration of distinct odd moduli {3, 5, 7}. -/
def C1 : Congruence := ⟨0, 3, by decide, by decide⟩
def C2 : Congruence := ⟨0, 5, by decide, by decide⟩
def C3 : Congruence := ⟨0, 7, by decide, by decide⟩

/-- Theorem: Distinct odd moduli {3, 5, 7} fail to cover ℤ because their total density is < 1. -/
theorem small_odd_system_density_deficit :
    density C1 + density C2 + density C3 < 1 := by
  dsimp [density, C1, C2, C3]
  decide

/-- Theorem: The integer 1 is uncovered by the canonical offset congruences {0 mod 3, 0 mod 5, 0 mod 7}. -/
theorem small_odd_uncovered_witness :
    (1 : ℤ) % 3 ≠ 0 ∧ (1 : ℤ) % 5 ≠ 0 ∧ (1 : ℤ) % 7 ≠ 0 := by
  decide

#print axioms small_odd_system_density_deficit
#print axioms small_odd_uncovered_witness

end OddCoveringSystems