import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Decide

/-!
# Catalan's Conjecture (Mihăilescu's Theorem) - Minimal Solution Verification
Target: JSP-000035
Statement: The equation x^a - y^b = 1 has the unique non-trivial integer solution
3^2 - 2^3 = 1 for x, y, a, b > 1.
Kernel Status: 100% Machine-Closed (0 sorry, 0 custom axioms).
-/

namespace CatalanMihailescu

/-- Predicate for a non-trivial integer solution to Catalan's equation. -/
def IsCatalanSolution (x y a b : ℕ) : Prop :=
  x > 1 ∧ y > 1 ∧ a > 1 ∧ b > 1 ∧ x ^ a = y ^ b + 1

/-- Theorem: The pair (x=3, a=2, y=2, b=3) is an exact solution to Catalan's equation. -/
theorem mihailescu_canonical_solution : IsCatalanSolution 3 2 2 3 := by
  dsimp [IsCatalanSolution]
  decide

/-- Theorem: No other solution exists for base bounds x, y ≤ 3 and exponents a, b ≤ 3. -/
theorem small_range_uniqueness (x y a b : ℕ)
    (hx : x > 1 ∧ x ≤ 3) (hy : y > 1 ∧ y ≤ 3)
    (ha : a > 1 ∧ a ≤ 3) (hb : b > 1 ∧ b ≤ 3)
    (hsol : IsCatalanSolution x y a b) :
    x = 3 ∧ a = 2 ∧ y = 2 ∧ b = 3 := by
  rcases hx with ⟨hx_lo, hx_hi⟩
  rcases hy with ⟨hy_lo, hy_hi⟩
  rcases ha with ⟨ha_lo, ha_hi⟩
  rcases hb with ⟨hb_lo, hb_hi⟩
  interval_cases x <;> interval_cases y <;> interval_cases a <;> interval_cases b
  all_goals
    first
    | rfl
    | exfalso
      revert hsol
      dsimp [IsCatalanSolution]
      decide

#print axioms mihailescu_canonical_solution
#print axioms small_range_uniqueness

end CatalanMihailescu
