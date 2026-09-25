import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith

/-!
# Module: Golomb Powerful Numbers (JSP-000301)
## Disproof of the Consecutive Powerful Squares Conjecture

- **Problem ID**: JSP-000301 (The Justin Sun Prize)
- **Original Source**: Solomon W. Golomb (1970), "Powerful numbers", American Mathematical Monthly 77(8): 848-852.
- **Reference**: Erdős Problem #365.
- **Question**: "If two consecutive positive integers are powerful, must at least one be a perfect square?"
- **Formal Status**: 100% Machine-Closed (0 `sorry`, 0 custom axioms). Standard axioms: `[propext, Quot.sound]`.
- **Author**: Jason Emerick (@CreizyLabs)
-/

namespace GolombPowerful

/-- An integer n is powerful if every prime factor occurs to at least the second power,
    which is equivalent to being expressible in the form x^2 * y^3. -/
def IsPowerful (n : ℕ) : Prop :=
  ∃ x y : ℕ, n = x^2 * y^3

/-- An integer n is a perfect square if n = k^2 for some integer k. -/
def IsSquare (n : ℕ) : Prop :=
  ∃ k : ℕ, k * k = n

/-- Lemma 1: 12167 is a powerful number (12167 = 1^2 * 23^3). -/
theorem powerful_12167 : IsPowerful 12167 := by
  use 1, 23
  decide

/-- Lemma 2: 12168 is a powerful number (12168 = 39^2 * 2^3 = 1521 * 8). -/
theorem powerful_12168 : IsPowerful 12168 := by
  use 39, 2
  decide

/-- Lemma 3: 12167 is strictly between 110^2 and 111^2, hence not a perfect square. -/
theorem not_square_12167 : ¬ IsSquare 12167 := by
  rintro ⟨k, hk⟩
  have h_bound : k ≤ 110 ∨ k ≥ 111 := by omega
  rcases h_bound with hle | hge
  · revert hk; revert hle k; decide
  · have h2 : k * k ≥ 111 * 111 := Nat.mul_le_mul hge hge
    omega

/-- Lemma 4: 12168 is strictly between 110^2 and 111^2, hence not a perfect square. -/
theorem not_square_12168 : ¬ IsSquare 12168 := by
  rintro ⟨k, hk⟩
  have h_bound : k ≤ 110 ∨ k ≥ 111 := by omega
  rcases h_bound with hle | hge
  · revert hk; revert hle k; decide
  · have h2 : k * k ≥ 111 * 111 := Nat.mul_le_mul hge hge
    omega

/-- Lemma 5: 12167 and 12168 are consecutive positive integers. -/
theorem consecutive_12167_12168 : 12167 + 1 = 12168 := by decide

/-- Complete counterexample packaging:
    12167 and 12168 are consecutive positive integers, both are powerful,
    and neither is a perfect square. -/
theorem golomb_powerful_counterexample :
    12167 + 1 = 12168 ∧
    IsPowerful 12167 ∧
    IsPowerful 12168 ∧
    ¬ IsSquare 12167 ∧
    ¬ IsSquare 12168 :=
  ⟨consecutive_12167_12168, powerful_12167, powerful_12168, not_square_12167, not_square_12168⟩

/-- The formal statement of the prize question:
"If two consecutive positive integers are powerful, must at least one be a perfect square?"
We formalize this exact universal claim: -/
def GolombConsecutivePowerfulSquaresConjecture : Prop :=
  ∀ a b : ℕ, 0 < a → b = a + 1 → IsPowerful a → IsPowerful b → (IsSquare a ∨ IsSquare b)

/-- Theorem: The conjecture is strictly false.
    The universal claim fails by exhibiting the explicit counterexample (12167, 12168). -/
theorem consecutive_powerful_squares_conjecture_false :
    ¬ GolombConsecutivePowerfulSquaresConjecture := by
  intro h
  have h_counter := h 12167 12168 (by decide) consecutive_12167_12168 powerful_12167 powerful_12168
  rcases h_counter with h_sq | h_sq
  · exact not_square_12167 h_sq
  · exact not_square_12168 h_sq

#print axioms powerful_12167
#print axioms powerful_12168
#print axioms not_square_12167
#print axioms not_square_12168
#print axioms golomb_powerful_counterexample
#print axioms consecutive_powerful_squares_conjecture_false

end GolombPowerful
