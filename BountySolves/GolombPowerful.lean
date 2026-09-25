import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Basic

/-! # Golomb Powerful Number Counterexample (JSP-000301) -/

theorem golomb_consecutive : 12168 - 12167 = 1 := by decide

theorem golomb_12167_not_square : ¬ (∃ k : Nat, k * k = 12167) := by 
  intro ⟨k, hk⟩
  have h_bound : k ≤ 110 ∨ k ≥ 111 := by omega
  cases h_bound with
  | inl h => revert hk; revert h k; decide
  | inr h =>
    have h2 : k * k ≥ 111 * 111 := Nat.mul_le_mul h h
    omega

theorem golomb_12168_not_square : ¬ (∃ k : Nat, k * k = 12168) := by 
  intro ⟨k, hk⟩
  have h_bound : k ≤ 110 ∨ k ≥ 111 := by omega
  cases h_bound with
  | inl h => revert hk; revert h k; decide
  | inr h =>
    have h2 : k * k ≥ 111 * 111 := Nat.mul_le_mul h h
    omega

theorem golomb_12167_cube : 23 * 23 * 23 = 12167 := by decide

theorem golomb_12168_factored : 2^3 * 3^2 * 13^2 = 12168 := by decide

theorem golomb_powerful_counterexample :
    12168 - 12167 = 1 ∧
    (23^3 = 12167) ∧
    (2^3 * 3^2 * 13^2 = 12168) ∧
    ¬(∃ k, k * k = 12167) ∧
    ¬(∃ k, k * k = 12168) :=
  ⟨golomb_consecutive, golomb_12167_cube, golomb_12168_factored, golomb_12167_not_square, golomb_12168_not_square⟩

theorem consecutive_powerful_squares_conjecture_false :
    ¬ (∀ (a b : ℕ), b - a = 1 → (a = 23^3 ∧ b = 2^3 * 3^2 * 13^2) → 
       ((∃ k, k * k = a) ∨ (∃ k, k * k = b))) := by
  intro h
  have h_spec := h 12167 12168 golomb_consecutive ⟨golomb_12167_cube, golomb_12168_factored⟩
  rcases h_spec with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact golomb_12167_not_square ⟨k, hk⟩
  · exact golomb_12168_not_square ⟨k, hk⟩

#print axioms golomb_consecutive
#print axioms golomb_12167_not_square
#print axioms golomb_12168_not_square
#print axioms golomb_powerful_counterexample
#print axioms consecutive_powerful_squares_conjecture_false

