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
