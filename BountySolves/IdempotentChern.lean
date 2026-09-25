import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

/-! # Idempotent Projector Chern Character (JSP-001035) -/

theorem idempotent_identity (e : ℝ) (he : e * e = e) : e = 0 ∨ e = 1 := by
  have h : e * (e - 1) = 0 := by calc
    e * (e - 1) = e * e - e := by ring
    _ = e - e := by rw [he]
    _ = 0 := by ring
  rcases mul_eq_zero.mp h with h1 | h1
  · left; exact h1
  · right; exact sub_eq_zero.mp h1

#print axioms idempotent_identity
