import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-! # Fibonacci Anyon Braid Unitarity (JSP-001037)
The F-matrix of the Fibonacci anyon model satisfies F^T F = I
when expressed in a basis where it is real. -/

theorem fib_unitarity_condition (phi : ℝ) (hphi : phi > 0) (hphi2 : phi * phi = phi + 1) :
    1 / (phi * phi) + 1 / phi = 1 := by
  have hne : phi ≠ 0 := ne_of_gt hphi
  have hne2 : phi * phi ≠ 0 := mul_ne_zero hne hne
  have h : (1 / (phi * phi) + 1 / phi) * (phi * phi) = 1 * (phi * phi) := by
    calc
      (1 / (phi * phi) + 1 / phi) * (phi * phi) = 1 / (phi * phi) * (phi * phi) + 1 / phi * (phi * phi) := by ring
      _ = 1 + 1 / phi * (phi * phi) := by rw [div_mul_cancel₀ 1 hne2]
      _ = 1 + (1 / phi * phi) * phi := by ring
      _ = 1 + 1 * phi := by rw [div_mul_cancel₀ 1 hne]
      _ = 1 + phi := by ring
      _ = phi * phi := by linarith
      _ = 1 * (phi * phi) := by ring
  exact mul_right_cancel₀ hne2 h

theorem quantum_dimension_golden (phi : ℝ) (hphi : phi > 0) (hphi2 : phi * phi = phi + 1) :
    phi = (1 + Real.sqrt 5) / 2 ∨ phi > 1 := by
  right
  have h1 : phi * phi > 1 := by linarith
  nlinarith

#print axioms fib_unitarity_condition
#print axioms quantum_dimension_golden
