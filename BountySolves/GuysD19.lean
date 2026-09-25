import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

namespace GuysProblemD19

def HasFourRationalDistances (x y : ℝ) : Prop :=
  ∃ (d₁ d₂ d₃ d₄ : ℚ),
    (d₁ : ℝ)^2 = x^2 + y^2 ∧
    (d₂ : ℝ)^2 = (x - 1)^2 + y^2 ∧
    (d₃ : ℝ)^2 = (x - 1)^2 + (y - 1)^2 ∧
    (d₄ : ℝ)^2 = x^2 + (y - 1)^2

theorem british_flag_real (x y d₁ d₂ d₃ d₄ : ℝ)
    (h₁ : d₁^2 = x^2 + y^2)
    (h₂ : d₂^2 = (x - 1)^2 + y^2)
    (h₃ : d₃^2 = (x - 1)^2 + (y - 1)^2)
    (h₄ : d₄^2 = x^2 + (y - 1)^2) :
    d₁^2 + d₃^2 = d₂^2 + d₄^2 := by
  linear_combination h₁ + h₃ - h₂ - h₄

theorem british_flag_int (X Y W D₁ D₂ D₃ D₄ : ℤ)
    (h₁ : D₁^2 = X^2 + Y^2)
    (h₂ : D₂^2 = (X - W)^2 + Y^2)
    (h₃ : D₃^2 = (X - W)^2 + (Y - W)^2)
    (h₄ : D₄^2 = X^2 + (Y - W)^2) :
    D₁^2 + D₃^2 = D₂^2 + D₄^2 := by
  linear_combination h₁ + h₃ - h₂ - h₄

lemma x_coord_identity (x y d₁ d₂ : ℝ)
    (h₁ : d₁^2 = x^2 + y^2)
    (h₂ : d₂^2 = (x - 1)^2 + y^2) :
    x = (d₁^2 - d₂^2 + 1) / 2 := by
  have h₂' : d₂^2 = x^2 - 2 * x + 1 + y^2 := by
    calc d₂^2 = (x - 1)^2 + y^2 := h₂
    _ = x^2 - 2 * x + 1 + y^2 := by ring
  linarith

lemma y_coord_identity (x y d₁ d₄ : ℝ)
    (h₁ : d₁^2 = x^2 + y^2)
    (h₄ : d₄^2 = x^2 + (y - 1)^2) :
    y = (d₁^2 - d₄^2 + 1) / 2 := by
  have h₄' : d₄^2 = x^2 + y^2 - 2 * y + 1 := by
    calc d₄^2 = x^2 + (y - 1)^2 := h₄
    _ = x^2 + y^2 - 2 * y + 1 := by ring
  linarith

theorem coordinate_rationality (x y : ℝ) (q₁ q₂ q₄ : ℚ)
    (h₁ : (q₁ : ℝ)^2 = x^2 + y^2)
    (h₂ : (q₂ : ℝ)^2 = (x - 1)^2 + y^2)
    (h₄ : (q₄ : ℝ)^2 = x^2 + (y - 1)^2) :
    ∃ (qx qy : ℚ), (qx : ℝ) = x ∧ (qy : ℝ) = y := by
  let qx : ℚ := (q₁^2 - q₂^2 + 1) / 2
  let qy : ℚ := (q₁^2 - q₄^2 + 1) / 2
  use qx, qy
  constructor
  · have hx : x = ((q₁ : ℝ)^2 - (q₂ : ℝ)^2 + 1) / 2 :=
      x_coord_identity x y (q₁ : ℝ) (q₂ : ℝ) h₁ h₂
    have hcast : (qx : ℝ) = ((q₁ : ℝ)^2 - (q₂ : ℝ)^2 + 1) / 2 := by
      dsimp [qx]; rw [sq, sq]; push_cast; ring
    rw [hcast, ← hx]
  · have hy : y = ((q₁ : ℝ)^2 - (q₄ : ℝ)^2 + 1) / 2 :=
      y_coord_identity x y (q₁ : ℝ) (q₄ : ℝ) h₁ h₄
    have hcast : (qy : ℝ) = ((q₁ : ℝ)^2 - (q₄ : ℝ)^2 + 1) / 2 := by
      dsimp [qy]; rw [sq, sq]; push_cast; ring
    rw [hcast, ← hy]

lemma zmod4_sq_cases (a : ZMod 4) : a^2 = 0 ∨ a^2 = 1 := by
  fin_cases a <;> decide

lemma zmod4_no_square_eq_two (d : ZMod 4) : d^2 ≠ 2 := by
  fin_cases d <;> decide

theorem mod4_sum_of_odd_squares_not_square (x y d : ZMod 4)
    (hx : x = 1 ∨ x = 3) (hy : y = 1 ∨ y = 3) :
    x^2 + y^2 ≠ d^2 := by
  have h_sum : x^2 + y^2 = 2 := by
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rfl
  rw [h_sum]
  intro h_eq
  exact zmod4_no_square_eq_two d h_eq.symm

lemma zmod8_odd_sq (a : ZMod 8) (ha : a = 1 ∨ a = 3 ∨ a = 5 ∨ a = 7) :
    a^2 = 1 := by
  rcases ha with rfl | rfl | rfl | rfl <;> decide

lemma zmod8_sq_zero_imp_div4 (y : ZMod 8) (hy : y^2 = 0) :
    y = 0 ∨ y = 4 := by
  revert y hy
  decide

theorem zmod8_valuation_floor (x y d : ZMod 8)
    (hx : x = 1 ∨ x = 3 ∨ x = 5 ∨ x = 7)
    (hd : d = 1 ∨ d = 3 ∨ d = 5 ∨ d = 7)
    (h_eq : x^2 + y^2 = d^2) :
    y = 0 ∨ y = 4 := by
  have hx2 : x^2 = 1 := zmod8_odd_sq x hx
  have hd2 : d^2 = 1 := zmod8_odd_sq d hd
  have hy2 : y^2 = 0 := by
    calc y^2 = (x^2 + y^2) - x^2 := by ring
    _ = d^2 - x^2 := by rw [h_eq]
    _ = 1 - 1 := by rw [hd2, hx2]
    _ = 0 := by ring
  exact zmod8_sq_zero_imp_div4 y hy2

/-! ### 5. The 2-Adic and 3-Adic Valuation Obstructions -/

/-- Theorem (2-Adic Valuation Floor):
In ZMod 4, the grid denominator W must be even: W ≡ 0 (mod 2).
If W were odd, no choice of parities for (X, Y) can prevent at least one of the
squared distances from being congruent to 2 modulo 4, which is impossible for any square. -/
theorem zmod4_denominator_must_be_even (X Y W D₁ D₂ D₃ D₄ : ZMod 4)
    (h₁ : D₁^2 = X^2 + Y^2)
    (h₂ : D₂^2 = (X - W)^2 + Y^2)
    (h₃ : D₃^2 = (X - W)^2 + (Y - W)^2)
    (h₄ : D₄^2 = X^2 + (Y - W)^2) :
    W = 0 ∨ W = 2 := by
  revert X Y W D₁ D₂ D₃ D₄ h₁ h₂ h₃ h₄
  decide

/-- No element in ZMod 3 has square equal to 2. -/
lemma zmod3_no_square_eq_two (d : ZMod 3) : d^2 ≠ 2 := by
  fin_cases d <;> decide

/-- Theorem (3-Adic Valuation Floor):
In ZMod 3, any integer grid configuration satisfying all four square distance relations
forces the grid denominator W to vanish modulo 3: 3 | W. -/
theorem zmod3_denominator_must_be_zero (X Y W D₁ D₂ D₃ D₄ : ZMod 3)
    (h₁ : D₁^2 = X^2 + Y^2)
    (h₂ : D₂^2 = (X - W)^2 + Y^2)
    (h₃ : D₃^2 = (X - W)^2 + (Y - W)^2)
    (h₄ : D₄^2 = X^2 + (Y - W)^2) :
    W = 0 := by
  revert X Y W D₁ D₂ D₃ D₄ h₁ h₂ h₃ h₄
  decide

/-! ### Axiomatic Kernel Audits -/
#print axioms british_flag_real
#print axioms british_flag_int
#print axioms coordinate_rationality
#print axioms mod4_sum_of_odd_squares_not_square
#print axioms zmod8_valuation_floor
#print axioms zmod4_denominator_must_be_even
#print axioms zmod3_no_square_eq_two
#print axioms zmod3_denominator_must_be_zero

end GuysProblemD19
