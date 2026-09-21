import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases

/-!
# Module I: Guy's Problem D19 (Four-Distance Problem)
Author: Jason Emerick (Creizy Labs)
Problem: Rational Distances from the Vertices of a Unit Square
Mathematical Grounding: Euler-British Flag Invariant, Coordinate Rationality,
and Modulo 4 / Modulo 8 Valuation Floors.
Kernel Status: 100% Machine-Closed Core (0 sorry, 0 custom axioms).
-/

namespace GuysProblemD19

/-! ### 1. Problem Formulation and British Flag Invariants -/

/-- Predicate stating that a point (x, y) in the Euclidean plane has rational
Euclidean distances to all four vertices of the unit square:
(0,0), (1,0), (1,1), and (0,1). -/
def HasFourRationalDistances (x y : ℝ) : Prop :=
  ∃ (d₁ d₂ d₃ d₄ : ℚ),
    (d₁ : ℝ)^2 = x^2 + y^2 ∧
    (d₂ : ℝ)^2 = (x - 1)^2 + y^2 ∧
    (d₃ : ℝ)^2 = (x - 1)^2 + (y - 1)^2 ∧
    (d₄ : ℝ)^2 = x^2 + (y - 1)^2

/-- Theorem 2.2: The Euler-British Flag Invariant in ℝ.
For any Euclidean point (x, y), the sum of squared distances to diagonally
opposite vertices of the unit square is identically equal. -/
theorem british_flag_real (x y d₁ d₂ d₃ d₄ : ℝ)
    (h₁ : d₁^2 = x^2 + y^2)
    (h₂ : d₂^2 = (x - 1)^2 + y^2)
    (h₃ : d₃^2 = (x - 1)^2 + (y - 1)^2)
    (h₄ : d₄^2 = x^2 + (y - 1)^2) :
    d₁^2 + d₃^2 = d₂^2 + d₄^2 := by
  linear_combination h₁ + h₃ - h₂ - h₄

/-- Theorem 2.2 (Integer Lattice Grid):
The British Flag invariant holds identically on the cleared-denominator integer grid. -/
theorem british_flag_int (X Y W D₁ D₂ D₃ D₄ : ℤ)
    (h₁ : D₁^2 = X^2 + Y^2)
    (h₂ : D₂^2 = (X - W)^2 + Y^2)
    (h₃ : D₃^2 = (X - W)^2 + (Y - W)^2)
    (h₄ : D₄^2 = X^2 + (Y - W)^2) :
    D₁^2 + D₃^2 = D₂^2 + D₄^2 := by
  linear_combination h₁ + h₃ - h₂ - h₄

/-! ### 2. Theorem 2.1: Coordinate Rationality -/

lemma x_coord_identity (x y d₁ d₂ : ℝ)
    (h₁ : d₁^2 = x^2 + y^2)
    (h₂ : d₂^2 = (x - 1)^2 + y^2) :
    x = (d₁^2 - d₂^2 + 1) / 2 := by
  linear_combination (h₁ - h₂) / 2

lemma y_coord_identity (x y d₁ d₄ : ℝ)
    (h₁ : d₁^2 = x^2 + y^2)
    (h₄ : d₄^2 = x^2 + (y - 1)^2) :
    y = (d₁^2 - d₄^2 + 1) / 2 := by
  linear_combination (h₁ - h₄) / 2

/-- Theorem 2.1: Coordinate Rationality Theorem.
Any candidate point having rational Euclidean distances to vertices
(0,0), (1,0), and (0,1) must have strictly rational Cartesian coordinates:
(x, y) ∈ ℚ². -/
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
      push_cast; rfl
    rw [hcast, ← hx]
  · have hy : y = ((q₁ : ℝ)^2 - (q₄ : ℝ)^2 + 1) / 2 :=
      y_coord_identity x y (q₁ : ℝ) (q₄ : ℝ) h₁ h₄
    have hcast : (qy : ℝ) = ((q₁ : ℝ)^2 - (q₄ : ℝ)^2 + 1) / 2 := by
      push_cast; rfl
    rw [hcast, ← hy]

/-! ### 3. Theorem 4.1: Modulo 4 and Modulo 8 Valuation Floors -/

lemma zmod4_sq_cases (a : ZMod 4) : a^2 = 0 ∨ a^2 = 1 := by
  fin_cases a <;> decide

lemma zmod4_no_square_eq_two (d : ZMod 4) : d^2 ≠ 2 := by
  fin_cases d <;> decide

/-- Parity descent barrier: The sum of two odd squares in ℤ/4ℤ is always 2,
which can never match any square D² in ℤ/4ℤ. -/
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
  fin_cases y <;> revert hy <;> decide

/-- Valuation Floor modulo 8:
If X and D are odd units in ℤ/8ℤ and X² + Y² ≡ D² (mod 8),
then Y must be a multiple of 4, proving v₂(Y) ≥ 2. -/
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

/-! ### 4. Axiomatic Kernel Audits -/
#print axioms british_flag_real
#print axioms british_flag_int
#print axioms coordinate_rationality
#print axioms mod4_sum_of_odd_squares_not_square
#print axioms zmod8_valuation_floor

end GuysProblemD19
