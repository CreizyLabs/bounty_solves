import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace ZPhi

@[ext]
structure Element where
  a : ℤ
  b : ℤ
  deriving DecidableEq, Repr

def zero : Element := ⟨0, 0⟩
def one : Element  := ⟨1, 0⟩
def phi : Element  := ⟨0, 1⟩

def add (x y : Element) : Element :=
  ⟨x.a + y.a, x.b + y.b⟩

def neg (x : Element) : Element :=
  ⟨-x.a, -x.b⟩

def mul (x y : Element) : Element :=
  ⟨x.a * y.a + x.b * y.b, x.a * y.b + x.b * y.a + x.b * y.b⟩

instance : Zero Element := ⟨zero⟩
instance : One Element  := ⟨one⟩
instance : Add Element  := ⟨add⟩
instance : Neg Element  := ⟨neg⟩
instance : Mul Element  := ⟨mul⟩
instance : Sub Element  := ⟨fun x y => add x (neg y)⟩

theorem add_assoc (x y z : Element) : (x + y) + z = x + (y + z) := by
  rcases x with ⟨xa, xb⟩; rcases y with ⟨ya, yb⟩; rcases z with ⟨za, zb⟩
  apply Element.ext
  · change (xa + ya) + za = xa + (ya + za); ring
  · change (xb + yb) + zb = xb + (yb + zb); ring

theorem add_comm (x y : Element) : x + y = y + x := by
  rcases x with ⟨xa, xb⟩; rcases y with ⟨ya, yb⟩
  apply Element.ext
  · change xa + ya = ya + xa; ring
  · change xb + yb = yb + xb; ring

theorem zero_add (x : Element) : 0 + x = x := by
  rcases x with ⟨xa, xb⟩
  apply Element.ext
  · change 0 + xa = xa; ring
  · change 0 + xb = xb; ring

theorem add_zero (x : Element) : x + 0 = x := by
  rcases x with ⟨xa, xb⟩
  apply Element.ext
  · change xa + 0 = xa; ring
  · change xb + 0 = xb; ring

theorem add_left_neg (x : Element) : -x + x = 0 := by
  rcases x with ⟨xa, xb⟩
  apply Element.ext
  · change -xa + xa = 0; ring
  · change -xb + xb = 0; ring

theorem mul_assoc (x y z : Element) : (x * y) * z = x * (y * z) := by
  rcases x with ⟨xa, xb⟩; rcases y with ⟨ya, yb⟩; rcases z with ⟨za, zb⟩
  apply Element.ext
  · change (xa * ya + xb * yb) * za + (xa * yb + xb * ya + xb * yb) * zb =
           xa * (ya * za + yb * zb) + xb * (ya * zb + yb * za + yb * zb); ring
  · change (xa * ya + xb * yb) * zb + (xa * yb + xb * ya + xb * yb) * za + (xa * yb + xb * ya + xb * yb) * zb =
           xa * (ya * zb + yb * za + yb * zb) + xb * (ya * za + yb * zb) + xb * (ya * zb + yb * za + yb * zb); ring

theorem mul_comm (x y : Element) : x * y = y * x := by
  rcases x with ⟨xa, xb⟩; rcases y with ⟨ya, yb⟩
  apply Element.ext
  · change xa * ya + xb * yb = ya * xa + yb * xb; ring
  · change xa * yb + xb * ya + xb * yb = ya * xb + yb * xa + yb * xb; ring

theorem one_mul (x : Element) : 1 * x = x := by
  rcases x with ⟨xa, xb⟩
  apply Element.ext
  · change 1 * xa + 0 * xb = xa; ring
  · change 1 * xb + 0 * xa + 0 * xb = xb; ring

theorem mul_one (x : Element) : x * 1 = x := by
  rcases x with ⟨xa, xb⟩
  apply Element.ext
  · change xa * 1 + xb * 0 = xa; ring
  · change xa * 0 + xb * 1 + xb * 0 = xb; ring

theorem left_distrib (x y z : Element) : x * (y + z) = x * y + x * z := by
  rcases x with ⟨xa, xb⟩; rcases y with ⟨ya, yb⟩; rcases z with ⟨za, zb⟩
  apply Element.ext
  · change xa * (ya + za) + xb * (yb + zb) = (xa * ya + xb * yb) + (xa * za + xb * zb); ring
  · change xa * (yb + zb) + xb * (ya + za) + xb * (yb + zb) =
           (xa * yb + xb * ya + xb * yb) + (xa * zb + xb * za + xb * zb); ring

theorem right_distrib (x y z : Element) : (x + y) * z = x * z + y * z := by
  rcases x with ⟨xa, xb⟩; rcases y with ⟨ya, yb⟩; rcases z with ⟨za, zb⟩
  apply Element.ext
  · change (xa + ya) * za + (xb + yb) * zb = (xa * za + xb * zb) + (ya * za + yb * zb); ring
  · change (xa + ya) * zb + (xb + yb) * za + (xb + yb) * zb =
           (xa * zb + xb * za + xb * zb) + (ya * zb + yb * za + yb * zb); ring

theorem phi_squared_identity : phi * phi = phi + 1 := by
  apply Element.ext
  · change 0 * 0 + 1 * 1 = 0 + 1; ring
  · change 0 * 1 + 1 * 0 + 1 * 1 = 1 + 0; ring

def norm (x : Element) : ℤ :=
  x.a^2 + x.a * x.b - x.b^2

theorem norm_mul (x y : Element) : norm (x * y) = norm x * norm y := by
  rcases x with ⟨xa, xb⟩
  rcases y with ⟨ya, yb⟩
  change (xa * ya + xb * yb)^2 + (xa * ya + xb * yb) * (xa * yb + xb * ya + xb * yb) - (xa * yb + xb * ya + xb * yb)^2 =
         (xa^2 + xa * xb - xb^2) * (ya^2 + ya * yb - yb^2)
  ring

def phi_inv_sq : Element := ⟨2, -1⟩
def phi_sq     : Element := ⟨1, 1⟩

theorem norm_phi_inv_sq : norm phi_inv_sq = 1 := by
  decide

theorem phi_inv_sq_is_unit : phi_inv_sq * phi_sq = 1 ∧ phi_sq * phi_inv_sq = 1 := by
  constructor
  · apply Element.ext
    · change 2 * 1 + (-1) * 1 = 1; ring
    · change 2 * 1 + (-1) * 1 + (-1) * 1 = 0; ring
  · apply Element.ext
    · change 1 * 2 + 1 * (-1) = 1; ring
    · change 1 * (-1) + 1 * 2 + 1 * (-1) = 0; ring

theorem unit_floor_non_vanishing (x : Element) (hx : norm x = 1) : norm x ≠ 0 := by
  linarith

def toReal (φ_val : ℝ) (x : Element) : ℝ :=
  (x.a : ℝ) + (x.b : ℝ) * φ_val

theorem phi_inv_sq_real_positive (φ_val : ℝ) (_h1 : 1 < φ_val) (_h2 : φ_val < 2) :
    0 < toReal φ_val phi_inv_sq := by
  unfold toReal phi_inv_sq
  push_cast
  linarith

#print axioms phi_squared_identity
#print axioms norm_mul
#print axioms norm_phi_inv_sq
#print axioms phi_inv_sq_is_unit
#print axioms unit_floor_non_vanishing
#print axioms phi_inv_sq_real_positive

end ZPhi
