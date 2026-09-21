import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Module II: ℤ[φ] Exact Algebraic Integer Rings (Solve 13)
Author: Jason Emerick (Creizy Labs)
Grounded Mathematics: Exact Diophantine Ring Arithmetic, Minimal Polynomial
Invariance, Galois Norm Multiplicativity, and the Unimodular Boundary Floor.
-/

namespace ZPhi

/-- Exact representation of elements x = a + bφ in the quadratic integer ring ℤ[φ]. -/
@[ext]
structure Element where
  a : ℤ
  b : ℤ
  deriving DecidableEq, Repr

/-- Additive identity: 0 = 0 + 0φ. -/
def zero : Element := ⟨0, 0⟩

/-- Multiplicative identity: 1 = 1 + 0φ. -/
def one : Element  := ⟨1, 0⟩

/-- The canonical golden ratio generator: φ = 0 + 1φ. -/
def phi : Element  := ⟨0, 1⟩

/-- Ring addition: (a₁ + b₁φ) + (a₂ + b₂φ) = (a₁ + a₂) + (b₁ + b₂)φ. -/
def add (x y : Element) : Element :=
  ⟨x.a + y.a, x.b + y.b⟩

/-- Additive negation: -(a + bφ) = -a + (-b)φ. -/
def neg (x : Element) : Element :=
  ⟨-x.a, -x.b⟩

/-- Ring multiplication derived from the minimal polynomial φ² = φ + 1:
    (a₁ + b₁φ)(a₂ + b₂φ) = (a₁a₂ + b₁b₂) + (a₁b₂ + b₁a₂ + b₁b₂)φ. -/
def mul (x y : Element) : Element :=
  ⟨x.a * y.a + x.b * y.b, x.a * y.b + x.b * y.a + x.b * y.b⟩

instance : Zero Element := ⟨zero⟩
instance : One Element  := ⟨one⟩
instance : Add Element  := ⟨add⟩
instance : Neg Element  := ⟨neg⟩
instance : Mul Element  := ⟨mul⟩
instance : Sub Element  := ⟨fun x y => add x (neg y)⟩

theorem add_assoc (x y z : Element) : (x + y) + z = x + (y + z) := by ext <;> ring
theorem add_comm (x y : Element) : x + y = y + x := by ext <;> ring
theorem zero_add (x : Element) : 0 + x = x := by ext <;> ring
theorem add_zero (x : Element) : x + 0 = x := by ext <;> ring
theorem add_left_neg (x : Element) : -x + x = 0 := by ext <;> ring
theorem mul_assoc (x y z : Element) : (x * y) * z = x * (y * z) := by ext <;> ring
theorem mul_comm (x y : Element) : x * y = y * x := by ext <;> ring
theorem one_mul (x : Element) : 1 * x = x := by ext <;> ring
theorem mul_one (x : Element) : x * 1 = x := by ext <;> ring
theorem left_distrib (x y z : Element) : x * (y + z) = x * y + x * z := by ext <;> ring
theorem right_distrib (x y z : Element) : (x + y) * z = x * z + y * z := by ext <;> ring

/-- Proof of the minimal polynomial identity: φ² = φ + 1 with zero drift. -/
theorem phi_squared_identity : phi * phi = phi + 1 := by
  ext <;> decide

/-- The Diophantine Galois field norm: N(a + bφ) = a² + ab - b² ∈ ℤ. -/
def norm (x : Element) : ℤ :=
  x.a^2 + x.a * x.b - x.b^2

/-- Theorem: Multiplicativity of the Diophantine Galois field norm.
    N(x * y) = N(x) * N(y) holds unconditionally across the entire ring. -/
theorem norm_mul (x y : Element) : norm (x * y) = norm x * norm y := by
  unfold norm mul
  ring

/-- The fundamental totally positive unimodular unit: φ⁻² = 2 - φ. -/
def phi_inv_sq : Element := ⟨2, -1⟩

/-- The quadratic power unit: φ² = 1 + φ. -/
def phi_sq     : Element := ⟨1, 1⟩

/-- Theorem: Unimodular Galois field norm of φ⁻² is identically +1. -/
theorem norm_phi_inv_sq : norm phi_inv_sq = 1 := by
  decide

/-- Theorem: φ⁻² is an authentic unit with two-sided inverse φ². -/
theorem phi_inv_sq_is_unit : phi_inv_sq * phi_sq = 1 ∧ phi_sq * phi_inv_sq = 1 := by
  constructor <;> decide

/-- Theorem: Invariant Unit Floor.
    A unimodular integer unit can never continuously collapse to 0 in ℤ. -/
theorem unit_floor_non_vanishing (x : Element) (hx : norm x = 1) : norm x ≠ 0 := by
  linarith

/-- Canonical realization of an element x = a + bφ in the real continuum ℝ. -/
def toReal (φ_val : ℝ) (x : Element) : ℝ :=
  (x.a : ℝ) + (x.b : ℝ) * φ_val

/-- Theorem: The physical realization of φ⁻² = 2 - φ is strictly positive
    for any real golden-ratio parameter satisfying 1 < φ < 2. -/
theorem phi_inv_sq_real_positive (φ_val : ℝ) (h1 : 1 < φ_val) (h2 : φ_val < 2) :
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
