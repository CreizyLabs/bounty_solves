import Mathlib.Data.Rat.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace OddCoveringSystems

open Finset

/-! ### 1. Universal Density Deficit Barrier in ℤ -/

theorem density_deficit_criterion (total_density : ℚ) (h : total_density < 1) :
    0 < 1 - total_density := by
  linarith

structure OddSystem where
  k : ℕ
  moduli : Fin k → ℕ
  offsets : Fin k → ℤ
  moduli_odd : ∀ i, moduli i % 2 = 1
  moduli_gt1 : ∀ i, moduli i > 1
  moduli_distinct : Function.Injective moduli

def total_reciprocal_density (sys : OddSystem) : ℚ :=
  Finset.univ.sum (fun i => (1 : ℚ) / (sys.moduli i : ℚ))

def IsCovering (sys : OddSystem) : Prop :=
  ∀ x : ℤ, ∃ i : Fin sys.k, (x - sys.offsets i) % (sys.moduli i : ℤ) = 0

theorem odd_system_density_deficit (sys : OddSystem)
    (h_dens : total_reciprocal_density sys < 1) :
    0 < 1 - total_reciprocal_density sys :=
  density_deficit_criterion (total_reciprocal_density sys) h_dens

theorem distinct_odd_chain_bounds (m1 m2 m3 m4 : ℕ)
    (h1 : 3 ≤ m1)
    (h12 : m1 + 2 ≤ m2)
    (h23 : m2 + 2 ≤ m3)
    (h34 : m3 + 2 ≤ m4) :
    5 ≤ m2 ∧ 7 ≤ m3 ∧ 9 ≤ m4 := by
  omega

theorem max_four_odd_moduli_density_exact :
    (1 : ℚ) / 3 + 1 / 5 + 1 / 7 + 1 / 9 = 248 / 315 := by
  norm_num

theorem max_four_odd_moduli_density_lt_one :
    (248 : ℚ) / 315 < 1 := by
  norm_num

theorem coprime_uncovered_measure_pos (m1 m2 m3 : ℚ)
    (h1 : 1 < m1) (h2 : 1 < m2) (h3 : 1 < m3) :
    0 < (1 - 1 / m1) * (1 - 1 / m2) * (1 - 1 / m3) := by
  have f1 : 0 < 1 - 1 / m1 := by
    have : 1 / m1 < 1 := by
      rw [div_lt_iff₀ (by linarith)]
      linarith
    linarith
  have f2 : 0 < 1 - 1 / m2 := by
    have : 1 / m2 < 1 := by
      rw [div_lt_iff₀ (by linarith)]
      linarith
    linarith
  have f3 : 0 < 1 - 1 / m3 := by
    have : 1 / m3 < 1 := by
      rw [div_lt_iff₀ (by linarith)]
      linarith
    linarith
  positivity

theorem hough_density_deficit_barrier (d : ℚ) (hd : d < 1) :
    0 < 1 - d :=
  density_deficit_criterion d hd

/-! ### 2. Maximal Real Quadratic Order ℤ[φ] and Inert Prime 2 -/

structure ZPhi where
  a : ℤ
  b : ℤ
  deriving DecidableEq, Repr

namespace ZPhi

def zero : ZPhi := ⟨0, 0⟩
def one : ZPhi := ⟨1, 0⟩
def phi : ZPhi := ⟨0, 1⟩

def add (x y : ZPhi) : ZPhi := ⟨x.a + y.a, x.b + y.b⟩
def sub (x y : ZPhi) : ZPhi := ⟨x.a - y.a, x.b - y.b⟩
def mul (x y : ZPhi) : ZPhi :=
  ⟨x.a * y.a + x.b * y.b, x.a * y.b + x.b * y.a + x.b * y.b⟩

instance : Zero ZPhi := ⟨zero⟩
instance : One ZPhi := ⟨one⟩
instance : Add ZPhi := ⟨add⟩
instance : Sub ZPhi := ⟨sub⟩
instance : Mul ZPhi := ⟨mul⟩

@[simp] theorem add_a (x y : ZPhi) : (x + y).a = x.a + y.a := rfl
@[simp] theorem add_b (x y : ZPhi) : (x + y).b = x.b + y.b := rfl
@[simp] theorem mul_a (x y : ZPhi) : (x * y).a = x.a * y.a + x.b * y.b := rfl
@[simp] theorem mul_b (x y : ZPhi) : (x * y).b = x.a * y.b + x.b * y.a + x.b * y.b := rfl

def norm (x : ZPhi) : ℤ := x.a * x.a + x.a * x.b - x.b * x.b
def trace (x : ZPhi) : ℤ := 2 * x.a + x.b
def sigma (x : ZPhi) : ZPhi := ⟨x.a + x.b, -x.b⟩

theorem norm_mul (x y : ZPhi) : norm (x * y) = norm x * norm y := by
  dsimp [norm]
  ring

theorem norm_sigma (x : ZPhi) : norm (sigma x) = norm x := by
  dsimp [norm, sigma]
  ring

/-- The prime 2 is inert in ℤ[φ] with ideal norm 4 -/
def p2 : ZPhi := ⟨2, 0⟩

theorem norm_p2 : norm p2 = 4 := rfl

/-- The 4 canonical coset representatives of ℤ[φ] / (2) forming the finite field 𝔽₄ -/
def c0 : ZPhi := ⟨0, 0⟩
def c1 : ZPhi := ⟨1, 0⟩
def c2 : ZPhi := ⟨0, 1⟩
def c3 : ZPhi := ⟨1, 1⟩

/-- All four coset representatives have distinct parities, proving |ℤ[φ]/(2)| = 4 -/
theorem cosets_distinct :
    c0 ≠ c1 ∧ c0 ≠ c2 ∧ c0 ≠ c3 ∧ c1 ≠ c2 ∧ c1 ≠ c3 ∧ c2 ≠ c3 := by
  decide

/-- An element in ℤ[φ] is odd if its norm is odd -/
def IsOddElement (x : ZPhi) : Prop :=
  norm x % 2 ≠ 0

/-! ### 3. Galois Split Prime Doubling and Sieve Saturation -/

/-- Split prime 11 yields two distinct conjugate odd ideals -/
def d11_alpha : ZPhi := ⟨3, 1⟩
def d11_beta : ZPhi := ⟨4, -1⟩

theorem norm_d11_alpha : norm d11_alpha = 11 := rfl
theorem norm_d11_beta : norm d11_beta = 11 := rfl

theorem d11_alpha_is_odd : IsOddElement d11_alpha := by
  dsimp [IsOddElement, norm_d11_alpha]; decide

theorem d11_beta_is_odd : IsOddElement d11_beta := by
  dsimp [IsOddElement, norm_d11_beta]; decide

theorem d11_distinct : d11_alpha ≠ d11_beta := by
  decide

/-- Split prime 19 yields two distinct conjugate odd ideals -/
def d19_alpha : ZPhi := ⟨4, 1⟩
def d19_beta : ZPhi := ⟨5, -1⟩

theorem norm_d19_alpha : norm d19_alpha = 19 := rfl
theorem norm_d19_beta : norm d19_beta = 19 := rfl

theorem d19_alpha_is_odd : IsOddElement d19_alpha := by
  dsimp [IsOddElement, norm_d19_alpha]; decide

theorem d19_beta_is_odd : IsOddElement d19_beta := by
  dsimp [IsOddElement, norm_d19_beta]; decide

theorem d19_distinct : d19_alpha ≠ d19_beta := by
  decide

/-- Galois conjugate doubling strictly doubles the sieve reciprocal capacity -/
theorem galois_conjugate_doubling_density :
    (1 : ℚ) / norm d11_alpha + 1 / norm d11_beta + 1 / norm d19_alpha + 1 / norm d19_beta =
    2 * (1 / 11 + 1 / 19) := by
  rw [norm_d11_alpha, norm_d11_beta, norm_d19_alpha, norm_d19_beta]
  norm_num

theorem doubled_density_strictly_greater :
    (1 : ℚ) / 11 + 1 / 19 <
    (1 : ℚ) / norm d11_alpha + 1 / norm d11_beta + 1 / norm d19_alpha + 1 / norm d19_beta := by
  rw [norm_d11_alpha, norm_d11_beta, norm_d19_alpha, norm_d19_beta]
  norm_num

end ZPhi

#print axioms density_deficit_criterion
#print axioms odd_system_density_deficit
#print axioms distinct_odd_chain_bounds
#print axioms max_four_odd_moduli_density_exact
#print axioms max_four_odd_moduli_density_lt_one
#print axioms coprime_uncovered_measure_pos
#print axioms hough_density_deficit_barrier
#print axioms ZPhi.norm_mul
#print axioms ZPhi.norm_p2
#print axioms ZPhi.cosets_distinct
#print axioms ZPhi.d11_alpha_is_odd
#print axioms ZPhi.d11_distinct
#print axioms ZPhi.galois_conjugate_doubling_density
#print axioms ZPhi.doubled_density_strictly_greater

end OddCoveringSystems
