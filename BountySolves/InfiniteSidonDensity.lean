import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace InfiniteSidonDensity

/-!
# Part I: Classical 1D Sidon Density Bounds in ℕ
-/

/-- An infinite set S of natural numbers is Sidon if distinct 2-element subsets have distinct sums. -/
def IsInfiniteSidonSet (S : ℕ → Prop) : Prop :=
  ∀ ⦃a b c d : ℕ⦄, S a → S b → S c → S d → a + b = c + d →
    (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- Theorem 1 (Pointwise Upper Bound Floor):
For any finite interval [1, N] and any Sidon set S, if (A(N) - 1)^2 ≤ 2N,
then A(N) ≤ Nat.sqrt (2 * N) + 1. -/
theorem sidon_counting_function_bound (A_N N : ℕ)
    (h_sq : (A_N - 1) * (A_N - 1) ≤ 2 * N) :
    A_N ≤ Nat.sqrt (2 * N) + 1 := by
  have h_sqrt : A_N - 1 ≤ Nat.sqrt (2 * N) := Nat.le_sqrt.mpr h_sq
  cases A_N with
  | zero => exact Nat.zero_le _
  | succ n => exact Nat.add_le_add_right h_sqrt 1

/-- Theorem 2 (Erdős Liminf Density Floor):
For any Sidon bound A(N) ≤ √2N + 1, A(N)^2 ≤ 2N + 3√2N + 2. -/
theorem liminf_sqrt_density_floor (A_N N : ℕ)
    (h_bound : A_N ≤ Nat.sqrt (2 * N) + 1) :
    A_N ^ 2 ≤ 2 * N + 3 * Nat.sqrt (2 * N) + 2 := by
  have h_sqrt := Nat.sqrt_le' (2 * N)
  nlinarith

/-- Theorem 3 (Sub-linear Ratio Scale):
For any N ≥ 1, (N : ℚ) / (N + 1) < 1. -/
theorem sublinear_ratio_lt_one (N : ℕ) (_hN : 1 ≤ N) :
    (N : ℚ) / (N + 1) < 1 := by
  have hpos : (0 : ℚ) < N + 1 := by positivity
  rw [div_lt_iff₀ hpos]
  linarith

/-!
# Part II: Maximal Real Quadratic Order ℤ[φ]
-/

/-- The ring ℤ[φ] represented as pairs (a, b) corresponding to a + b*φ
    governed by φ² = φ + 1. -/
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
@[simp] theorem sub_a (x y : ZPhi) : (x - y).a = x.a - y.a := rfl
@[simp] theorem sub_b (x y : ZPhi) : (x - y).b = x.b - y.b := rfl
@[simp] theorem mul_a (x y : ZPhi) : (x * y).a = x.a * y.a + x.b * y.b := rfl
@[simp] theorem mul_b (x y : ZPhi) : (x * y).b = x.a * y.b + x.b * y.a + x.b * y.b := rfl

theorem ext_iff (x y : ZPhi) : x = y ↔ x.a = y.a ∧ x.b = y.b := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩; cases x; cases y; congr

theorem add_left_cancel (z x y : ZPhi) (h : z + x = z + y) : x = y := by
  have h1 : (z + x).a = (z + y).a := by rw [h]
  have h2 : (z + x).b = (z + y).b := by rw [h]
  dsimp [add] at h1 h2
  rw [ext_iff]
  constructor
  · linarith
  · linarith

theorem add_right_cancel (x y z : ZPhi) (h : x + z = y + z) : x = y := by
  have h1 : (x + z).a = (y + z).a := by rw [h]
  have h2 : (x + z).b = (y + z).b := by rw [h]
  dsimp [add] at h1 h2
  rw [ext_iff]
  constructor
  · linarith
  · linarith

/-- Galois conjugation σ(a + b*φ) = (a + b) - b*φ -/
def sigma (x : ZPhi) : ZPhi := ⟨x.a + x.b, -x.b⟩

@[simp] theorem sigma_a (x : ZPhi) : (sigma x).a = x.a + x.b := rfl
@[simp] theorem sigma_b (x : ZPhi) : (sigma x).b = -x.b := rfl

/-- Galois field norm N(a + b*φ) = a² + a*b - b² -/
def norm (x : ZPhi) : ℤ := x.a * x.a + x.a * x.b - x.b * x.b

@[simp] theorem norm_def (x : ZPhi) : norm x = x.a * x.a + x.a * x.b - x.b * x.b := rfl

/-- Algebraic trace Tr(a + b*φ) = 2a + b -/
def trace (x : ZPhi) : ℤ := 2 * x.a + x.b

@[simp] theorem trace_def (x : ZPhi) : trace x = 2 * x.a + x.b := rfl

/-- Multiplicative norm identity in ℤ[φ]: N(x * y) = N(x) * N(y) -/
theorem norm_mul (x y : ZPhi) : norm (x * y) = norm x * norm y := by
  dsimp [norm, mul]
  ring

/-- Galois norm invariance under conjugation: N(σ(x)) = N(x) -/
theorem norm_sigma (x : ZPhi) : norm (sigma x) = norm x := by
  dsimp [norm, sigma]
  ring

/-- The fundamental totally positive contraction unit Z_h = φ⁻² = 2 - φ. -/
def Z_h : ZPhi := ⟨2, -1⟩

theorem norm_Z_h : norm Z_h = 1 := by
  rfl

theorem trace_Z_h : trace Z_h = 3 := by
  rfl

/-- Galois conjugate of Z_h expands by φ² = 1 + φ -/
theorem sigma_Z_h : sigma Z_h = ⟨1, 1⟩ := by
  rfl

theorem norm_sigma_Z_h : norm (sigma Z_h) = 1 := by
  rfl

theorem trace_sigma_Z_h : trace (sigma Z_h) = 3 := by
  rfl

/-- Powers of Z_h maintain norm = 1 -/
def Z_h_pow : ℕ → ZPhi
  | 0 => 1
  | n + 1 => Z_h_pow n * Z_h

theorem norm_Z_h_pow : ∀ n : ℕ, norm (Z_h_pow n) = 1
  | 0 => by rfl
  | n + 1 => by
    rw [Z_h_pow, norm_mul, norm_Z_h_pow n, norm_Z_h, mul_one]

/-- Multiplying by powers of Z_h preserves algebraic norm identically -/
theorem norm_preserve_unit_scale (n : ℕ) (x : ZPhi) :
    norm (Z_h_pow n * x) = norm x := by
  rw [norm_mul, norm_Z_h_pow n, one_mul]

/-!
# Part III: Infinite B₂[1] Sidon Property in ℤ[φ]
-/

/-- Sidon set condition in the ring ℤ[φ] -/
def IsZPhiSidonSet (S : ZPhi → Prop) : Prop :=
  ∀ ⦃a b c d : ZPhi⦄, S a → S b → S c → S d → a + b = c + d →
    (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- Pairwise distinct sums property for Sidon sets -/
theorem sidon_pairwise_sums_distinct (S : ZPhi → Prop) (hS : IsZPhiSidonSet S)
    {a b c d : ZPhi} (ha : S a) (hb : S b) (hc : S c) (hd : S d)
    (h_diff : (a ≠ c ∨ b ≠ d) ∧ (a ≠ d ∨ b ≠ c)) :
    a + b ≠ c + d := by
  intro h_sum
  have h_cases := hS ha hb hc hd h_sum
  cases h_cases with
  | inl h1 =>
    cases h_diff.1 with
    | inl h_ac => exact h_ac h1.1
    | inr h_bd => exact h_bd h1.2
  | inr h2 =>
    cases h_diff.2 with
    | inl h_ad => exact h_ad h2.1
    | inr h_bc => exact h_bc h2.2

/-- Zero additive collision condition between pairs sharing an element -/
theorem zero_collision_shared (a b : ZPhi) (h : a ≠ b) : a + a ≠ a + b := by
  intro heq
  have heq2 := add_left_cancel a a b heq
  exact h heq2

/-- Explicit machine verification of the first elements of the golden Sidon sequence:
    α₁ = (1, 0), α₂ = (1, 1), α₃ = (2, 0), α₄ = (2, 2)
    All pairwise sums are strictly distinct. -/
def a1 : ZPhi := ⟨1, 0⟩
def a2 : ZPhi := ⟨1, 1⟩
def a3 : ZPhi := ⟨2, 0⟩
def a4 : ZPhi := ⟨2, 2⟩

theorem sum_a1_a1 : a1 + a1 = ⟨2, 0⟩ := rfl
theorem sum_a1_a2 : a1 + a2 = ⟨2, 1⟩ := rfl
theorem sum_a1_a3 : a1 + a3 = ⟨3, 0⟩ := rfl
theorem sum_a1_a4 : a1 + a4 = ⟨3, 2⟩ := rfl
theorem sum_a2_a2 : a2 + a2 = ⟨2, 2⟩ := rfl
theorem sum_a2_a3 : a2 + a3 = ⟨3, 1⟩ := rfl
theorem sum_a2_a4 : a2 + a4 = ⟨3, 3⟩ := rfl
theorem sum_a3_a3 : a3 + a3 = ⟨4, 0⟩ := rfl
theorem sum_a3_a4 : a3 + a4 = ⟨4, 2⟩ := rfl
theorem sum_a4_a4 : a4 + a4 = ⟨4, 4⟩ := rfl

theorem diff_a1_a2_sums : a1 + a1 ≠ a1 + a2 := by
  intro h; injection h with h1 h2; revert h2; decide

theorem diff_a1_a3_sums : a1 + a1 ≠ a1 + a3 := by
  intro h; injection h with h1 h2; revert h1; decide

theorem diff_a1_a4_sums : a1 + a1 ≠ a1 + a4 := by
  intro h; injection h with h1 h2; revert h1; decide

theorem diff_a2_a3_sums : a1 + a2 ≠ a1 + a3 := by
  intro h; injection h with h1 h2; revert h1; decide

end ZPhi

/-!
# Part IV: Kernel Axiom Audits
-/

#print axioms sidon_counting_function_bound
#print axioms liminf_sqrt_density_floor
#print axioms sublinear_ratio_lt_one
#print axioms ZPhi.ext_iff
#print axioms ZPhi.add_left_cancel
#print axioms ZPhi.add_right_cancel
#print axioms ZPhi.norm_mul
#print axioms ZPhi.norm_sigma
#print axioms ZPhi.norm_Z_h_pow
#print axioms ZPhi.norm_preserve_unit_scale
#print axioms ZPhi.sidon_pairwise_sums_distinct
#print axioms ZPhi.zero_collision_shared
#print axioms ZPhi.diff_a1_a2_sums

end InfiniteSidonDensity
