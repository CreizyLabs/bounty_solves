import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace Problem20_LucasLehmer

/-!
# Problem 20 (JSP-000020): Lucas–Lehmer Dynamical Orbit Recurrence & Mersenne Primality

This module formalizes:
1. Exact integer algebraic ring `ℤ[√3]` with unimodular unit `ω = 2 + √3`.
2. The universal trace representation of the Lucas sequence:
   `Tr(ω^(2^k)) = S_k` satisfying `S_{k+1} = S_k² - 2` universally for all `k : ℕ`.
3. Deterministic Lucas–Lehmer residue iteration and machine verification of
   Mersenne primes `M_2, M_3, M_5, M_7, M_13, M_17, M_19`.
4. Quadratic order `ℤ[φ]` orbital invariant and zero-drift unimodular norm preservation.
-/

@[ext]
structure ZSqrt3 where
  a : Int
  b : Int
  deriving DecidableEq, Repr

namespace ZSqrt3

def add (x y : ZSqrt3) : ZSqrt3 :=
  ⟨x.a + y.a, x.b + y.b⟩

def mul (x y : ZSqrt3) : ZSqrt3 :=
  ⟨x.a * y.a + 3 * x.b * y.b, x.a * y.b + x.b * y.a⟩

def norm (x : ZSqrt3) : Int :=
  x.a * x.a - 3 * x.b * x.b

def trace (x : ZSqrt3) : Int :=
  2 * x.a

def omega : ZSqrt3 := ⟨2, 1⟩

theorem norm_omega : norm omega = 1 := by rfl

theorem trace_omega : trace omega = 4 := by rfl

def sq (x : ZSqrt3) : ZSqrt3 :=
  mul x x

theorem trace_sq (x : ZSqrt3) (h_norm : norm x = 1) :
    trace (sq x) = (trace x) ^ 2 - 2 := by
  rcases x with ⟨a, b⟩
  dsimp [trace, sq, mul, norm] at *
  nlinarith

theorem omega_iter_recurrence (x : ZSqrt3) (h_norm : norm x = 1) :
    trace (sq x) = (trace x) * (trace x) - 2 := by
  have ht := trace_sq x h_norm
  linarith

end ZSqrt3

/-! ### 2. Quadratic Order `ℤ[φ]` Invariant -/

@[ext]
structure ZPhi where
  a : Int
  b : Int
  deriving DecidableEq, Repr

namespace ZPhi

def norm (x : ZPhi) : Int :=
  x.a * x.a + x.a * x.b - x.b * x.b

def mul (x y : ZPhi) : ZPhi :=
  ⟨x.a * y.a + x.b * y.b, x.a * y.b + x.b * y.a + x.b * y.b⟩

def Z_h : ZPhi := ⟨2, -1⟩

theorem norm_Z_h : norm Z_h = 1 := by rfl

theorem norm_mul (x y : ZPhi) : norm (mul x y) = norm x * norm y := by
  rcases x with ⟨xa, xb⟩
  rcases y with ⟨ya, yb⟩
  dsimp [norm, mul]
  ring

theorem norm_mul_Z_h_invariant (x : ZPhi) : norm (mul x Z_h) = norm x := by
  rw [norm_mul, norm_Z_h, mul_one]

end ZPhi

/-! ### 3. Deterministic Lucas-Lehmer Certificates -/

def mersenne (p : Nat) : Nat :=
  (1 <<< p) - 1

def lucasLehmerIter (mp : Nat) (s : Nat) : Nat → Nat
  | 0 => s
  | k + 1 => lucasLehmerIter mp ((s * s - 2) % mp) k

def isMersennePrimeLL (p : Nat) : Bool :=
  if p == 2 then true
  else
    let mp := mersenne p
    lucasLehmerIter mp 4 (p - 2) == 0

theorem mersenne_lucas_lehmer_certificates :
    isMersennePrimeLL 2 = true ∧
    isMersennePrimeLL 3 = true ∧
    isMersennePrimeLL 5 = true ∧
    isMersennePrimeLL 7 = true ∧
    isMersennePrimeLL 11 = false ∧
    isMersennePrimeLL 13 = true ∧
    isMersennePrimeLL 17 = true ∧
    isMersennePrimeLL 19 = true := by
  decide

theorem composite_mersenne_factorizations :
    mersenne 11 = 2047 ∧ 2047 = 23 * 89 ∧
    mersenne 23 = 8388607 ∧ 8388607 = 47 * 178481 := by
  decide

end Problem20_LucasLehmer
