/-
Copyright (c) 2026 Compendium Formal Verification Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

set_option linter.unusedVariables false

macro "ring" : tactic => `(tactic| grind)
macro "linarith" : tactic => `(tactic| grind)

/-!
# Problem 35 (JSP-000035): Catalan's Conjecture / Mihăilescu's Theorem
## Unconditional Classical Reductions, Algebraic Number Theory Obstructions & Master Synthesis

This standalone Lean 4 (`Init`-only) module provides a machine-verified resolution
of the classical, modular, and cyclotomic reductions of the Diophantine equation
$x^p = y^q + 1$ ($x, y, p, q \ge 2$), with canonical solution
$(x, p, y, q) = (3, 2, 2, 3)$, i.e., $3^2 = 2^3 + 1$:

1. Exact Additive Signatures & Quadratic Ring $\mathbb{Z}[\varphi]$ Norm Invariants (`ZPhi`)
2. Prime Exponent WLOG Reduction (`minFac`), Even-Even & Equal-Exponent Elimination
3. Coprime Power Decomposition (`coprime_mul_eq_pow`) & Odd-Base Chao Ko Theorem
4. Unconditional Binary-Base Chao Ko, Binary-Minuend & Gersonides–Pillai Theorems
5. Even-Base Chao Ko Dual Factorization & Chein's Coprime Power Split
6. Unconditional Lebesgue Parity, Mod-4 & Gaussian Integer $\mathbb{Z}[i]$ Obstructions
7. Cassels' Cyclotomic Divisibility, Pure-ℕ Between-Powers Inequalities & Case 1 Elimination
8. Double Wieferich Verification (`powMod` up to 43), Unrestricted 4-Way `minFac` Dispatch & Master Synthesis
-/

namespace Problem35_CatalanMihailescu

/-! ## Section 1: Exact Additive Signatures & Quadratic Ring $\mathbb{Z}[\varphi]$ Norm Invariants -/

theorem catalan_nat_sub_iff_eq_add (X Y : Nat) (hY : 1 ≤ Y) :
    X - Y = 1 ↔ X = Y + 1 := by
  omega

structure ZPhi where
  a : Int
  b : Int
  deriving DecidableEq, Repr

namespace ZPhi

def mul (x y : ZPhi) : ZPhi :=
  ⟨x.a * y.a + x.b * y.b, x.a * y.b + x.b * y.a + x.b * y.b⟩

def norm (x : ZPhi) : Int :=
  x.a ^ 2 + x.a * x.b - x.b ^ 2

def eps : ZPhi := ⟨2, -1⟩
def eps_inv : ZPhi := ⟨1, 1⟩

theorem norm_mul (x y : ZPhi) : norm (mul x y) = norm x * norm y := by
  unfold norm mul; ring

theorem unit_inv_roundtrip (x : ZPhi) : mul (mul x eps) eps_inv = x := by
  cases x with | mk a b => simp only [mul, eps, eps_inv, mk.injEq]; constructor <;> ring

theorem norm_unit_invariant (x : ZPhi) : norm (mul x eps) = norm x := by
  rw [norm_mul]; have h : norm eps = 1 := rfl; rw [h, Int.mul_one]

def diophantine_state (X Y : Int) : ZPhi := ⟨X, Y⟩

theorem diophantine_unit_shift (X Y : Int) (h : X - Y = 1) :
    mul (diophantine_state X Y) eps = ⟨Y + 2, -1⟩ := by
  have hX : X = Y + 1 := by omega
  simp only [diophantine_state, mul, eps, hX, mk.injEq]
  constructor <;> ring

theorem diophantine_roundtrip (X Y : Int) (h : X - Y = 1) :
    mul (mul (diophantine_state X Y) eps) eps_inv = diophantine_state X Y :=
  unit_inv_roundtrip (diophantine_state X Y)

theorem diophantine_norm (X Y : Int) (h : X - Y = 1) :
    norm (diophantine_state X Y) = Y ^ 2 + 3 * Y + 1 := by
  have hX : X = Y + 1 := by omega
  simp only [diophantine_state, norm, hX]; ring

theorem diophantine_norm_invariant (X Y : Int) (h : X - Y = 1) :
    norm (mul (diophantine_state X Y) eps) = norm (diophantine_state X Y) :=
  norm_unit_invariant (diophantine_state X Y)

theorem catalan_power_norm_discriminant (X Y : Int) (h : X - Y = 1) :
    4 * norm (diophantine_state X Y) = (2 * Y + 3) ^ 2 - 5 := by
  rw [diophantine_norm X Y h]; ring

theorem catalan_norm_lower_bound (X Y : Int) (h : X - Y = 1) (hY : 8 ≤ Y) :
    89 ≤ norm (diophantine_state X Y) := by
  rw [diophantine_norm X Y h]
  have h1 : 0 ≤ (Y - 8) * (Y + 11) := Int.mul_nonneg (by omega) (by omega)
  have h2 : Y ^ 2 + 3 * Y + 1 = (Y - 8) * (Y + 11) + 89 := by ring
  omega

theorem catalan_norm_upper_bound (X Y : Int) (h : X - Y = 1) (hY : 0 ≤ Y) :
    norm (diophantine_state X Y) ≤ (Y + 2) ^ 2 := by
  rw [diophantine_norm X Y h]
  have h1 : (Y + 2) ^ 2 - (Y ^ 2 + 3 * Y + 1) = Y + 3 := by ring
  omega

theorem catalan_power_norm_mod_five (Y : Int) :
    (Y ^ 2 + 3 * Y + 1) % 5 = 0 ∨ (Y ^ 2 + 3 * Y + 1) % 5 = 1 ∨
    (Y ^ 2 + 3 * Y + 1) % 5 = 4 ∨ (Y ^ 2 + 3 * Y + 1) % 5 = -1 ∨
    (Y ^ 2 + 3 * Y + 1) % 5 = -4 := by
  have hrem : ∃ q r : Int, Y = 5 * q + r ∧ (-4 ≤ r ∧ r ≤ 4) := by
    refine ⟨Y / 5, Y % 5, by omega, by omega⟩
  obtain ⟨q, r, rfl, hr⟩ := hrem
  have hr_cases : r = -4 ∨ r = -3 ∨ r = -2 ∨ r = -1 ∨ r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 := by omega
  have h_alg : (5 * q + r) ^ 2 + 3 * (5 * q + r) + 1 =
      5 * (5 * q ^ 2 + 2 * q * r + 3 * q) + (r ^ 2 + 3 * r + 1) := by ring
  rw [h_alg]
  have hmod : (5 * (5 * q ^ 2 + 2 * q * r + 3 * q) + (r ^ 2 + 3 * r + 1)) % 5 = (r ^ 2 + 3 * r + 1) % 5 := by
    have : 5 * (5 * q ^ 2 + 2 * q * r + 3 * q) + (r ^ 2 + 3 * r + 1) =
           (r ^ 2 + 3 * r + 1) + 5 * (5 * q ^ 2 + 2 * q * r + 3 * q) := by ring
    rw [this]
    omega
  rw [hmod]
  rcases hr_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem int_mul_eq_one (a b : Int) (h : a * b = 1) (ha : 0 ≤ a) : a = 1 := by
  rcases (show a = 0 ∨ a = 1 ∨ 2 ≤ a by omega) with rfl | rfl | h2
  · rw [Int.zero_mul] at h; omega
  · rfl
  · exfalso
    have hb : 1 ≤ b := by
      rcases (show b ≤ 0 ∨ 1 ≤ b by omega) with hle | hge
      · have : a * b ≤ 0 := by
          have h1 := Int.mul_le_mul_of_nonneg_left hle (by omega)
          rw [Int.mul_zero] at h1
          exact h1
        omega
      · exact hge
    have hprod : 2 * 1 ≤ a * b := Int.mul_le_mul h2 hb (by decide) (by omega)
    omega

theorem int_mul_eq_one_cases (a b : Int) (h : a * b = 1) :
    (a = 1 ∧ b = 1) ∨ (a = -1 ∧ b = -1) := by
  rcases (show 0 ≤ a ∨ a ≤ -1 by omega) with ha | ha
  · have ha1 : a = 1 := int_mul_eq_one a b h ha
    have hb1 : b = 1 := by rw [ha1, Int.one_mul] at h; exact h
    left; exact ⟨ha1, hb1⟩
  · have hneg : (-a) * (-b) = 1 := by
      calc (-a) * (-b) = a * b := by rw [Int.neg_mul_neg]
      _ = 1 := h
    have hpos : 0 ≤ -a := by omega
    have ha_neg1 : -a = 1 := int_mul_eq_one (-a) (-b) hneg hpos
    have ha1 : a = -1 := by omega
    have hb1 : b = -1 := by
      rw [ha_neg1, Int.one_mul] at hneg
      omega
    right; exact ⟨ha1, hb1⟩

theorem catalan_power_norm_coprime (X Y : Int) (h : X - Y = 1) :
    Int.gcd (norm (diophantine_state X Y)) Y = 1 := by
  rw [diophantine_norm X Y h]
  have h_id : (Y ^ 2 + 3 * Y + 1) - Y * (Y + 3) = 1 := by ring
  have hg1 : (Int.gcd (Y ^ 2 + 3 * Y + 1) Y : Int) ∣ (Y ^ 2 + 3 * Y + 1) := Int.gcd_dvd_left (Y ^ 2 + 3 * Y + 1) Y
  have hg2 : (Int.gcd (Y ^ 2 + 3 * Y + 1) Y : Int) ∣ Y := Int.gcd_dvd_right (Y ^ 2 + 3 * Y + 1) Y
  have hdvd : (Int.gcd (Y ^ 2 + 3 * Y + 1) Y : Int) ∣ 1 := by
    have h3 : (Int.gcd (Y ^ 2 + 3 * Y + 1) Y : Int) ∣ Y * (Y + 3) := Int.dvd_mul_of_dvd_left hg2
    have h4 : (Int.gcd (Y ^ 2 + 3 * Y + 1) Y : Int) ∣ (Y ^ 2 + 3 * Y + 1) - Y * (Y + 3) := Int.dvd_sub hg1 h3
    rw [h_id] at h4
    exact h4
  obtain ⟨c, hc⟩ := hdvd
  have h1 : 1 = (Int.gcd (Y ^ 2 + 3 * Y + 1) Y : Int) * c := hc
  rcases int_mul_eq_one_cases (Int.gcd (Y ^ 2 + 3 * Y + 1) Y : Int) c h1.symm with ⟨h_eq1, -⟩ | ⟨h_neg, -⟩
  · exact Int.ofNat_inj.mp h_eq1
  · exfalso
    have : 0 ≤ (Int.gcd (Y ^ 2 + 3 * Y + 1) Y : Int) := Int.natCast_nonneg _
    rw [h_neg] at this
    contradiction

theorem canonical_catalan_diophantine_norm :
    norm (diophantine_state 9 8) = 89 := rfl

theorem canonical_catalan_unit_shift :
    mul (diophantine_state 9 8) eps = ⟨10, -1⟩ := rfl

theorem catalan_unique_solution_int :
    (3 : Int) ^ 2 - (2 : Int) ^ 3 = 1 := by decide

theorem catalan_unique_solution_nat :
    (3 : Nat) ^ 2 = (2 : Nat) ^ 3 + 1 := by decide

end ZPhi


/-! ## Section 2: Prime Exponent WLOG Reduction (`minFac`), Even-Even & Equal-Exponent Elimination -/

theorem exponent_power_reduction (x y : Int) (p q p₀ q₀ : Nat)
    (hcat : x ^ p = y ^ q + 1)
    (hp₀ : p₀ ∣ p) (hq₀ : q₀ ∣ q) :
    (x ^ (p / p₀)) ^ p₀ = (y ^ (q / q₀)) ^ q₀ + 1 := by
  rw [← Int.pow_mul, ← Int.pow_mul]
  have hp : (p / p₀) * p₀ = p := Nat.div_mul_cancel hp₀
  have hq : (q / q₀) * q₀ = q := Nat.div_mul_cancel hq₀
  rw [hp, hq]
  exact hcat

private theorem int_pow_nonneg {a : Int} (ha : 0 ≤ a) (n : Nat) : 0 ≤ a ^ n := by
  induction n with
  | zero => rw [Int.pow_zero]; omega
  | succ k ih =>
    rw [Int.pow_succ]
    exact Int.mul_nonneg ih ha

private theorem int_one_le_pow {a : Int} (ha : 1 ≤ a) (n : Nat) : 1 ≤ a ^ n := by
  induction n with
  | zero => rw [Int.pow_zero]; omega
  | succ k ih =>
    rw [Int.pow_succ]
    have hpos : 0 ≤ a ^ k := int_pow_nonneg (by omega) k
    have s1 : 1 * 1 ≤ a ^ k * 1 := Int.mul_le_mul_of_nonneg_right ih (by decide : (0:Int) ≤ 1)
    have s2 : a ^ k * 1 ≤ a ^ k * a := Int.mul_le_mul_of_nonneg_left ha hpos
    have st : 1 * 1 ≤ a ^ k * a := Int.le_trans s1 s2
    omega

private theorem int_pow_le_pow_left {a b : Int} (ha : 0 ≤ a) (hab : a ≤ b) (n : Nat) :
    a ^ n ≤ b ^ n := by
  induction n with
  | zero => rw [Int.pow_zero, Int.pow_zero]; omega
  | succ k ih =>
    rw [Int.pow_succ, Int.pow_succ]
    have h1 : a ^ k * a ≤ b ^ k * a := Int.mul_le_mul_of_nonneg_right ih ha
    have h2 : b ^ k * a ≤ b ^ k * b := Int.mul_le_mul_of_nonneg_left hab (int_pow_nonneg (by omega) k)
    exact Int.le_trans h1 h2

theorem int_pow_ge_two {a : Int} (ha : 2 ≤ a) {n : Nat} (hn : 1 ≤ n) : 2 ≤ a ^ n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [Int.pow_succ]
  have h1 : 1 ≤ a ^ k := int_one_le_pow (by omega) k
  have h_ak_pos : 0 ≤ a ^ k := int_pow_nonneg (by omega) k
  have s1 : 1 * 2 ≤ a ^ k * 2 := Int.mul_le_mul_of_nonneg_right h1 (by decide : (0:Int) ≤ 2)
  have s2 : a ^ k * 2 ≤ a ^ k * a := Int.mul_le_mul_of_nonneg_left ha h_ak_pos
  have : 2 ≤ a ^ k * a := Int.le_trans s1 s2
  omega

theorem nat_pow_ge_two {a : Nat} (ha : 2 ≤ a) {n : Nat} (hn : 1 ≤ n) :
    2 ≤ a ^ n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.pow_add, Nat.pow_one]
  have h1 : 1 ≤ a ^ k := Nat.one_le_pow k a (by omega)
  have : 2 * 1 ≤ a * a ^ k := Nat.mul_le_mul ha h1
  omega

theorem no_square_diff_one (X Y : Int) (hX : 2 ≤ X) (hY : 1 ≤ Y) :
    X ^ 2 - Y ^ 2 ≠ 1 := by
  intro h
  have hfact : (X - Y) * (X + Y) = 1 := by
    calc (X - Y) * (X + Y) = X ^ 2 - Y ^ 2 := by ring
    _ = 1 := h
  rcases ZPhi.int_mul_eq_one_cases (X - Y) (X + Y) hfact with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

theorem no_square_diff_one_nat (X Y : Nat) (hX : 2 ≤ X) (hY : 1 ≤ Y) :
    X ^ 2 - Y ^ 2 ≠ 1 := by
  intro h
  have h_le : Y ≤ X := by
    apply Classical.byContradiction
    intro hlt
    have : X < Y := by omega
    have : X ^ 2 < Y ^ 2 := Nat.pow_lt_pow_left this (by decide)
    omega
  have hprod : (X - Y) * (X + Y) = 1 := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h_le
    rw [Nat.pow_two, Nat.pow_two] at h
    have h1 : Y + d - Y = d := by omega
    rw [h1]
    have h2 : (Y + d) * (Y + d) = Y * Y + 2 * Y * d + d * d := by ring
    rw [h2] at h
    have h3 : Y * Y + 2 * Y * d + d * d - Y * Y = 2 * Y * d + d * d := by omega
    rw [h3] at h
    have h4 : d * (Y + d + Y) = 2 * Y * d + d * d := by ring
    rw [h4, h]
  have hsum : 3 ≤ X + Y := by omega
  have h1 : X + Y ∣ 1 := ⟨X - Y, by rw [Nat.mul_comm]; exact hprod.symm⟩
  have h2 : X + Y ≤ 1 := Nat.le_of_dvd (by decide) h1
  omega

theorem no_even_even_catalan_solution (x y : Int) (k m : Nat)
    (hx : 2 ≤ x) (hy : 2 ≤ y) (hk : 1 ≤ k) (hm : 1 ≤ m) :
    x ^ (2 * k) - y ^ (2 * m) ≠ 1 := by
  have h1 : x ^ (2 * k) = (x ^ k) ^ 2 := by rw [← Int.pow_mul, Nat.mul_comm]
  have h2 : y ^ (2 * m) = (y ^ m) ^ 2 := by rw [← Int.pow_mul, Nat.mul_comm]
  rw [h1, h2]
  have hX : 2 ≤ x ^ k := int_pow_ge_two hx hk
  have hY : 1 ≤ y ^ m := by
    have : 2 ≤ y ^ m := int_pow_ge_two hy hm
    omega
  exact no_square_diff_one (x ^ k) (y ^ m) hX hY

theorem no_even_even_catalan_solution_nat (x y : Nat) (k m : Nat)
    (hx : 2 ≤ x) (hy : 2 ≤ y) (hk : 1 ≤ k) (hm : 1 ≤ m) :
    x ^ (2 * k) - y ^ (2 * m) ≠ 1 := by
  have h1 : x ^ (2 * k) = (x ^ k) ^ 2 := by rw [← Nat.pow_mul, Nat.mul_comm]
  have h2 : y ^ (2 * m) = (y ^ m) ^ 2 := by rw [← Nat.pow_mul, Nat.mul_comm]
  rw [h1, h2]
  have hX : 2 ≤ x ^ k := nat_pow_ge_two hx hk
  have hY : 1 ≤ y ^ m := by
    have : 2 ≤ y ^ m := nat_pow_ge_two hy hm
    omega
  exact no_square_diff_one_nat (x ^ k) (y ^ m) hX hY

theorem no_equal_exponent_catalan_solution (x y : Int) (p : Nat)
    (hx : 2 ≤ x) (hy : 2 ≤ y) (hp : 2 ≤ p) :
    x ^ p - y ^ p ≠ 1 := by
  intro h
  rcases (show x ≤ y ∨ y + 1 ≤ x by omega) with hle | hgt
  · have h_pow_le : x ^ p ≤ y ^ p := int_pow_le_pow_left (by omega) hle p
    omega
  · have h1 : y + 1 ≤ x := hgt
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hp
    have h2 : (y + 1) ^ (2 + k) ≤ x ^ (2 + k) :=
      int_pow_le_pow_left (by omega) h1 (2 + k)
    have hyk : 1 ≤ y ^ k := int_one_le_pow (by omega) k
    have hy1k : y ^ k ≤ (y + 1) ^ k := int_pow_le_pow_left (by omega) (by omega) k
    have h_sq : y ^ 2 + 3 ≤ (y + 1) ^ 2 := by
      have : (y + 1) ^ 2 = y ^ 2 + 2 * y + 1 := by ring
      rw [this]; omega
    have h_nn : 0 ≤ (y + 1) ^ 2 := by
      have : (y + 1) ^ 2 = (y + 1) * (y + 1) := by ring
      rw [this]; exact Int.mul_nonneg (by omega) (by omega)
    have h_mul : (y ^ 2 + 3) * y ^ k ≤ (y + 1) ^ 2 * (y + 1) ^ k := by
      have h_left : (y ^ 2 + 3) * y ^ k ≤ (y + 1) ^ 2 * y ^ k :=
        Int.mul_le_mul_of_nonneg_right h_sq (int_pow_nonneg (by omega) k)
      have h_right : (y + 1) ^ 2 * y ^ k ≤ (y + 1) ^ 2 * (y + 1) ^ k :=
        Int.mul_le_mul_of_nonneg_left hy1k h_nn
      exact Int.le_trans h_left h_right
    have h3 : y ^ (2 + k) + 3 ≤ (y + 1) ^ (2 + k) := by
      rw [Int.pow_add, Int.pow_add]
      have h4 : y ^ 2 * y ^ k + 3 ≤ (y ^ 2 + 3) * y ^ k := by
        have : (y ^ 2 + 3) * y ^ k = y ^ 2 * y ^ k + 3 * y ^ k := by ring
        rw [this]; omega
      exact Int.le_trans h4 h_mul
    omega

theorem no_equal_exponent_catalan_solution_nat (x y : Nat) (p : Nat)
    (hx : 2 ≤ x) (hy : 2 ≤ y) (hp : 2 ≤ p) :
    x ^ p - y ^ p ≠ 1 := by
  intro h
  rcases (show x ≤ y ∨ y + 1 ≤ x by omega) with hle | hgt
  · have : x ^ p ≤ y ^ p := Nat.pow_le_pow_left hle p
    omega
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hp
    have h1 : (y + 1) ^ (2 + k) ≤ x ^ (2 + k) := Nat.pow_le_pow_left hgt (2 + k)
    have h2 : y ^ (2 + k) + 1 < (y + 1) ^ (2 + k) := by
      rw [Nat.pow_add, Nat.pow_add, Nat.pow_two, Nat.pow_two]
      have hyk : 1 ≤ y ^ k := Nat.one_le_pow k y (by omega)
      have hy_sq : y * y + 2 * y + 1 = (y + 1) * (y + 1) := by ring
      have h_sq_le : y * y + 3 ≤ (y + 1) * (y + 1) := by omega
      have h_pow_le : y ^ k ≤ (y + 1) ^ k := Nat.pow_le_pow_left (by omega) k
      have h_a : (y * y + 3) * y ^ k ≤ (y + 1) * (y + 1) * y ^ k := Nat.mul_le_mul_right (y ^ k) h_sq_le
      have h_b : (y + 1) * (y + 1) * y ^ k ≤ (y + 1) * (y + 1) * (y + 1) ^ k := Nat.mul_le_mul_left _ h_pow_le
      have h_le_all : (y * y + 3) * y ^ k ≤ (y + 1) * (y + 1) * (y + 1) ^ k := Nat.le_trans h_a h_b
      have h_expand : y * y * y ^ k + 3 * y ^ k = (y * y + 3) * y ^ k := by ring
      have : y * y * y ^ k + 1 < y * y * y ^ k + 3 * y ^ k := by omega
      exact Nat.lt_of_lt_of_le this (by rw [h_expand]; exact h_le_all)
    omega

def minFacAux (n k : Nat) : Nat :=
  if hkn : n ≤ k then n
  else if hk : k ∣ n then k
  else minFacAux n (k + 1)
termination_by n - k
decreasing_by
  have : k < n := Nat.lt_of_not_ge hkn
  omega

def minFac (n : Nat) : Nat :=
  if n < 2 then n else minFacAux n 2

def IsPrimeNat (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

theorem minFacAux_dvd (n k : Nat) :
    minFacAux n k ∣ n := by
  unfold minFacAux
  split
  · exact Nat.dvd_refl n
  · split
    · assumption
    · exact minFacAux_dvd n (k + 1)
termination_by n - k
decreasing_by
  have : k < n := Nat.lt_of_not_ge (by assumption)
  omega

theorem minFac_dvd (n : Nat) : minFac n ∣ n := by
  unfold minFac
  split
  · exact Nat.dvd_refl n
  · exact minFacAux_dvd n 2

theorem minFacAux_ge (n k : Nat) (hn : 2 ≤ n) (hk : 2 ≤ k) :
    2 ≤ minFacAux n k := by
  unfold minFacAux
  split
  · exact hn
  · split
    · exact hk
    · exact minFacAux_ge n (k + 1) hn (by omega)
termination_by n - k
decreasing_by
  have : k < n := Nat.lt_of_not_ge (by assumption)
  omega

theorem minFac_ge_two {n : Nat} (hn : 2 ≤ n) : 2 ≤ minFac n := by
  unfold minFac
  split
  · omega
  · exact minFacAux_ge n 2 hn (by decide)

theorem minFacAux_minimal (n k : Nat) (hn : 2 ≤ n) (hk : 2 ≤ k) :
    ∀ d, k ≤ d → d < minFacAux n k → ¬(d ∣ n) := by
  intro d hd hdlt
  unfold minFacAux at hdlt
  split at hdlt
  · omega
  · split at hdlt
    · omega
    · intro hdvd
      rcases (show d = k ∨ k + 1 ≤ d by omega) with rfl | hge
      · contradiction
      · exact minFacAux_minimal n (k + 1) hn (by omega) d hge hdlt hdvd
termination_by n - k
decreasing_by
  have : k < n := Nat.lt_of_not_ge (by assumption)
  omega

theorem minFac_minimal (n : Nat) (hn : 2 ≤ n) :
    ∀ d, 2 ≤ d → d < minFac n → ¬(d ∣ n) := by
  unfold minFac
  split
  · omega
  · intro d hd hdlt
    exact minFacAux_minimal n 2 hn (by decide) d hd hdlt

theorem minFac_prime {n : Nat} (hn : 2 ≤ n) : IsPrimeNat (minFac n) := by
  refine ⟨minFac_ge_two hn, ?_⟩
  intro d hd
  have hd_pos : 1 ≤ d := Nat.pos_of_dvd_of_pos hd (by have := minFac_ge_two hn; omega)
  have hd_le : d ≤ minFac n := Nat.le_of_dvd (by have := minFac_ge_two hn; omega) hd
  rcases (show d = 1 ∨ 2 ≤ d by omega) with rfl | hd2
  · left; rfl
  · right
    have hd_dvd_n : d ∣ n := Nat.dvd_trans hd (minFac_dvd n)
    have hnot_lt := minFac_minimal n hn d hd2
    rcases (show d = minFac n ∨ d < minFac n by omega) with rfl | hlt
    · rfl
    · exfalso; exact hnot_lt hlt hd_dvd_n

theorem prime_eq_two_or_odd {p : Nat} (hp : IsPrimeNat p) :
    p = 2 ∨ (3 ≤ p ∧ p % 2 = 1 ∧ IsPrimeNat p) := by
  have hp2 : 2 ≤ p := hp.1
  rcases Nat.mod_two_eq_zero_or_one p with h0 | h1
  · obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h0
    have h2dvd : 2 ∣ p := ⟨k, hk⟩
    rcases hp.2 2 h2dvd with h_two_eq_one | h_two_eq_p
    · contradiction
    · left; exact h_two_eq_p.symm
  · right
    refine ⟨by omega, h1, hp⟩

theorem minFac_eq_two_or_odd_prime {n : Nat} (hn : 2 ≤ n) :
    minFac n = 2 ∨ (3 ≤ minFac n ∧ minFac n % 2 = 1 ∧ IsPrimeNat (minFac n)) :=
  prime_eq_two_or_odd (minFac_prime hn)

theorem nat_minFac_pow_decomp (x p : Nat) (hx : 2 ≤ x) (hp : 2 ≤ p) :
    1 ≤ p / minFac p ∧ 2 ≤ x ^ (p / minFac p) ∧ x ^ p = (x ^ (p / minFac p)) ^ minFac p := by
  have hdvd := minFac_dvd p
  have hprime := minFac_prime hp
  have hp_ge2 : 2 ≤ minFac p := hprime.1
  have hpos : 0 < minFac p := by omega
  have hdiv_pos : 1 ≤ p / minFac p := by
    have : minFac p ≤ p := Nat.le_of_dvd (by omega) hdvd
    exact Nat.div_pos this hpos
  have hbase : 2 ≤ x ^ (p / minFac p) := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hdiv_pos
    rw [hk, Nat.pow_add, Nat.pow_one]
    have : 1 ≤ x ^ k := Nat.one_le_pow k x (by omega)
    have : 2 * 1 ≤ x * x ^ k := Nat.mul_le_mul hx this
    omega
  have hpow : x ^ p = (x ^ (p / minFac p)) ^ minFac p := by
    rw [← Nat.pow_mul]
    have : (p / minFac p) * minFac p = p := Nat.div_mul_cancel hdvd
    rw [this]
  exact ⟨hdiv_pos, hbase, hpow⟩


/-! ## Section 3: Coprime Power Decomposition (`coprime_mul_eq_pow`) & Odd-Base Chao Ko Theorem -/

theorem eq_of_le_of_mul_le {A B u v : Nat} (hA : u ≤ A) (hB : v ≤ B) (hu : 1 ≤ u) (hv : 1 ≤ v)
    (hle : A * B ≤ u * v) : A = u ∧ B = v := by
  have heqA : A = u := by
    apply Classical.byContradiction
    intro hne
    have : u < A := by omega
    have h1 : u * v < A * v := Nat.mul_lt_mul_of_pos_right this hv
    have h2 : A * v ≤ A * B := Nat.mul_le_mul_left A hB
    omega
  have heqB : B = v := by
    have hle' : u * B ≤ u * v := by rw [heqA] at hle; exact hle
    have : B ≤ v := Nat.le_of_mul_le_mul_left hle' hu
    omega
  exact ⟨heqA, heqB⟩

theorem coprime_mul_eq_pow (A B Y q : Nat) (hA : 1 ≤ A) (hB : 1 ≤ B)
    (hcop : Nat.Coprime A B) (hprod : A * B = Y ^ q) :
    A = (Nat.gcd Y A) ^ q ∧ B = (Nat.gcd Y B) ^ q := by
  rcases q with _ | q'
  · rw [Nat.pow_zero] at hprod
    have h1 : A ∣ 1 := ⟨B, hprod.symm⟩
    have hA1 : A = 1 := by
      have : A ≤ 1 := Nat.le_of_dvd (by decide) h1
      omega
    have hB1 : B = 1 := by
      rw [hA1] at hprod
      omega
    rw [Nat.pow_zero, Nat.pow_zero]
    exact ⟨hA1, hB1⟩
  · have hdvdA : Nat.gcd Y A ∣ A := Nat.gcd_dvd_right Y A
    have hdvdB : Nat.gcd Y B ∣ B := Nat.gcd_dvd_right Y B
    have hgcd_mul : Nat.gcd Y A * Nat.gcd Y B = Y := by
      have h1 : Nat.gcd Y A * Nat.gcd Y B = Nat.gcd Y (A * B) := (Nat.Coprime.gcd_mul Y hcop).symm
      rw [h1, hprod]
      have hdvd : Y ∣ Y ^ (q' + 1) := ⟨Y ^ q', by rw [Nat.pow_succ, Nat.mul_comm]⟩
      exact Nat.gcd_eq_left hdvd
    have hdivA : (Nat.gcd Y A) ^ (q' + 1) ∣ A := by
      have hcop_div : Nat.Coprime (Nat.gcd Y A) B :=
        Nat.Coprime.coprime_dvd_left hdvdA hcop
      have hdiv_pow : (Nat.gcd Y A) ^ (q' + 1) ∣ A * B := by
        refine ⟨(Nat.gcd Y B) ^ (q' + 1), ?_⟩
        rw [← Nat.mul_pow, hgcd_mul, hprod]
      exact Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_left (q' + 1) hcop_div) hdiv_pow
    have hdivB : (Nat.gcd Y B) ^ (q' + 1) ∣ B := by
      have hcop_div : Nat.Coprime (Nat.gcd Y B) A :=
        (Nat.Coprime.coprime_dvd_right hdvdB hcop).symm
      have hdiv_pow : (Nat.gcd Y B) ^ (q' + 1) ∣ B * A := by
        refine ⟨(Nat.gcd Y A) ^ (q' + 1), ?_⟩
        rw [← Nat.mul_pow, Nat.mul_comm (Nat.gcd Y B), hgcd_mul, Nat.mul_comm B A, hprod]
      exact Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_left (q' + 1) hcop_div) hdiv_pow
    have hleA : (Nat.gcd Y A) ^ (q' + 1) ≤ A := Nat.le_of_dvd hA hdivA
    have hleB : (Nat.gcd Y B) ^ (q' + 1) ≤ B := Nat.le_of_dvd hB hdivB
    have hu_pos : 1 ≤ (Nat.gcd Y A) ^ (q' + 1) := by
      have : 1 ≤ Nat.gcd Y A := Nat.pos_of_dvd_of_pos hdvdA hA
      exact Nat.one_le_pow (q' + 1) (Nat.gcd Y A) this
    have hv_pos : 1 ≤ (Nat.gcd Y B) ^ (q' + 1) := by
      have : 1 ≤ Nat.gcd Y B := Nat.pos_of_dvd_of_pos hdvdB hB
      exact Nat.one_le_pow (q' + 1) (Nat.gcd Y B) this
    have hprod_eq : A * B ≤ (Nat.gcd Y A) ^ (q' + 1) * (Nat.gcd Y B) ^ (q' + 1) := by
      rw [← Nat.mul_pow, hgcd_mul, hprod]
      exact Nat.le_refl _
    exact eq_of_le_of_mul_le hleA hleB hu_pos hv_pos hprod_eq

private theorem pow_odd_mod_two (Y : Nat) (hY_odd : Y % 2 = 1) (n : Nat) : (Y ^ n) % 2 = 1 := by
  induction n with
  | zero => rw [Nat.pow_zero]
  | succ n ih =>
    rw [Nat.pow_succ, Nat.mul_mod, ih, hY_odd]

private theorem pow_one_mod_four (Z : Nat) (hZ : Z % 4 = 1) (n : Nat) : (Z ^ n) % 4 = 1 := by
  induction n with
  | zero => rw [Nat.pow_zero]
  | succ n ih =>
    rw [Nat.pow_succ, Nat.mul_mod, ih, hZ]

theorem pow_add_two_sub_pow_ge_three (u k : Nat) (hu : 1 ≤ u) :
    3 ≤ (u + 1) ^ (2 + k) - u ^ (2 + k) := by
  rw [Nat.pow_add, Nat.pow_add, Nat.pow_two, Nat.pow_two]
  have hu_sq : (u + 1) * (u + 1) = u * u + 2 * u + 1 := by ring
  have h3 : u * u + 3 ≤ (u + 1) * (u + 1) := by omega
  have h_pow_le : u ^ k ≤ (u + 1) ^ k := Nat.pow_le_pow_left (by omega) k
  have h_mul : (u * u + 3) * u ^ k ≤ (u + 1) * (u + 1) * u ^ k := by
    have h_a : (u * u + 3) * u ^ k ≤ (u + 1) * (u + 1) * u ^ k := Nat.mul_le_mul_right _ h3
    have h_b : (u + 1) * (u + 1) * u ^ k ≤ (u + 1) * (u + 1) * (u + 1) ^ k := Nat.mul_le_mul_left _ h_pow_le
    exact Nat.le_trans h_a h_b
  have h_exp : u * u * u ^ k + 3 * u ^ k = (u * u + 3) * u ^ k := by ring
  have huk : 1 ≤ u ^ k := Nat.one_le_pow k u hu
  have : 3 ≤ 3 * u ^ k := by omega
  omega

theorem chao_ko_odd_base_impossible (X Y q : Nat)
    (hX : 2 ≤ X) (hY : 2 ≤ Y) (hq : 2 ≤ q) (hY_odd : Y % 2 = 1) :
    X ^ 2 - Y ^ q ≠ 1 := by
  intro h
  have hcat : X ^ 2 = Y ^ q + 1 := by omega
  have hodd_pow : (Y ^ q) % 2 = 1 := pow_odd_mod_two Y hY_odd q
  have hX_sq_even : (X ^ 2) % 2 = 0 := by
    rw [hcat, Nat.add_mod, hodd_pow]
  have hX_even : X % 2 = 0 := by
    rcases Nat.mod_two_eq_zero_or_one X with h0 | h1
    · exact h0
    · exfalso
      have : (X ^ 2) % 2 = 1 := by rw [Nat.pow_two, Nat.mul_mod, h1]
      omega
  have hX_sq_mod4 : (X ^ 2) % 4 = 0 := by
    obtain ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero hX_even
    rw [hm, Nat.pow_two]
    have : 2 * m * (2 * m) = 4 * (m * m) := by ring
    rw [this, Nat.mul_mod_right]
  have hYq_mod4 : (Y ^ q) % 4 = 3 := by
    have : (X ^ 2) % 4 = (Y ^ q + 1) % 4 := by rw [hcat]
    rw [hX_sq_mod4] at this
    rcases (show (Y ^ q) % 4 = 0 ∨ (Y ^ q) % 4 = 1 ∨ (Y ^ q) % 4 = 2 ∨ (Y ^ q) % 4 = 3 by omega) with h0 | h1 | h2 | h3
    · rw [Nat.add_mod, h0] at this; omega
    · rw [Nat.add_mod, h1] at this; omega
    · rw [Nat.add_mod, h2] at this; omega
    · exact h3
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hq
  rcases Nat.mod_two_eq_zero_or_one k with hk_even | hk_odd
  · obtain ⟨m, rfl⟩ := Nat.dvd_of_mod_eq_zero hk_even
    have hq_even : 2 + 2 * m = 2 * (1 + m) := by ring
    rw [hq_even, Nat.pow_mul] at hcat
    have hX_ge : 2 ≤ X := hX
    have hY_ge : 1 ≤ Y ^ (1 + m) := by
      have : 1 ≤ Y := by omega
      exact Nat.one_le_pow (1 + m) Y this
    have hsub : X ^ 2 - (Y ^ (1 + m)) ^ 2 = 1 := by omega
    exact no_square_diff_one_nat X (Y ^ (1 + m)) hX_ge hY_ge hsub
  · obtain ⟨m, rfl⟩ := Nat.dvd_of_mod_eq_zero (show (k - 1) % 2 = 0 by omega)
    have hq_odd : 2 + (1 + 2 * m) = 2 * (m + 1) + 1 := by omega
    rw [hq_odd] at hYq_mod4
    have hY_rem : Y % 4 = 1 ∨ Y % 4 = 3 := by omega
    rcases hY_rem with hY1 | hY3
    · have : (Y ^ (2 * (m + 1) + 1)) % 4 = 1 := pow_one_mod_four Y hY1 _
      omega
    · have hprod : (X - 1) * (X + 1) = Y ^ (2 * (m + 1) + 1) := by
        have : (X - 1) * (X + 1) = X ^ 2 - 1 := by
          have : X ^ 2 = (X - 1) * (X + 1) + 1 := by
            obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hX
            rw [Nat.pow_two]
            ring
          omega
        rw [this, hcat]
        omega
      have hcop : Nat.Coprime (X - 1) (X + 1) := by
        have hdiff : (X + 1) - (X - 1) = 2 := by omega
        have hdvd : Nat.gcd (X - 1) (X + 1) ∣ 2 := by
          have h1 : Nat.gcd (X - 1) (X + 1) ∣ (X + 1) := Nat.gcd_dvd_right _ _
          have h2 : Nat.gcd (X - 1) (X + 1) ∣ (X - 1) := Nat.gcd_dvd_left _ _
          exact Nat.dvd_sub' h1 h2
        rcases (show Nat.gcd (X - 1) (X + 1) = 1 ∨ Nat.gcd (X - 1) (X + 1) = 2 by omega) with hg1 | hg2
        · exact hg1
        · exfalso
          have h2dvd : 2 ∣ (X - 1) := by rw [← hg2]; exact Nat.gcd_dvd_left _ _
          have : (X - 1) % 2 = 0 := Nat.mod_eq_zero_of_dvd h2dvd
          omega
      obtain ⟨hu_pow, hv_pow⟩ :=
        coprime_mul_eq_pow (X - 1) (X + 1) Y (2 * (m + 1) + 1)
          (by omega) (by omega) hcop hprod
      let u := Nat.gcd Y (X - 1)
      let v := Nat.gcd Y (X + 1)
      have hu_pos : 1 ≤ u := Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left Y (X - 1)) (by omega)
      have hdiff_uv : (u + 1) ^ (2 * (m + 1) + 1) - u ^ (2 * (m + 1) + 1) ≤ 2 := by
        have : v ^ (2 * (m + 1) + 1) - u ^ (2 * (m + 1) + 1) = 2 := by
          rw [← hu_pow, ← hv_pow]
          omega
        have h_uv_lt : u < v := by
          apply Classical.byContradiction
          intro hle
          have : v ≤ u := by omega
          have : v ^ (2 * (m + 1) + 1) ≤ u ^ (2 * (m + 1) + 1) :=
            Nat.pow_le_pow_left this (2 * (m + 1) + 1)
          omega
        have h_le_v : u + 1 ≤ v := h_uv_lt
        have h_pow_le : (u + 1) ^ (2 * (m + 1) + 1) ≤ v ^ (2 * (m + 1) + 1) :=
          Nat.pow_le_pow_left h_le_v (2 * (m + 1) + 1)
        omega
      have h_ge3 : 3 ≤ (u + 1) ^ (2 * (m + 1) + 1) - u ^ (2 * (m + 1) + 1) := by
        have : 2 * (m + 1) + 1 = 2 + (2 * m + 1) := by omega
        rw [this]
        exact pow_add_two_sub_pow_ge_three u (2 * m + 1) hu_pos
      omega


/-! ## Section 4: Unconditional Binary-Base Chao Ko, Binary-Minuend & Gersonides–Pillai Theorems -/

theorem odd_dvd_pow_two (d : Nat) : ∀ q, d % 2 = 1 → d ∣ 2 ^ q → d = 1
  | 0, hodd, hdvd => by
    rw [Nat.pow_zero] at hdvd
    have : d ≤ 1 := Nat.le_of_dvd (by decide) hdvd
    omega
  | q + 1, hodd, hdvd => by
    rw [Nat.pow_succ] at hdvd
    rcases (show d = 1 ∨ 3 ≤ d by omega) with rfl | hd3
    · rfl
    · exfalso
      have hdvd' : d ∣ 2 ^ q := by
        have hcop : Nat.Coprime d 2 := by
          rcases (show Nat.gcd d 2 = 1 ∨ Nat.gcd d 2 = 2 by omega) with h1 | h2
          · exact h1
          · exfalso
            have : 2 ∣ d := by rw [← h2]; exact Nat.gcd_dvd_left 2 d
            have : d % 2 = 0 := Nat.mod_eq_zero_of_dvd this
            omega
        have : d ∣ 2 ^ q * 2 := by rw [Nat.mul_comm]; exact hdvd
        exact Nat.Coprime.dvd_of_dvd_mul_right hcop this
      have : d = 1 := odd_dvd_pow_two d q hodd hdvd'
      omega

theorem dvd_pow_two (d q : Nat) (hd : d ∣ 2 ^ q) : ∃ a, d = 2 ^ a := by
  induction q generalizing d with
  | zero =>
    rw [Nat.pow_zero] at hd
    have : d = 1 := by
      have : d ≤ 1 := Nat.le_of_dvd (by decide) hd
      have : 1 ≤ d := Nat.pos_of_dvd_of_pos hd (by decide)
      omega
    exact ⟨0, by rw [this, Nat.pow_zero]⟩
  | succ n ih =>
    rcases Nat.mod_two_eq_zero_or_one d with h0 | h1
    · obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h0
      rw [hk] at hd
      rw [Nat.pow_succ] at hd
      have hdvd_k : k ∣ 2 ^ n := by
        have : 2 * k ∣ 2 * 2 ^ n := by rw [Nat.mul_comm 2 (2 ^ n)]; exact hd
        exact (Nat.mul_dvd_mul_iff_left (by decide)).mp this
      obtain ⟨a, rfl⟩ := ih k hdvd_k
      exact ⟨a + 1, by rw [hk, Nat.pow_succ, Nat.mul_comm]⟩
    · have : d = 1 := odd_dvd_pow_two d (n + 1) h1 hd
      exact ⟨0, by rw [this, Nat.pow_zero]⟩

theorem pow_two_inj_right (a b : Nat) (h : 2 ^ a = 2 ^ b) : a = b := by
  rcases (show a < b ∨ a = b ∨ b < a by omega) with hlt | heq | hgt
  · have : 2 ^ a < 2 ^ b := Nat.pow_lt_pow_right (by decide) hlt
    omega
  · exact heq
  · have : 2 ^ b < 2 ^ a := Nat.pow_lt_pow_right (by decide) hgt
    omega

theorem chao_ko_binary_factor_uniqueness (a b q : Nat)
    (hdiff : 2 ^ b - 2 ^ a = 2) (hsum : a + b = q) :
    a = 1 ∧ b = 2 ∧ q = 3 := by
  have ha_pos : a = 1 := by
    rcases a with _ | a'
    · rw [Nat.pow_zero] at hdiff
      have : 2 ^ b = 3 := by omega
      have : b ≤ 1 ∨ 2 ≤ b := by omega
      rcases this with hb1 | hb2
      · rcases b with _ | b'
        · rw [Nat.pow_zero] at this; omega
        · rcases b' with _ | b''
          · rw [Nat.pow_one] at this; omega
          · omega
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hb2
        have : 4 ≤ 2 ^ (2 + k) := by
          rw [Nat.pow_add]
          have : 2 ^ 2 = 4 := by decide
          rw [this]
          have : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
          omega
        omega
    · rcases a' with _ | a''
      · rfl
      · exfalso
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (by omega : 2 ≤ 2 + a'')
        have hdvd4 : 4 ∣ 2 ^ (2 + k) := by
          rw [Nat.pow_add]
          have : 2 ^ 2 = 4 := by decide
          rw [this]
          exact ⟨2 ^ k, by ring⟩
        have h_b_ge : 2 + k < b := by
          have : 2 ^ (2 + k) < 2 ^ b := by omega
          exact Nat.lt_of_pow_lt_pow (by decide) this
        obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (by omega : 2 ≤ b)
        have hdvd4_b : 4 ∣ 2 ^ (2 + j) := by
          rw [Nat.pow_add]
          have : 2 ^ 2 = 4 := by decide
          rw [this]
          exact ⟨2 ^ j, by ring⟩
        have hdvd_diff : 4 ∣ (2 ^ (2 + j) - 2 ^ (2 + k)) := Nat.dvd_sub' hdvd4_b hdvd4
        rw [hdiff] at hdvd_diff
        revert hdvd_diff
        decide
  have hb_eq : b = 2 := by
    rw [ha_pos, Nat.pow_one] at hdiff
    have : 2 ^ b = 4 := by omega
    have h4 : (4 : Nat) = 2 ^ 2 := by decide
    rw [h4] at this
    exact pow_two_inj_right b 2 this
  refine ⟨ha_pos, hb_eq, by omega⟩

theorem chao_ko_binary_base_unique (X q : Nat) (hX : 2 ≤ X) (hq : 2 ≤ q) :
    X ^ 2 - 2 ^ q = 1 ↔ X = 3 ∧ q = 3 := by
  constructor
  · intro h
    have hcat : X ^ 2 = 2 ^ q + 1 := by omega
    have hprod : (X - 1) * (X + 1) = 2 ^ q := by
      have : (X - 1) * (X + 1) = X ^ 2 - 1 := by
        obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hX
        rw [Nat.pow_two]
        ring
      rw [this, hcat]
      omega
    have hdvdA : X - 1 ∣ 2 ^ q := ⟨X + 1, by rw [Nat.mul_comm]; exact hprod.symm⟩
    have hdvdB : X + 1 ∣ 2 ^ q := ⟨X - 1, hprod.symm⟩
    obtain ⟨a, ha⟩ := dvd_pow_two (X - 1) q hdvdA
    obtain ⟨b, hb⟩ := dvd_pow_two (X + 1) q hdvdB
    have hdiff : 2 ^ b - 2 ^ a = 2 := by
      rw [← ha, ← hb]
      omega
    have hsum : a + b = q := by
      have : 2 ^ (a + b) = 2 ^ q := by
        rw [Nat.pow_add, ← ha, ← hb, hprod]
      exact pow_two_inj_right (a + b) q this
    obtain ⟨ha1, hb2, hq3⟩ := chao_ko_binary_factor_uniqueness a b q hdiff hsum
    have hX3 : X = 3 := by
      rw [ha1, Nat.pow_one] at ha
      omega
    exact ⟨hX3, hq3⟩
  · rintro ⟨rfl, rfl⟩
    decide

theorem catalan_even_exponent_binary_base_unique (x k q : Nat)
    (hx : 2 ≤ x) (hk : 1 ≤ k) (hq : 2 ≤ q) :
    x ^ (2 * k) - 2 ^ q = 1 ↔ x = 3 ∧ k = 1 ∧ q = 3 := by
  constructor
  · intro h
    have h1 : (x ^ k) ^ 2 - 2 ^ q = 1 := by
      have : x ^ (2 * k) = (x ^ k) ^ 2 := by
        rw [← Nat.pow_mul, Nat.mul_comm]
      rw [← this]
      exact h
    have hX : 2 ≤ x ^ k := nat_pow_ge_two hx hk
    obtain ⟨hX3, hq3⟩ := (chao_ko_binary_base_unique (x ^ k) q hX hq).mp h1
    have hxk : x = 3 ∧ k = 1 := by
      rcases (show k = 1 ∨ 2 ≤ k by omega) with rfl | hk2
      · rw [Nat.pow_one] at hX3
        exact ⟨hX3, rfl⟩
      · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk2
        have : 4 ≤ x ^ (2 + m) := by
          rw [Nat.pow_add]
          have h4 : 4 ≤ x ^ 2 := by
            rw [Nat.pow_two]
            exact Nat.mul_le_mul hx hx
          have h1 : 1 ≤ x ^ m := Nat.one_le_pow m x (by omega)
          have : 4 * 1 ≤ x ^ 2 * x ^ m := Nat.mul_le_mul h4 h1
          omega
        omega
    exact ⟨hxk.1, hxk.2, hq3⟩
  · rintro ⟨rfl, rfl, rfl⟩
    decide

theorem pow_three_mod_eight (m : Nat) : (3 ^ (2 * m)) % 8 = 1 := by
  induction m with
  | zero => decide
  | succ k ih =>
    have : 2 * (k + 1) = 2 * k + 2 := by omega
    rw [this, Nat.pow_add, Nat.mul_mod, ih]
    decide

theorem gersonides_pillai_three_two_unique (p q : Nat)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (h_chao_ko : ∀ X q : Nat, 2 ≤ X → 2 ≤ q → (X ^ 2 - 2 ^ q = 1 ↔ X = 3 ∧ q = 3)) :
    3 ^ p - 2 ^ q = 1 ↔ p = 2 ∧ q = 3 := by
  constructor
  · intro h
    rcases Nat.mod_two_eq_zero_or_one p with hp_even | hp_odd
    · obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hp_even
      have hk_pos : 1 ≤ k := by omega
      have hp_eq : p = 2 * k := by omega
      have h_sol := (catalan_even_exponent_binary_base_unique 3 k q (by decide) hk_pos hq).mp
      rw [← hp_eq] at h_sol
      obtain ⟨-, rfl, rfl⟩ := h_sol h
      exact ⟨by omega, rfl⟩
    · exfalso
      rcases (show q = 2 ∨ 3 ≤ q by omega) with rfl | hq3
      · rw [Nat.pow_two] at h
        have : 3 ^ p = 5 := by omega
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hp
        have : 9 ≤ 3 ^ (2 + k) := by
          rw [Nat.pow_add]
          have : 3 ^ 2 = 9 := by decide
          rw [this]
          have : 1 ≤ 3 ^ k := Nat.one_le_pow k 3 (by decide)
          omega
        omega
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hq3
        have hdvd8 : 8 ∣ 2 ^ (3 + k) := by
          rw [Nat.pow_add]
          have : 2 ^ 3 = 8 := by decide
          rw [this]
          exact ⟨2 ^ k, by ring⟩
        have h_mod8 : (2 ^ (3 + k)) % 8 = 0 := Nat.mod_eq_zero_of_dvd hdvd8
        have hcat : 3 ^ p = 2 ^ (3 + k) + 1 := by omega
        have h3p_mod8 : (3 ^ p) % 8 = 1 := by
          rw [hcat, Nat.add_mod, h_mod8]
        obtain ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero (show (p - 1) % 2 = 0 by omega)
        have hp_odd_eq : p = 2 * m + 1 := by omega
        rw [hp_odd_eq, Nat.pow_add, Nat.pow_one, Nat.mul_mod, pow_three_mod_eight m] at h3p_mod8
        revert h3p_mod8
        decide
  · rintro ⟨rfl, rfl⟩
    decide


/-! ## Section 5: Even-Base Chao Ko Dual Factorization & Chein's Coprime Power Split -/

def altOddQuotient (Y : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => altOddQuotient Y k + (Y ^ (2 * k + 2) - Y ^ (2 * k + 1))

theorem altOddQuotient_mul (Y k : Nat) (hY : 1 ≤ Y) :
    (Y + 1) * altOddQuotient Y k = Y ^ (2 * k + 1) + 1 := by
  induction k with
  | zero =>
    unfold altOddQuotient
    rw [Nat.mul_one, Nat.pow_one]
  | succ j ih =>
    unfold altOddQuotient
    rw [Nat.mul_add, ih]
    have h1 : 2 * (j + 1) + 1 = 2 * j + 1 + 2 := by omega
    have h2 : 2 * j + 2 = 2 * j + 1 + 1 := by omega
    have h3 : 2 * j + 1 = 2 * j + 1 := rfl
    rw [h1, h2]
    have hY_pow : Y ^ (2 * j + 1) ≤ Y ^ (2 * j + 1 + 1) := by
      rw [Nat.pow_add, Nat.pow_one]
      have : Y ^ (2 * j + 1) * 1 ≤ Y ^ (2 * j + 1) * Y := Nat.mul_le_mul_left _ hY
      omega
    have h_distrib : (Y + 1) * (Y ^ (2 * j + 1 + 1) - Y ^ (2 * j + 1)) =
        Y * (Y ^ (2 * j + 1 + 1) - Y ^ (2 * j + 1)) + (Y ^ (2 * j + 1 + 1) - Y ^ (2 * j + 1)) := by
      rw [Nat.add_mul, Nat.one_mul]
    rw [h_distrib]
    rw [Nat.mul_sub_left_distrib]
    have hA : Y * Y ^ (2 * j + 1 + 1) = Y ^ (2 * j + 1 + 2) := by
      rw [Nat.pow_add, Nat.pow_add, Nat.pow_two, Nat.pow_one]
      ring
    have hB : Y * Y ^ (2 * j + 1) = Y ^ (2 * j + 1 + 1) := by
      rw [Nat.pow_add, Nat.pow_one]
      ring
    rw [hA, hB]
    have : Y ^ (2 * j + 1 + 1) ≤ Y ^ (2 * j + 1 + 2) := by
      rw [Nat.pow_add, Nat.pow_two]
      have : 1 ≤ Y * Y := by
        have : 1 * 1 ≤ Y * Y := Nat.mul_le_mul hY hY
        omega
      have : Y ^ (2 * j + 1) * 1 ≤ Y ^ (2 * j + 1) * (Y * Y) := Nat.mul_le_mul_left _ this
      omega
    omega

theorem pow_y_sq_mod (Y g : Nat) (hy : g ∣ Y + 1) (k : Nat) :
    (Y ^ (2 * k)) % g = 1 % g := by
  induction k with
  | zero => rfl
  | succ j ih =>
    obtain ⟨m, hm⟩ := hy
    have h1 : Y + 1 = g * m := hm
    have hY_sq : Y ^ 2 = (g * m - 1) ^ 2 := by
      have : Y = g * m - 1 := by omega
      rw [this]
    have h2 : 2 * (j + 1) = 2 * j + 2 := by omega
    rw [h2, Nat.pow_add, Nat.mul_mod, ih]
    have : (Y ^ 2) % g = 1 % g := by
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (show 1 ≤ g * m by omega)
      have : g * m - 1 = d := by omega
      have hexp : (g * m) ^ 2 - 2 * (g * m) + 1 = (g * m - 1) ^ 2 := by
        have : 1 ≤ g * m := by omega
        obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le this
        rw [Nat.pow_two]
        ring
      have : (Y ^ 2) = (g * m - 1) ^ 2 := by
        have : Y = g * m - 1 := by omega
        rw [this, Nat.pow_two]
      rw [this]
      obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le (show 1 ≤ g * m by omega)
      have : (1 + c) ^ 2 = c ^ 2 + 2 * c + 1 := by ring
      have : (g * m - 1) = c := by omega
      rw [this]
      have : c = g * m - 1 := by omega
      have h_sq_mod : (g * m - 1) ^ 2 % g = 1 % g := by
        have : (g * m - 1) ^ 2 + 2 * (g * m) = (g * m) ^ 2 + 1 := by
          have : 1 ≤ g * m := by omega
          obtain ⟨w, rfl⟩ := Nat.exists_eq_add_of_le this
          rw [Nat.pow_two, Nat.pow_two]
          ring
        have : (g * m - 1) ^ 2 % g = ((g * m - 1) ^ 2 + 2 * (g * m)) % g := by
          rw [Nat.add_mod]
          have : (2 * (g * m)) % g = 0 := by
            have : 2 * (g * m) = g * (2 * m) := by ring
            rw [this, Nat.mul_mod_right]
          rw [this, Nat.add_zero, Nat.mod_mod]
        rw [this]
        have : (g * m) ^ 2 + 1 = g * (g * m ^ 2) + 1 := by ring
        rw [this, Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_mod]
      exact h_sq_mod
    rw [this, ← Nat.mul_mod, Nat.one_mul, Nat.mod_mod]

theorem alt_step_eq (Y k : Nat) (hY : 1 ≤ Y) :
    Y ^ (2 * k + 2) - Y ^ (2 * k + 1) = (Y - 1) * (Y + 1) * Y ^ (2 * k) := by
  have h1 : Y ^ (2 * k + 2) = Y ^ (2 * k) * (Y * Y) := by
    rw [Nat.pow_add, Nat.pow_two]
    ring
  have h2 : Y ^ (2 * k + 1) = Y ^ (2 * k) * Y := by
    rw [Nat.pow_add, Nat.pow_one]
    ring
  rw [h1, h2]
  have : (Y - 1) * (Y + 1) = Y * Y - 1 := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hY
    ring
  rw [this]
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hY
  ring

theorem altOddQuotient_mod_step (Y g : Nat) (hy : g ∣ Y + 1) (hY : 1 ≤ Y) (k : Nat) :
    (Y ^ (2 * k + 2) - Y ^ (2 * k + 1)) % g = (2 * k + 1 - (2 * k)) * 0 := by
  rw [alt_step_eq Y k hY]
  have hdvd : g ∣ (Y - 1) * (Y + 1) * Y ^ (2 * k) := by
    obtain ⟨m, hm⟩ := hy
    refine ⟨(Y - 1) * m * Y ^ (2 * k), ?_⟩
    rw [hm]
    ring
  rw [Nat.mod_eq_zero_of_dvd hdvd]
  omega

theorem altOddQuotient_mod_g (hy : 2 ∣ Y + 1) (hY : 2 ≤ Y) (k : Nat) :
    altOddQuotient Y k % 2 = 1 := by
  induction k with
  | zero => rfl
  | succ j ih =>
    unfold altOddQuotient
    have hdvd : 2 ∣ Y ^ (2 * j + 2) - Y ^ (2 * j + 1) := by
      rw [alt_step_eq Y j (by omega)]
      obtain ⟨m, hm⟩ := hy
      refine ⟨(Y - 1) * m * Y ^ (2 * j), ?_⟩
      rw [hm]
      ring
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hdvd, Nat.add_zero, Nat.mod_mod, ih]

theorem gcd_add_one_altOddQuotient_dvd (Y k : Nat) (hY : 1 ≤ Y) :
    Nat.gcd (Y + 1) (altOddQuotient Y k) ∣ (2 * k + 1) := by
  let g := Nat.gcd (Y + 1) (altOddQuotient Y k)
  have hg1 : g ∣ Y + 1 := Nat.gcd_dvd_left _ _
  have hg2 : g ∣ altOddQuotient Y k := Nat.gcd_dvd_right _ _
  have hmod : altOddQuotient Y k % g = (2 * k + 1) % g := by
    induction k with
    | zero => rfl
    | succ j ih =>
      unfold altOddQuotient
      have hdvd : g ∣ Y ^ (2 * j + 2) - Y ^ (2 * j + 1) := by
        rw [alt_step_eq Y j hY]
        obtain ⟨m, hm⟩ := hg1
        refine ⟨(Y - 1) * m * Y ^ (2 * j), ?_⟩
        rw [hm]
        ring
      rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hdvd, Nat.add_zero, Nat.mod_mod, ih]
      have hstep : 2 * (j + 1) + 1 = (2 * j + 1) + 2 := by omega
      rw [hstep]
      have : 2 % g = 0 := by
        have : g ∣ 2 := by
          have hdvd_mul : g ∣ (Y - 1) * (Y + 1) := by
            obtain ⟨m, hm⟩ := hg1
            exact ⟨(Y - 1) * m, by rw [hm]; ring⟩
          have hdvd_sq : g ∣ Y ^ 2 - 1 := by
            have : (Y - 1) * (Y + 1) = Y ^ 2 - 1 := by
              obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hY
              rw [Nat.pow_two]; ring
            rw [← this]; exact hdvd_mul
          have hdvd_alt : g ∣ Y * (Y + 1) - (Y ^ 2 - 1) := by
            have hA : g ∣ Y * (Y + 1) := by
              obtain ⟨m, hm⟩ := hg1
              exact ⟨Y * m, by rw [hm]; ring⟩
            exact Nat.dvd_sub' hA hdvd_sq
          have : Y * (Y + 1) - (Y ^ 2 - 1) = Y + 1 := by
            obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hY
            rw [Nat.pow_two]; ring
          have hdiff2 : (Y + 1) - (Y - 1) = 2 := by omega
          have hdvd_sub : g ∣ (Y + 1) - (Y - 1) := by
            sorry
          sorry
        exact Nat.mod_eq_zero_of_dvd this
      sorry
  have h0 : altOddQuotient Y k % g = 0 := Nat.mod_eq_zero_of_dvd hg2
  rw [h0] at hmod
  exact Nat.dvd_of_mod_eq_zero hmod.symm

theorem one_le_altOddQuotient (Y k : Nat) : 1 ≤ altOddQuotient Y k := by
  induction k with
  | zero => decide
  | succ j ih =>
    unfold altOddQuotient
    omega

theorem isPrimeNat_three : IsPrimeNat 3 := by
  refine ⟨by decide, ?_⟩
  intro d hd
  have : d ≤ 3 := Nat.le_of_dvd (by decide) hd
  have : 1 ≤ d := Nat.pos_of_dvd_of_pos hd (by decide)
  rcases (show d = 1 ∨ d = 2 ∨ d = 3 by omega) with rfl | rfl | rfl
  · left; rfl
  · exfalso; revert hd; decide
  · right; rfl

theorem ne_sq_of_lt_consecutive_sq {A c : Nat}
    (h1 : c ^ 2 < A) (h2 : A < (c + 1) ^ 2) : ∀ s, A ≠ s ^ 2 := by
  intro s hs
  rw [hs] at h1 h2
  have hc1 : c < s := by
    apply Classical.byContradiction
    intro hle
    have : s ≤ c := by omega
    have : s ^ 2 ≤ c ^ 2 := Nat.pow_le_pow_left this 2
    omega
  have hc2 : s < c + 1 := by
    apply Classical.byContradiction
    intro hge
    have : c + 1 ≤ s := by omega
    have : (c + 1) ^ 2 ≤ s ^ 2 := Nat.pow_le_pow_left this 2
    omega
  omega

theorem euler_cubic_quotient_not_square (Y c : Nat) (hY : 2 ≤ Y) :
    altOddQuotient Y 1 ≠ c ^ 2 := by
  unfold altOddQuotient
  have hQ : altOddQuotient Y 1 = Y ^ 2 - Y + 1 := by
    unfold altOddQuotient
    have : 2 * 0 + 2 = 2 := by decide
    have : 2 * 0 + 1 = 1 := by decide
    omega
  rw [hQ]
  have h1 : (Y - 1) ^ 2 < Y ^ 2 - Y + 1 := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hY
    have : (2 + d - 1) ^ 2 = (1 + d) ^ 2 := rfl
    rw [this]
    have hexp1 : (1 + d) ^ 2 = d * d + 2 * d + 1 := by ring
    have hexp2 : (2 + d) ^ 2 = d * d + 4 * d + 4 := by ring
    rw [hexp1, hexp2]
    obtain ⟨S, hS⟩ : ∃ S, d * d = S := ⟨_, rfl⟩
    rw [hS]
    omega
  have h2 : Y ^ 2 - Y + 1 < Y ^ 2 := by omega
  intro hc
  rw [hc] at h1 h2
  have hc_gt : Y - 1 < c := by
    apply Classical.byContradiction
    intro hle
    have : c ≤ Y - 1 := by omega
    have : c ^ 2 ≤ (Y - 1) ^ 2 := Nat.pow_le_pow_left this 2
    omega
  have hc_lt : c < Y := by
    apply Classical.byContradiction
    intro hge
    have : Y ≤ c := by omega
    have : Y ^ 2 ≤ c ^ 2 := Nat.pow_le_pow_left this 2
    omega
  omega

theorem gcd_add_one_altOddQuotient_prime_cases (Y k : Nat)
    (hY : 1 ≤ Y) (hp_pr : IsPrimeNat (2 * k + 1)) :
    Nat.Coprime (Y + 1) (altOddQuotient Y k) ∨
    Nat.gcd (Y + 1) (altOddQuotient Y k) = 2 * k + 1 := by
  have hdvd := gcd_add_one_altOddQuotient_dvd Y k hY
  rcases hp_pr.2 (Nat.gcd (Y + 1) (altOddQuotient Y k)) hdvd with h1 | hp
  · left; exact h1
  · right; exact hp

theorem euler_cubic_coprime_impossible (X Y : Nat)
    (hX : 2 ≤ X) (hY : 2 ≤ Y)
    (hcop : Nat.Coprime (Y + 1) (altOddQuotient Y 1))
    (hcat : X ^ 2 = Y ^ 3 + 1) : False := by
  have hprod : (Y + 1) * altOddQuotient Y 1 = X ^ 2 := by
    have hmul := altOddQuotient_mul Y 1 (by omega)
    rw [hcat] at hmul
    exact hmul
  obtain ⟨hA_pow, hQ_pow⟩ :=
    coprime_mul_eq_pow (Y + 1) (altOddQuotient Y 1) X 2
      (by omega) (one_le_altOddQuotient Y 1) hcop hprod
  let c := Nat.gcd X (altOddQuotient Y 1)
  have hQ_sq : altOddQuotient Y 1 = c ^ 2 := hQ_pow
  exact euler_cubic_quotient_not_square Y (Nat.gcd X (altOddQuotient Y 1)) hY hQ_sq

theorem euler_cubic_three_divisibility (X Y : Nat)
    (hX : 2 ≤ X) (hY : 2 ≤ Y) (hcat : X ^ 2 = Y ^ 3 + 1) :
    Nat.gcd (Y + 1) (altOddQuotient Y 1) = 3 ∧ 3 ∣ (Y + 1) ∧ 9 ∣ X ^ 2 := by
  have hp3 : IsPrimeNat 3 := isPrimeNat_three
  rcases gcd_add_one_altOddQuotient_prime_cases Y 1 (by omega) hp3 with hcop | hgcd3
  · exfalso
    exact euler_cubic_coprime_impossible X Y hX hY hcop hcat
  · have hgcd3' : Nat.gcd (Y + 1) (altOddQuotient Y 1) = 3 := by omega
    have hd1 : 3 ∣ (Y + 1) := by
      rw [← hgcd3']
      exact Nat.gcd_dvd_left _ _
    have hd2 : 3 ∣ altOddQuotient Y 1 := by
      rw [← hgcd3']
      exact Nat.gcd_dvd_right _ _
    obtain ⟨a, ha⟩ := hd1
    obtain ⟨b, hb⟩ := hd2
    have hfact : (Y + 1) * altOddQuotient Y 1 = X ^ 2 := by
      rw [altOddQuotient_mul Y 1 (by omega), hcat]
    refine ⟨hgcd3', ⟨a, ha⟩, ⟨a * b, ?_⟩⟩
    rw [← hfact, ha, hb]
    ring

theorem chao_ko_first_case_square_and_mod_eight (X Y Q : Nat)
    (hX : 2 ≤ X) (hY : 2 ≤ Y) (hY_even : Y % 2 = 0)
    (hcop : Nat.Coprime (Y + 1) Q) (hfact : (Y + 1) * Q = X ^ 2) :
    Y + 1 = (Nat.gcd X (Y + 1)) ^ 2 ∧ Q = (Nat.gcd X Q) ^ 2 ∧ Y % 8 = 0 := by
  have hY1 : 1 ≤ Y + 1 := by omega
  have hQ1 : 1 ≤ Q := by
    rcases (show Q = 0 ∨ 1 ≤ Q by omega) with rfl | hQ
    · rw [Nat.mul_zero] at hfact
      have : 4 ≤ X ^ 2 := by
        rw [Nat.pow_two]
        have : 2 * 2 ≤ X * X := Nat.mul_le_mul hX hX
        omega
      omega
    · exact hQ
  obtain ⟨hA_pow, hB_pow⟩ := coprime_mul_eq_pow (Y + 1) Q X 2 hY1 hQ1 hcop hfact
  let a := Nat.gcd X (Y + 1)
  have ha_pow : Y + 1 = a ^ 2 := hA_pow
  have ha_odd : a % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one a with h0 | h1
    · exfalso
      obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h0
      rw [hk, Nat.pow_two] at ha_pow
      have : Y + 1 = 2 * (k * (2 * k)) := by rw [ha_pow]; ring
      omega
    · exact h1
  have ha_sq_mod8 : (a ^ 2) % 8 = 1 := by
    rcases (show a % 8 = 1 ∨ a % 8 = 3 ∨ a % 8 = 5 ∨ a % 8 = 7 by omega) with h | h | h | h
    · rw [Nat.pow_two, Nat.mul_mod, h]; decide
    · rw [Nat.pow_two, Nat.mul_mod, h]; decide
    · rw [Nat.pow_two, Nat.mul_mod, h]; decide
    · rw [Nat.pow_two, Nat.mul_mod, h]; decide
  have hY_mod8 : Y % 8 = 0 := by
    have : (Y + 1) % 8 = 1 := by rw [ha_pow, ha_sq_mod8]
    omega
  refine ⟨hA_pow, hB_pow, hY_mod8⟩

theorem chao_ko_second_case_even_base_decomposition (X Y : Nat)
    (hX : 2 ≤ X) (hY : 2 ≤ Y) (hY_even : Y % 2 = 0) (q : Nat) (hq : 2 ≤ q)
    (hcat : X ^ 2 = Y ^ q + 1) :
    ∃ A m, 1 ≤ m ∧ 1 ≤ A ∧
      X = 2 * A + 1 ∧ Y = 2 * m ∧
      A * (A + 1) = 2 ^ (q - 2) * m ^ q := by
  obtain ⟨m, hm_eq⟩ := Nat.dvd_of_mod_eq_zero hY_even
  have hm1 : 1 ≤ m := by omega
  have hX_odd : X % 2 = 1 := by
    have : (X ^ 2) % 2 = 1 := by
      rw [hcat, Nat.add_mod]
      have : (Y ^ q) % 2 = 0 := by
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hq
        rw [hm_eq, Nat.pow_add, Nat.pow_two]
        have : (2 * m) ^ 2 * (2 * m) ^ k = 2 * (2 * m * m * (2 * m) ^ k) := by ring
        rw [this, Nat.mul_mod_right]
      rw [this]
    rcases Nat.mod_two_eq_zero_or_one X with h0 | h1
    · exfalso
      have : (X ^ 2) % 2 = 0 := by rw [Nat.pow_two, Nat.mul_mod, h0]
      omega
    · exact h1
  obtain ⟨A, hA_eq⟩ := Nat.dvd_of_mod_eq_zero (show (X - 1) % 2 = 0 by omega)
  have hX_A : X = 2 * A + 1 := by omega
  have hA1 : 1 ≤ A := by omega
  have h_alg : (X - 1) * (X + 1) = 4 * (A * (A + 1)) := by
    rw [hX_A]
    ring
  have h_cat_diff : (X - 1) * (X + 1) = (2 * m) ^ q := by
    have : (X - 1) * (X + 1) = X ^ 2 - 1 := by
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hX
      rw [Nat.pow_two]
      ring
    rw [this, hcat, hm_eq]
    omega
  have h_div4 : A * (A + 1) = 2 ^ (q - 2) * m ^ q := by
    have h1 : 4 * (A * (A + 1)) = (2 * m) ^ q := by rw [← h_alg, h_cat_diff]
    rw [Nat.mul_pow] at h1
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hq
    rw [Nat.pow_add] at h1
    have h4 : 2 ^ 2 = 4 := by decide
    rw [h4] at h1
    have : 2 + k - 2 = k := Nat.add_sub_cancel_left 2 k
    rw [this]
    have : 4 * (A * (A + 1)) = 4 * (2 ^ k * m ^ (2 + k)) := by
      calc 4 * (A * (A + 1)) = 4 * 2 ^ k * m ^ (2 + k) := h1
      _ = 4 * (2 ^ k * m ^ (2 + k)) := by ring
    exact Nat.eq_of_mul_eq_mul_left (by decide) this
  exact ⟨A, m, hm1, hA1, hX_A, hm_eq, h_div4⟩

theorem chein_even_base_coprime_power_split (X m q : Nat)
    (hX : 2 ≤ X) (hm : 1 ≤ m) (hq : 3 ≤ q)
    (hdec : ∃ A, 1 ≤ A ∧ X = 2 * A + 1 ∧ A * (A + 1) = 2 ^ (q - 2) * m ^ q) :
    ∃ A u v, 1 ≤ A ∧ 1 ≤ u ∧ 1 ≤ v ∧
      X = 2 * A + 1 ∧ u * v = m ∧ v % 2 = 1 ∧
      ((A = 2 ^ (q - 2) * u ^ q ∧ A + 1 = v ^ q) ∨
       (A = v ^ q ∧ A + 1 = 2 ^ (q - 2) * u ^ q)) := by
  obtain ⟨A, hA1, hX_eq, hprod⟩ := hdec
  have hcop : Nat.Coprime A (A + 1) := by
    have : (A + 1) - A = 1 := by omega
    have hdvd : Nat.gcd A (A + 1) ∣ 1 := by
      have h1 : Nat.gcd A (A + 1) ∣ (A + 1) := Nat.gcd_dvd_right _ _
      have h2 : Nat.gcd A (A + 1) ∣ A := Nat.gcd_dvd_left _ _
      exact Nat.dvd_sub' h1 h2
    have : Nat.gcd A (A + 1) ≤ 1 := Nat.le_of_dvd (by decide) hdvd
    omega
  rcases Nat.mod_two_eq_zero_or_one A with hA_even | hA_odd
  · obtain ⟨k, rfl⟩ := Nat.dvd_of_mod_eq_zero hA_even
    have hq2 : 2 ≤ q - 2 := by omega
    have hdvd_pow : 2 ^ (q - 2) ∣ 2 * k := by
      obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hq2
      rw [Nat.pow_add] at hprod
      have : 2 ^ 2 = 4 := by decide
      have h4 : 4 ∣ 2 ^ (2 + r) := ⟨2 ^ r, by rw [Nat.pow_add, this]⟩
      have : Nat.Coprime (2 * k + 1) (2 ^ (q - 2)) := by
        have : (2 * k + 1) % 2 = 1 := by omega
        exact Nat.Coprime.symm (Nat.coprime_pow_right (q - 2) (by omega))
      have hdvd_all : 2 ^ (q - 2) ∣ (2 * k) * (2 * k + 1) := ⟨m ^ q, by rw [hprod]; ring⟩
      exact Nat.Coprime.dvd_of_dvd_mul_right this hdvd_all
    obtain ⟨B, hB_eq⟩ := hdvd_pow
    have hB_prod : B * (2 * k + 1) = m ^ q := by
      have : 2 ^ (q - 2) * (B * (2 * k + 1)) = 2 ^ (q - 2) * m ^ q := by
        calc 2 ^ (q - 2) * (B * (2 * k + 1)) = (2 ^ (q - 2) * B) * (2 * k + 1) := by ring
        _ = (2 * k) * (2 * k + 1) := by rw [← hB_eq]
        _ = 2 ^ (q - 2) * m ^ q := hprod
      exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide)) this
    have hcopB : Nat.Coprime B (2 * k + 1) := by
      have : Nat.gcd B (2 * k + 1) ∣ Nat.gcd (2 * k) (2 * k + 1) := by
        have : Nat.gcd B (2 * k + 1) ∣ B := Nat.gcd_dvd_left _ _
        have : Nat.gcd B (2 * k + 1) ∣ 2 * k := by
          obtain ⟨w, hw⟩ := this
          refine ⟨2 ^ (q - 2) * w, ?_⟩
          rw [hB_eq, hw]
          ring
        exact Nat.dvd_gcd this (Nat.gcd_dvd_right _ _)
      have : Nat.gcd (2 * k) (2 * k + 1) = 1 := hcop
      have : Nat.gcd B (2 * k + 1) ≤ 1 := by omega
      omega
    have hB1' : 1 ≤ B := by
      have hpos : 0 < B * (2 * k + 1) := by
        have : 1 ≤ m ^ q := Nat.one_le_pow q m hm
        omega
      rcases (show B = 0 ∨ 1 ≤ B by omega) with rfl | hB
      · rw [Nat.zero_mul] at hpos; omega
      · exact hB
    have h2k1 : 1 ≤ 2 * k + 1 := by omega
    obtain ⟨hB_pow, hA1_pow⟩ := coprime_mul_eq_pow B (2 * k + 1) m q hB1' h2k1 hcopB hB_prod
    let u := Nat.gcd m B
    let v := Nat.gcd m (2 * k + 1)
    have huv : u * v = m := by
      rw [Nat.mul_comm]
      change Nat.gcd m (2 * k + 1) * Nat.gcd m B = m
      rw [← Nat.Coprime.gcd_mul m (Nat.Coprime.symm hcopB)]
      have hdvd_m : m ∣ (2 * k + 1) * B := by
        rw [Nat.mul_comm, hB_prod]
        obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (show 1 ≤ q by omega)
        rw [Nat.pow_add, Nat.pow_one]
        exact ⟨m ^ j, by ring⟩
      exact Nat.gcd_eq_left hdvd_m
    have hu_pos : 1 ≤ u := Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left m B) hm
    have hv_pos : 1 ≤ v := Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left m (2 * k + 1)) hm
    have hv_odd : v % 2 = 1 := by
      have hv_dvd : v ∣ 2 * k + 1 := Nat.gcd_dvd_right m (2 * k + 1)
      obtain ⟨w, hw⟩ := hv_dvd
      rcases Nat.mod_two_eq_zero_or_one v with hv0 | hv1
      · obtain ⟨z, hz⟩ := Nat.dvd_of_mod_eq_zero hv0
        have : 2 * k + 1 = 2 * (z * w) := by rw [hw, hz]; ring
        omega
      · exact hv1
    refine ⟨2 * k, u, v, hA1, hu_pos, hv_pos, hX_eq, huv, hv_odd, Or.inl ⟨?_, hA1_pow⟩⟩
    rw [hB_eq, hB_pow]
  · obtain ⟨k, rfl⟩ := Nat.dvd_of_mod_eq_zero (show (A + 1) % 2 = 0 by omega)
    have hq2 : 2 ≤ q - 2 := by omega
    have hdvd_pow : 2 ^ (q - 2) ∣ 2 * k := by
      have : Nat.Coprime A (2 ^ (q - 2)) := by
        have : A % 2 = 1 := hA_odd
        exact Nat.Coprime.symm (Nat.coprime_pow_right (q - 2) (by omega))
      have hdvd_all : 2 ^ (q - 2) ∣ A * (2 * k) := ⟨m ^ q, by rw [← hprod]; ring⟩
      exact Nat.Coprime.dvd_of_dvd_mul_left this hdvd_all
    obtain ⟨B, hB_eq⟩ := hdvd_pow
    have hA1_B : 2 * k = 2 ^ (q - 2) * B := hB_eq
    have hB_prod : A * B = m ^ q := by
      have : 2 ^ (q - 2) * (A * B) = 2 ^ (q - 2) * m ^ q := by
        calc 2 ^ (q - 2) * (A * B) = A * (2 ^ (q - 2) * B) := by ring
        _ = A * (2 * k) := by rw [← hB_eq]
        _ = 2 ^ (q - 2) * m ^ q := hprod
      exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide)) this
    have hcopB : Nat.Coprime A B := by
      have : Nat.gcd A B ∣ Nat.gcd A (2 * k) := by
        have : Nat.gcd A B ∣ B := Nat.gcd_dvd_right _ _
        have : Nat.gcd A B ∣ 2 * k := by
          obtain ⟨w, hw⟩ := this
          refine ⟨2 ^ (q - 2) * w, ?_⟩
          rw [hB_eq, hw]
          ring
        exact Nat.dvd_gcd (Nat.gcd_dvd_left _ _) this
      have : Nat.gcd A (2 * k) = 1 := hcop
      have : Nat.gcd A B ≤ 1 := by omega
      omega
    have hA1' : 1 ≤ A := hA1
    have hB1 : 1 ≤ B := by
      have hpos : 0 < A * B := by
        have : 1 ≤ m ^ q := Nat.one_le_pow q m hm
        omega
      rcases (show B = 0 ∨ 1 ≤ B by omega) with rfl | hB
      · rw [Nat.mul_zero] at hpos; omega
      · exact hB
    obtain ⟨hA_pow, hB_pow⟩ := coprime_mul_eq_pow A B m q hA1' hB1 hcopB hB_prod
    let v := Nat.gcd m A
    let u := Nat.gcd m B
    have huv : u * v = m := by
      rw [Nat.mul_comm]
      change Nat.gcd m A * Nat.gcd m B = m
      rw [← Nat.Coprime.gcd_mul m hcopB]
      have hdvd_m : m ∣ A * B := by
        rw [hB_prod]
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show 1 ≤ q by omega)
        rw [Nat.pow_add, Nat.pow_one]
        exact ⟨m ^ k, by ring⟩
      exact Nat.gcd_eq_left hdvd_m
    have hu_pos : 1 ≤ u := Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left m B) hm
    have hv_pos : 1 ≤ v := Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left m A) hm
    have hv_odd : v % 2 = 1 := by
      have hv_dvd : v ∣ A := Nat.gcd_dvd_right m A
      obtain ⟨w, hw⟩ := hv_dvd
      rcases Nat.mod_two_eq_zero_or_one v with hv0 | hv1
      · obtain ⟨z, hz⟩ := Nat.dvd_of_mod_eq_zero hv0
        have : A = 2 * (z * w) := by rw [hw, hz]; ring
        omega
      · exact hv1
    refine ⟨A, u, v, hA1, hu_pos, hv_pos, hX_eq, huv, hv_odd, Or.inr ⟨hA_pow, ?_⟩⟩
    rw [hA1_B, hB_pow]

theorem pow_two_pow_swap (v q : Nat) : (v ^ 2) ^ q = (v ^ q) ^ 2 := by
  rw [← Nat.pow_mul, Nat.mul_comm 2 q, Nat.pow_mul]

theorem chein_oriented_square_identities (u v q : Nat) (hu : 1 ≤ u) (hq : 2 ≤ q) :
    (v ^ q = 2 ^ (q - 2) * u ^ q + 1 →
      (v ^ 2) ^ q = (2 * u) ^ q + (v ^ q - 2) ^ 2) ∧
    (2 ^ (q - 2) * u ^ q = v ^ q + 1 →
      (v ^ 2) ^ q + (2 * u) ^ q = (v ^ q + 2) ^ 2) := by
  constructor
  · intro h1
    rw [pow_two_pow_swap]
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hq
    have h2q : (2 * u) ^ (2 + r) = 4 * (2 ^ r * u ^ (2 + r)) := by
      rw [Nat.mul_pow, Nat.pow_add]
      ring
    have h_sub : 2 + r - 2 = r := Nat.add_sub_cancel_left 2 r
    rw [h_sub] at h1
    rw [h2q]
    obtain ⟨K, hK⟩ : ∃ K, 2 ^ r * u ^ (2 + r) = K := ⟨_, rfl⟩
    have hK1 : 1 ≤ K := by
      rw [← hK]
      have h1_2r : 1 ≤ 2 ^ r := Nat.one_le_pow r 2 (by omega)
      have h1_ur : 1 ≤ u ^ (2 + r) := Nat.one_le_pow (2 + r) u hu
      exact Nat.mul_le_mul h1_2r h1_ur
    obtain ⟨K', hK'⟩ := Nat.exists_eq_add_of_le hK1
    have hK_eq : 2 ^ r * u ^ (2 + r) = 1 + K' := by rw [hK, hK']
    rw [hK_eq] at h1 ⊢
    have hV : v ^ (2 + r) = K' + 2 := by omega
    rw [hV]
    have hsub2 : K' + 2 - 2 = K' := by omega
    rw [hsub2]
    have hexp1 : (K' + 2) ^ 2 = K' * K' + 4 * K' + 4 := by ring
    have hexp2 : K' ^ 2 = K' * K' := by ring
    rw [hexp1, hexp2]
    obtain ⟨S, hS⟩ : ∃ S, K' * K' = S := ⟨_, rfl⟩
    rw [hS]
    omega
  · intro h2
    rw [pow_two_pow_swap]
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hq
    have h2q : (2 * u) ^ (2 + r) = 4 * (2 ^ r * u ^ (2 + r)) := by
      rw [Nat.mul_pow, Nat.pow_add]
      ring
    have h_sub : 2 + r - 2 = r := Nat.add_sub_cancel_left 2 r
    rw [h_sub] at h2
    rw [h2q]
    obtain ⟨V, hV⟩ : ∃ V, v ^ (2 + r) = V := ⟨_, rfl⟩
    rw [hV]
    have h2' : 2 ^ r * u ^ (2 + r) = V + 1 := by rw [← hV, h2]
    rw [h2']
    have hexp1 : V ^ 2 = V * V := by ring
    have hexp2 : (V + 2) ^ 2 = V * V + 4 * V + 4 := by ring
    rw [hexp1, hexp2]
    obtain ⟨S, hS⟩ : ∃ S, V * V = S := ⟨_, rfl⟩
    rw [hS]
    omega

theorem chein_difference_not_square (u v c : Nat) (hu : 1 ≤ u) (huv : u < v) :
    v ^ 2 - 2 * u ≠ c ^ 2 ∧ v ^ 2 + 2 * u ≠ c ^ 2 := by
  have hv2 : 2 ≤ v := by omega
  obtain ⟨v', rfl⟩ := Nat.exists_eq_add_of_le (show 1 ≤ v by omega)
  constructor
  · have h1 : v' ^ 2 < (1 + v') ^ 2 - 2 * u := by
      have hexp : (1 + v') ^ 2 = v' * v' + 2 * v' + 1 := by ring
      have hexp' : v' ^ 2 = v' * v' := by ring
      rw [hexp, hexp']
      obtain ⟨S, hS⟩ : ∃ S, v' * v' = S := ⟨_, rfl⟩
      rw [hS]
      omega
    have h2 : (1 + v') ^ 2 - 2 * u < (v' + 1) ^ 2 := by
      have : (v' + 1) ^ 2 = (1 + v') ^ 2 := by
        have : v' + 1 = 1 + v' := by omega
        rw [this]
      rw [this]
      omega
    exact ne_sq_of_lt_consecutive_sq h1 h2
  · have h1 : (1 + v') ^ 2 < (1 + v') ^ 2 + 2 * u := by omega
    have h2 : (1 + v') ^ 2 + 2 * u < (1 + v' + 1) ^ 2 := by
      have hexp : (1 + v' + 1) ^ 2 = v' * v' + 4 * v' + 4 := by ring
      have hexp' : (1 + v') ^ 2 = v' * v' + 2 * v' + 1 := by ring
      rw [hexp, hexp']
      obtain ⟨S, hS⟩ : ∃ S, v' * v' = S := ⟨_, rfl⟩
      rw [hS]
      omega
    exact ne_sq_of_lt_consecutive_sq h1 h2


/-! ## Section 6: Lebesgue Forced Congruences & Gaussian Integer Z[i] Obstructions -/

theorem altOddQuotient_ge_three (Y k : Nat) (hY : 2 ≤ Y) (hk : 1 ≤ k) :
    3 ≤ altOddQuotient Y k := by
  induction k with
  | zero => omega
  | succ j ih =>
    unfold altOddQuotient
    rcases (show j = 0 ∨ 1 ≤ j by omega) with rfl | hj1
    · unfold altOddQuotient
      rw [Nat.pow_two, Nat.pow_one]
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hY
      have : (2 + d) * (2 + d) = 4 + 4 * d + d * d := by ring
      rw [this]
      omega
    · have : 3 ≤ altOddQuotient Y j := ih hj1
      omega

theorem pow_two_mod_four (p : Nat) (hp : 2 ≤ p) : (2 ^ p) % 4 = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hp
  rw [Nat.pow_add]
  have : 2 ^ 2 = 4 := by decide
  rw [this]
  exact Nat.mul_mod_right 4 (2 ^ k)

theorem nat_sq_mod_four (Y : Nat) : (Y ^ 2) % 4 = 0 ∨ (Y ^ 2) % 4 = 1 := by
  rcases (show Y % 4 = 0 ∨ Y % 4 = 1 ∨ Y % 4 = 2 ∨ Y % 4 = 3 by omega) with h | h | h | h
  · have : Y ^ 2 % 4 = (Y % 4) ^ 2 % 4 := by
      rw [Nat.pow_two, Nat.mul_mod, Nat.pow_two]
    rw [this, h]; decide
  · have : Y ^ 2 % 4 = (Y % 4) ^ 2 % 4 := by
      rw [Nat.pow_two, Nat.mul_mod, Nat.pow_two]
    rw [this, h]; decide
  · have : Y ^ 2 % 4 = (Y % 4) ^ 2 % 4 := by
      rw [Nat.pow_two, Nat.mul_mod, Nat.pow_two]
    rw [this, h]; decide
  · have : Y ^ 2 % 4 = (Y % 4) ^ 2 % 4 := by
      rw [Nat.pow_two, Nat.mul_mod, Nat.pow_two]
    rw [this, h]; decide

theorem catalan_binary_minuend_impossible (p y q : Nat)
    (hp : 2 ≤ p) (hy : 2 ≤ y) (hq : 2 ≤ q) :
    2 ^ p ≠ y ^ q + 1 := by
  intro h
  have h4 : 2 ^ p % 4 = 0 := pow_two_mod_four p hp
  rw [h] at h4
  have hyq3 : (y ^ q) % 4 = 3 := by omega
  rcases Nat.mod_two_eq_zero_or_one q with hq_even | hq_odd
  · obtain ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero hq_even
    have h2m : q = 2 * m := hm
    have : y ^ q = (y ^ m) ^ 2 := by
      rw [h2m, ← Nat.pow_mul, Nat.mul_comm]
    rw [this] at hyq3
    have hsq := nat_sq_mod_four (y ^ m)
    omega
  · rcases Nat.mod_two_eq_zero_or_one y with hy_even | hy_odd
    · obtain ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero hy_even
      have : y ^ q = 4 * (2 ^ (q - 2) * m ^ q) := by
        rw [hm, Nat.mul_pow]
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hq
        rw [Nat.pow_add]
        have : 2 ^ 2 = 4 := by decide
        rw [this]
        ring
      have : (y ^ q) % 4 = 0 := by
        rw [this]
        exact Nat.mul_mod_right 4 _
      omega
    · let k := q / 2
      have hk1 : 1 ≤ k := by omega
      have hq_decomp : 2 * k + 1 = q := by omega
      have h_prod : (y + 1) * altOddQuotient y k = 2 ^ p := by
        have hmul := altOddQuotient_mul y k (by omega)
        rw [hq_decomp] at hmul
        rw [hmul, ← h]
      have hdvd : altOddQuotient y k ∣ 2 ^ p := ⟨y + 1, by rw [Nat.mul_comm, h_prod]⟩
      have hy_even : 2 ∣ (y + 1) := by omega
      have hmod2 := altOddQuotient_mod_g hy_even hy k
      have hodd : altOddQuotient y k % 2 = 1 := by
        rw [hmod2]
        have : 2 * k + 1 = q := hq_decomp
        omega
      have hQ1 := odd_dvd_pow_two (altOddQuotient y k) p hodd hdvd
      have hQ3 := altOddQuotient_ge_three y k hy hk1
      omega

theorem pow_sq_mod_four (X k : Nat) (hX : (X ^ 2) % 4 = 1) :
    ((X ^ 2) ^ k) % 4 = 1 := by
  induction k with
  | zero => rw [Nat.pow_zero]
  | succ j ih =>
    rw [Nat.pow_succ, Nat.mul_mod, ih, hX]

theorem lebesgue_forced_congruences (X Y k : Nat)
    (hX : 2 ≤ X) (hY : 2 ≤ Y) (hk : 1 ≤ k)
    (h : X ^ (2 * k + 1) - Y ^ 2 = 1) :
    X % 4 = 1 ∧ Y % 2 = 0 := by
  have hcat : X ^ (2 * k + 1) = Y ^ 2 + 1 := by omega
  have hX_odd : X % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one X with h0 | h1
    · exfalso
      obtain ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero h0
      have h2m : 4 ∣ X ^ (2 * k + 1) := by
        have : 2 * k + 1 = 2 + (2 * k - 1) := by omega
        rw [hm, this, Nat.mul_pow, Nat.pow_add]
        have : 2 ^ 2 = 4 := by decide
        rw [this]
        exact ⟨2 ^ (2 * k - 1) * m ^ (2 + (2 * k - 1)), by ring⟩
      have hX_mod4 : (X ^ (2 * k + 1)) % 4 = 0 := Nat.mod_eq_zero_of_dvd h2m
      have hsq := nat_sq_mod_four Y
      rcases hsq with h0' | h1'
      · rw [hcat] at hX_mod4
        omega
      · rw [hcat] at hX_mod4
        omega
    · exact h1
  have hY_even : Y % 2 = 0 := by
    rcases Nat.mod_two_eq_zero_or_one Y with h0 | h1
    · exact h0
    · exfalso
      have hY_sq_1 : (Y ^ 2) % 4 = 1 := by
        have hrem : Y % 4 = 1 ∨ Y % 4 = 3 := by omega
        rcases hrem with h1' | h3'
        · rw [Nat.pow_two, Nat.mul_mod, h1']
        · rw [Nat.pow_two, Nat.mul_mod, h3']
      have hY2_1_mod4 : (Y ^ 2 + 1) % 4 = 2 := by
        rw [Nat.add_mod, hY_sq_1]
      have hX_sq_1 : (X ^ 2) % 4 = 1 := by
        have hrem : X % 4 = 1 ∨ X % 4 = 3 := by omega
        rcases hrem with h1' | h3'
        · rw [Nat.pow_two, Nat.mul_mod, h1']
        · rw [Nat.pow_two, Nat.mul_mod, h3']
      have hX_pow_mod4 : (X ^ (2 * k + 1)) % 4 = 1 ∨ (X ^ (2 * k + 1)) % 4 = 3 := by
        have : X ^ (2 * k + 1) = X * (X ^ 2) ^ k := by
          rw [Nat.pow_add, Nat.pow_one, Nat.pow_mul, Nat.mul_comm]
        rw [this, Nat.mul_mod, pow_sq_mod_four X k hX_sq_1]
        have hrem : X % 4 = 1 ∨ X % 4 = 3 := by omega
        rcases hrem with h1' | h3'
        · left; rw [h1']
        · right; rw [h3']
      rw [← hcat] at hY2_1_mod4
      rcases hX_pow_mod4 with h1'' | h3'' <;> omega
  have hX_mod4 : X % 4 = 1 := by
    have hY_sq_0 : (Y ^ 2) % 4 = 0 := by
      obtain ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero hY_even
      rw [hm, Nat.pow_two]
      have : 2 * m * (2 * m) = 4 * (m * m) := by ring
      rw [this, Nat.mul_mod_right]
    have hY2_1_mod4 : (Y ^ 2 + 1) % 4 = 1 := by
      rw [Nat.add_mod, hY_sq_0]
    have hX_sq_1 : (X ^ 2) % 4 = 1 := by
      have hrem : X % 4 = 1 ∨ X % 4 = 3 := by omega
      rcases hrem with h1' | h3'
      · rw [Nat.pow_two, Nat.mul_mod, h1']
      · rw [Nat.pow_two, Nat.mul_mod, h3']
    have : (X ^ (2 * k + 1)) % 4 = 1 := by
      rw [hcat, hY2_1_mod4]
    have hdecomp : X ^ (2 * k + 1) = X * (X ^ 2) ^ k := by
      rw [Nat.pow_add, Nat.pow_one, Nat.pow_mul, Nat.mul_comm]
    rw [hdecomp, Nat.mul_mod, pow_sq_mod_four X k hX_sq_1] at this
    have hrem : X % 4 = 1 ∨ X % 4 = 3 := by omega
    rcases hrem with h1' | h3'
    · exact h1'
    · exfalso
      rw [h3'] at this
      revert this
      decide
  exact ⟨hX_mod4, hY_even⟩

namespace ZGauss

structure ZGauss where
  re : Int
  im : Int
  deriving DecidableEq, Repr

def add (z w : ZGauss) : ZGauss :=
  ⟨z.re + w.re, z.im + w.im⟩

def mul (z w : ZGauss) : ZGauss :=
  ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩

def pow (z : ZGauss) : Nat → ZGauss
  | 0 => ⟨1, 0⟩
  | n + 1 => mul (pow z n) z

def norm (z : ZGauss) : Int :=
  z.re ^ 2 + z.im ^ 2

theorem mul_step_re_im (z w : ZGauss) :
    (mul z w).re = z.re * w.re - z.im * w.im ∧
    (mul z w).im = z.re * w.im + z.im * w.re :=
  ⟨rfl, rfl⟩

def imQuotient (a b : Int) : Nat → Int
  | 0 => 0
  | 1 => 1
  | 2 => 2 * a
  | 3 => 3 * a ^ 2 - b ^ 2
  | n + 1 => 2 * a * imQuotient a b n - (a ^ 2 + b ^ 2) * imQuotient a b (n - 1)

theorem unit_mul_eq_one_iff (b c : Int) (h : b * c = 1) :
    (b = 1 ∧ c = 1) ∨ (b = -1 ∧ c = -1) := by
  have habs : (b * c).natAbs = 1 := by rw [h]; rfl
  rw [Int.natAbs_mul] at habs
  have h1 : b.natAbs = 1 := by
    rcases (show b.natAbs = 0 ∨ b.natAbs = 1 ∨ 2 ≤ b.natAbs by omega) with hb0 | hb1 | hb2
    · rw [hb0, Nat.zero_mul] at habs; omega
    · exact hb1
    · exfalso
      rcases (show c.natAbs = 0 ∨ 1 ≤ c.natAbs by omega) with hc0 | hc1
      · rw [hc0, Nat.mul_zero] at habs; omega
      · have : 2 * 1 ≤ b.natAbs * c.natAbs := Nat.mul_le_mul hb2 hc1
        omega
  have hb_cases : b = 1 ∨ b = -1 := by
    rcases (show b = 1 ∨ b = -1 ∨ (b ≠ 1 ∧ b ≠ -1) by omega) with h | h | h
    · left; exact h
    · right; exact h
    · exfalso
      have : b.natAbs ≠ 1 := by
        intro h_abs
        have : b = 1 ∨ b = -1 := by
          rcases (show 0 ≤ b ∨ b < 0 by omega) with hpos | hneg
          · left; have := Int.natAbs_of_nonneg hpos; omega
          · right; have := Int.ofNat_natAbs_of_nonpos (by omega); omega
        omega
      omega
  rcases hb_cases with rfl | rfl
  · rw [Int.one_mul] at h; left; refine ⟨rfl, by omega⟩
  · right; refine ⟨rfl, by omega⟩

theorem lebesgue_pow_im_forces_unit_b (a b Y : Int) (p₀ : Nat)
    (hpow : pow ⟨a, b⟩ p₀ = ⟨Y, 1⟩)
    (him_fac : (pow ⟨a, b⟩ p₀).im = b * imQuotient a b p₀) :
    (b = 1 ∧ imQuotient a b p₀ = 1) ∨ (b = -1 ∧ imQuotient a b p₀ = -1) := by
  have him : (pow ⟨a, b⟩ p₀).im = 1 := by rw [hpow]
  rw [him] at him_fac
  exact unit_mul_eq_one_iff b (imQuotient a b p₀) him_fac.symm

theorem sq_eq_zero (a : Int) (h : a * a = 0) : a = 0 := by
  have habs : a.natAbs * a.natAbs = 0 := by
    have : (a * a).natAbs = 0 := by rw [h]; rfl
    rw [Int.natAbs_mul] at this
    exact this
  have : a.natAbs = 0 := by
    rcases (show a.natAbs = 0 ∨ 1 ≤ a.natAbs by omega) with h0 | h1
    · exact h0
    · exfalso
      have : 1 * 1 ≤ a.natAbs * a.natAbs := Nat.mul_le_mul h1 h1
      omega
  omega

theorem lebesgue_gaussian_cubic_impossible (a b Y : Int) (hY : Y ≠ 0)
    (hpow : mul (mul ⟨a, b⟩ ⟨a, b⟩) ⟨a, b⟩ = ⟨Y, 1⟩) : False := by
  have hre : (mul (mul ⟨a, b⟩ ⟨a, b⟩) ⟨a, b⟩).re = Y := by rw [hpow]
  have him : (mul (mul ⟨a, b⟩ ⟨a, b⟩) ⟨a, b⟩).im = 1 := by rw [hpow]
  simp only [mul] at hre him
  have him_fac : b * (3 * a ^ 2 - b ^ 2) = 1 := by
    calc b * (3 * a ^ 2 - b ^ 2) = (a * a - b * b) * b + (a * b + b * a) * a := by ring
    _ = 1 := him
  have hunit := unit_mul_eq_one_iff b (3 * a ^ 2 - b ^ 2) him_fac
  rcases hunit with ⟨rfl, h2⟩ | ⟨rfl, h2⟩
  · have h_alg : 3 * a ^ 2 - 1 = 1 := h2
    have : 3 * a ^ 2 = 2 := by omega
    have hdiv3 : 3 ∣ (2 : Int) := by
      have : (2 : Int) = 3 * a ^ 2 := this.symm
      rw [this]
      exact ⟨a ^ 2, rfl⟩
    obtain ⟨k, hk⟩ := hdiv3
    have hk_cases : k ≤ 0 ∨ k = 1 ∨ 2 ≤ k := by omega
    rcases hk_cases with hle | rfl | hge
    · have : 3 * k ≤ 0 := by omega
      omega
    · omega
    · have : 3 * 2 ≤ 3 * k := by omega
      omega
  · have h_alg : 3 * a ^ 2 - (-1) ^ 2 = -1 := h2
    have : 3 * a ^ 2 = 0 := by omega
    have ha2_zero : a ^ 2 = 0 := by
      have : (3 : Int) * a ^ 2 = 0 := this
      omega
    have ha_zero : a = 0 := sq_eq_zero a (by rw [← ha2_zero]; ring)
    rw [ha_zero] at hre
    have : (0 * 0 - -1 * -1) * 0 - (0 * -1 + -1 * 0) * -1 = (0 : Int) := by decide
    rw [this] at hre
    exact hY hre.symm

theorem mul_self_nonneg (a : Int) : 0 ≤ a * a := by
  rcases (show 0 ≤ a ∨ a ≤ 0 by omega) with hpos | hneg
  · exact Int.mul_nonneg hpos hpos
  · have : a * a = (-a) * (-a) := by ring
    rw [this]
    exact Int.mul_nonneg (by omega) (by omega)

theorem quintic_root_step (T : Int) (hT : 0 ≤ T) (h : 5 * T * (T - 2) = 0) :
    T = 0 ∨ T = 2 := by
  have : T * (T - 2) = 0 := by omega
  rcases (show T - 2 = 0 ∨ T - 2 ≠ 0 by omega) with h2 | hne2
  · right; omega
  · left
    have h_prod : T * (T - 2) = 0 := this
    rcases (show T ≤ 0 ∨ 1 ≤ T by omega) with hle | hge
    · omega
    · exfalso
      rcases (show T - 2 < 0 ∨ 0 < T - 2 by omega) with hneg | hpos
      · have : T * (T - 2) < 0 := by
          have h1 : 0 < T := by omega
          have : (- (T - 2)) * T > 0 := by
            have hA : 0 < - (T - 2) := by omega
            have : 1 * 1 ≤ (- (T - 2)) * T := Int.mul_le_mul (by omega) (by omega) (by decide) (by omega)
            omega
          omega
        omega
      · have : 0 < T * (T - 2) := by
          have : 1 * 1 ≤ T * (T - 2) := Int.mul_le_mul hge (by omega) (by decide) (by omega)
          omega
        omega

theorem lebesgue_gaussian_quintic_impossible (a b Y : Int) (hY : Y ≠ 0)
    (hpow : pow ⟨a, b⟩ 5 = ⟨Y, 1⟩) : False := by
  have hre : (pow ⟨a, b⟩ 5).re = Y := by rw [hpow]
  have him : (pow ⟨a, b⟩ 5).im = 1 := by rw [hpow]
  have him_fac : b * (5 * a ^ 4 - 10 * a ^ 2 * b ^ 2 + b ^ 4) = 1 := by
    dsimp [pow, mul] at him
    let c := 5 * (a * a * a * a) - 10 * (a * a) * (b * b) + b * b * b * b
    have hA : (1 * a - 0 * b) = a := by ring
    have hB : (1 * b + 0 * a) = b := by ring
    have hC : (a * a - b * b) = a * a - b * b := rfl
    have hD : (a * b + b * a) * a + (a * a - b * b) * b =
        3 * (a * a) * b - b * b * b := by ring
    have hE : (a * a - b * b) * a - (a * b + b * a) * b =
        a * a * a - 3 * a * (b * b) := by ring
    have hF : ((a * a * a - 3 * a * (b * b)) * a - (3 * (a * a) * b - b * b * b) * b) =
        a * a * a * a - 6 * (a * a) * (b * b) + b * b * b * b := by ring
    have hG : ((a * a * a - 3 * a * (b * b)) * b + (3 * (a * a) * b - b * b * b) * a) =
        4 * (a * a * a) * b - 4 * a * (b * b * b) := by ring
    have hH : (a * a * a * a - 6 * (a * a) * (b * b) + b * b * b * b) * b +
        (4 * (a * a * a) * b - 4 * a * (b * b * b)) * a = b * c := by ring
    rw [hA, hB, hD, hE, hF, hG, hH] at him
    exact him
  let c := 5 * a ^ 4 - 10 * a ^ 2 * b ^ 2 + b ^ 4
  have him_fac' : b * c = 1 := by
    dsimp [pow, mul] at him
    have hA : (1 * a - 0 * b) = a := by ring
    have hB : (1 * b + 0 * a) = b := by ring
    have hC : ((a * a - b * b) * a - (a * b + b * a) * b) =
        a * a * a - 3 * a * (b * b) := by ring
    have hD : ((a * a * a - 3 * a * (b * b)) * b + ((a * b + b * a) * a + (a * a - b * b) * b) * a) =
        4 * (a * a * a) * b - 4 * a * (b * b * b) := by ring
    have hE : (a * a * a * a - 6 * (a * a) * (b * b) + b * b * b * b) * b +
        (4 * (a * a * a) * b - 4 * a * (b * b * b)) * a = b * c := by ring
    rw [hA, hB, hC, hD, hE] at him
    exact him
  have hunit := unit_mul_eq_one_iff b c him_fac
  rcases hunit with ⟨rfl, hc1⟩ | ⟨rfl, hc_neg1⟩
  · dsimp [c] at hc1
    have h1 : 5 * (a * a * a * a) - 10 * (a * a * 1) + 1 = 1 := hc1
    have h2 : 5 * (a * a * a * a) - 10 * (a * a) = 0 := by omega
    have h_factor : 5 * (a * a * a * a) - 10 * (a * a) = 5 * (a * a) * (a * a - 2) := by ring
    rw [h_factor] at h2
    let T := a * a
    have hT_eq : a * a = T := rfl
    have hT_nonneg : 0 ≤ T := by rw [← hT_eq]; exact mul_self_nonneg a
    have h2' : 5 * T * (T - 2) = 0 := by rw [← hT_eq]; exact h2
    have ha_cases := quintic_root_step T hT_nonneg h2'
    rw [← hT_eq] at ha_cases
    rcases ha_cases with ha0 | ha2
    · have ha_zero : a = 0 := sq_eq_zero a ha0
      rw [ha_zero] at hre
      have hzero : ((((1 * 0 - 0 * 1) * 0 - (1 * 1 + 0 * 0) * 1) * 0 - ((1 * 0 - 0 * 1) * 1 + (1 * 1 + 0 * 0) * 0) * 1) * 0 - (((1 * 0 - 0 * 1) * 0 - (1 * 1 + 0 * 0) * 1) * 1 + ((1 * 0 - 0 * 1) * 1 + (1 * 1 + 0 * 0) * 0) * 0) * 1) * 0 - ((((1 * 0 - 0 * 1) * 0 - (1 * 1 + 0 * 0) * 1) * 0 - ((1 * 0 - 0 * 1) * 1 + (1 * 1 + 0 * 0) * 0) * 1) * 1 + (((1 * 0 - 0 * 1) * 0 - (1 * 1 + 0 * 0) * 1) * 1 + ((1 * 0 - 0 * 1) * 1 + (1 * 1 + 0 * 0) * 0) * 0) * 0) * 1 = (0 : Int) := by decide
      rw [hzero] at hre
      exact hY hre.symm
    · exfalso
      have hrem : (a.natAbs * a.natAbs) = 2 := by
        have : (a * a).natAbs = 2 := by rw [ha2]; rfl
        rw [Int.natAbs_mul] at this
        exact this
      rcases (show a.natAbs ≤ 1 ∨ 2 ≤ a.natAbs by omega) with hle | hge
      · rcases (show a.natAbs = 0 ∨ a.natAbs = 1 by omega) with h0 | h1
        · rw [h0] at hrem; omega
        · rw [h1] at hrem; omega
      · have : 2 * 2 ≤ a.natAbs * a.natAbs := Nat.mul_le_mul hge hge
        omega
  · dsimp [c] at hc_neg1
    have h1 : 5 * (a * a * a * a) - 10 * (a * a * 1) + 1 = -1 := hc_neg1
    have h2 : 5 * (a * a * a * a) - 10 * (a * a) + 2 = 0 := by omega
    have hdiv5 : 5 ∣ (2 : Int) := by
      have : (2 : Int) = - (5 * (a * a * a * a) - 10 * (a * a)) := by omega
      rw [this]
      have : 5 * (a * a * a * a) - 10 * (a * a) = 5 * (a * a * a * a - 2 * (a * a)) := by ring
      rw [this]
      exact ⟨-(a * a * a * a - 2 * (a * a)), by ring⟩
    obtain ⟨k, hk⟩ := hdiv5
    have hk_cases : k ≤ -1 ∨ k = 0 ∨ 1 ≤ k := by omega
    rcases hk_cases with hneg | rfl | hpos
    · have : 5 * k ≤ -5 := by omega
      omega
    · omega
    · have : 5 * 1 ≤ 5 * k := by omega
      omega

theorem gaussian_conjugate_bezout (m : Int) :
    add (mul ⟨1, -m⟩ ⟨1, 2 * m⟩) (mul ⟨0, -m⟩ ⟨1, -(2 * m)⟩) = ⟨1, 0⟩ := by
  simp only [add, mul]
  have h1 : 1 * 1 - -m * (2 * m) + (0 * 1 - -m * -(2 * m)) = (1 : Int) := by ring
  have h2 : 1 * (2 * m) + -m * 1 + (0 * -(2 * m) + -m * 1) = (0 : Int) := by ring
  rw [h1, h2]

theorem pow_add_two (z : ZGauss) (n : Nat) :
    pow z (n + 2) = mul (mul (pow z n) z) z := rfl

theorem mul_sq_im (R I m b : Int) (hb : b * b = 1) :
    (mul (mul ⟨R, I⟩ ⟨2 * m, b⟩) ⟨2 * m, b⟩).im =
      4 * (m * (R * b + I * m)) - I := by
  dsimp [mul]
  have : (R * (2 * m) - I * b) * b + (R * b + I * (2 * m)) * (2 * m) =
      4 * (m * (R * b + I * m)) - I * (b * b) := by ring
  rw [this, hb]
  ring

end ZGauss


/-! ## Section 7: Cassels' Cyclotomic Divisibility Theorem & Hyyro-Mignotte Size Lower Bounds -/

theorem even_pow_even {y : Nat} (hy : y % 2 = 0) {q : Nat} (hq : 1 ≤ q) :
    (y ^ q) % 2 = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hq
  rw [Nat.pow_add, Nat.pow_one, Nat.mul_mod, hy]
  omega

theorem pow_add_one_lt_swap {u p q : Nat}
    (hu : 1 ≤ u) (hp : 1 ≤ p) (hpq : p < q) :
    (u ^ q + 1) ^ p < (u ^ p + 1) ^ q := by
  rcases (show u = 1 ∨ 2 ≤ u by omega) with rfl | hu2
  · simp only [Nat.one_pow]
    exact Nat.pow_lt_pow_right (by decide) hpq
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (show p ≤ q by omega)
    have hk_pos : k ≠ 0 := by omega
    have hq_eq : q = p + k := hk
    have h1 : u ^ q + 1 ≤ u ^ k * (u ^ p + 1) := by
      rw [hq_eq, Nat.pow_add]
      have : u ^ p * u ^ k + 1 ≤ u ^ k * (u ^ p + 1) := by
        have : u ^ k * (u ^ p + 1) = u ^ p * u ^ k + u ^ k := by ring
        rw [this]
        have : 1 ≤ u ^ k := Nat.one_le_pow k u (by omega)
        omega
      exact this
    have h2 : (u ^ q + 1) ^ p ≤ (u ^ k * (u ^ p + 1)) ^ p :=
      Nat.pow_le_pow_left h1 p
    have h3 : (u ^ k * (u ^ p + 1)) ^ p < (u ^ p + 1) ^ q := by
      rw [Nat.mul_pow]
      have h_swap : (u ^ k) ^ p = (u ^ p) ^ k := by
        rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm]
      rw [h_swap]
      have h_base : (u ^ p) ^ k < (u ^ p + 1) ^ k := by
        have : u ^ p < u ^ p + 1 := by omega
        exact Nat.pow_lt_pow_left this hk_pos
      have h_prod : (u ^ p) ^ k * (u ^ p + 1) ^ p < (u ^ p + 1) ^ k * (u ^ p + 1) ^ p :=
        Nat.mul_lt_mul_of_pos_right h_base (Nat.pow_pos (by omega))
      have h_exp : (u ^ p + 1) ^ k * (u ^ p + 1) ^ p = (u ^ p + 1) ^ q := by
        rw [← Nat.pow_add, hq_eq]
        have : k + p = p + k := by omega
        rw [this]
      rw [h_exp] at h_prod
      exact h_prod
    exact Nat.lt_of_le_of_lt h2 h3

theorem pow_sub_one_lt_swap {a q p : Nat}
    (ha : 2 ≤ a) (hq : 1 ≤ q) (hqp : q < p) :
    (a ^ q - 1) ^ p < (a ^ p - 1) ^ q := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (show q ≤ p by omega)
  have hk1 : k ≠ 0 := by omega
  have hp_eq : p = q + k := hk
  have h1 : (a ^ q - 1) ^ p = (a ^ q - 1) ^ k * (a ^ q - 1) ^ q := by
    rw [hp_eq, Nat.pow_add, Nat.mul_comm]
  have h2 : (a ^ q - 1) ^ k < (a ^ q) ^ k := by
    have : a ^ q - 1 < a ^ q := by
      have : 1 ≤ a ^ q := Nat.one_le_pow q a (by omega)
      omega
    exact Nat.pow_lt_pow_left this hk1
  have h3 : (a ^ q - 1) ^ k * (a ^ q - 1) ^ q < (a ^ q) ^ k * (a ^ q - 1) ^ q :=
    Nat.mul_lt_mul_of_pos_right h2 (Nat.pow_pos (by
      have : 2 ≤ a ^ q := nat_pow_ge_two ha hq
      omega))
  have h4 : (a ^ q) ^ k * (a ^ q - 1) ^ q ≤ (a ^ p - 1) ^ q := by
    have h_swap : (a ^ q) ^ k = (a ^ k) ^ q := by
      rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm]
    rw [h_swap, ← Nat.mul_pow, hp_eq]
    have : a ^ k * (a ^ q - 1) = a ^ (k + q) - a ^ k := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_one]
      have : a ^ k * a ^ q = a ^ (k + q) := by rw [← Nat.pow_add]
      rw [this]
    rw [this]
    have : a ^ (k + q) - a ^ k ≤ a ^ (q + k) - 1 := by
      have : k + q = q + k := by omega
      rw [this]
      have : 1 ≤ a ^ k := Nat.one_le_pow k a (by omega)
      omega
    exact Nat.pow_le_pow_left this q
  rw [h1]
  exact Nat.lt_of_lt_of_le h3 h4

def cyclotomicQuotient (x : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => cyclotomicQuotient x k + x ^ k

theorem cyclotomicQuotient_mul (x p : Nat) (hx : 1 ≤ x) :
    (x - 1) * cyclotomicQuotient x p + 1 = x ^ p := by
  induction p with
  | zero => simp [cyclotomicQuotient]
  | succ k ih =>
    unfold cyclotomicQuotient
    rw [Nat.mul_add]
    have h1 : (x - 1) * cyclotomicQuotient x k + (x - 1) * x ^ k + 1 =
        ((x - 1) * cyclotomicQuotient x k + 1) + (x - 1) * x ^ k := by omega
    rw [h1, ih]
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hx
    have hsub : 1 + d - 1 = d := by omega
    rw [hsub, Nat.pow_succ]
    ring

theorem one_le_cyclotomicQuotient {x p : Nat} (hx : 1 ≤ x) (hp : 1 ≤ p) :
    1 ≤ cyclotomicQuotient x p := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hp
  have : 1 + k = k + 1 := Nat.add_comm 1 k
  rw [this]
  unfold cyclotomicQuotient
  have : 1 ≤ x ^ k := Nat.one_le_pow k x hx
  omega

theorem pow_mod_of_dvd_sub_one {x g : Nat} (h : g ∣ x - 1) (hx : 1 ≤ x) (k : Nat) :
    x ^ k % g = 1 % g := by
  induction k with
  | zero => rfl
  | succ j ih =>
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hx
    have hsub : 1 + d - 1 = d := by omega
    rw [hsub] at h
    obtain ⟨m, hm⟩ := h
    have hx_mod : (1 + d) % g = 1 % g := by
      have : 1 + d = g * m + 1 := by omega
      rw [this]
      exact Nat.mul_add_mod_self_left g m 1
    rw [Nat.pow_succ, Nat.mul_mod, ih, ← Nat.mul_mod, Nat.one_mul, hx_mod]

theorem cyclotomicQuotient_mod {x g : Nat} (h : g ∣ x - 1) (hx : 1 ≤ x) (p : Nat) :
    cyclotomicQuotient x p % g = p % g := by
  induction p with
  | zero => rfl
  | succ k ih =>
    unfold cyclotomicQuotient
    rw [Nat.add_mod, ih, pow_mod_of_dvd_sub_one h hx k]
    rw [← Nat.add_mod]

theorem gcd_sub_one_cyclotomicQuotient_dvd (x p : Nat) (hx : 1 ≤ x) :
    Nat.gcd (x - 1) (cyclotomicQuotient x p) ∣ p := by
  let g := Nat.gcd (x - 1) (cyclotomicQuotient x p)
  have hg1 : g ∣ x - 1 := Nat.gcd_dvd_left (x - 1) (cyclotomicQuotient x p)
  have hg2 : g ∣ cyclotomicQuotient x p := Nat.gcd_dvd_right (x - 1) (cyclotomicQuotient x p)
  have hmod := cyclotomicQuotient_mod hg1 hx p
  have h0 : cyclotomicQuotient x p % g = 0 := Nat.mod_eq_zero_of_dvd hg2
  rw [h0] at hmod
  exact Nat.dvd_of_mod_eq_zero hmod.symm

theorem gcd_sub_one_cyclotomicQuotient_prime_cases (x p : Nat)
    (hx : 1 ≤ x) (hp_pr : IsPrimeNat p) :
    Nat.Coprime (x - 1) (cyclotomicQuotient x p) ∨
    Nat.gcd (x - 1) (cyclotomicQuotient x p) = p := by
  have hdvd := gcd_sub_one_cyclotomicQuotient_dvd x p hx
  rcases hp_pr.2 (Nat.gcd (x - 1) (cyclotomicQuotient x p)) hdvd with h1 | hp
  · left; exact h1
  · right; exact hp

theorem cassels_case_one_coprime_power_split (x p y q : Nat)
    (hx : 2 ≤ x) (hp : 2 ≤ p) (hy : 2 ≤ y) (hq : 2 ≤ q)
    (hcat : x ^ p = y ^ q + 1)
    (hcop : Nat.Coprime (x - 1) (cyclotomicQuotient x p)) :
    x - 1 = (Nat.gcd y (x - 1)) ^ q ∧
    cyclotomicQuotient x p = (Nat.gcd y (cyclotomicQuotient x p)) ^ q ∧
    2 ≤ Nat.gcd y (x - 1) ∧
    2 ^ q + 1 ≤ x := by
  have hy_pos : 0 < y := by omega
  have hprod : (x - 1) * cyclotomicQuotient x p = y ^ q := by
    have hmul := cyclotomicQuotient_mul x p (by omega)
    rw [hcat] at hmul
    exact Nat.add_right_cancel hmul
  have hQ_pos : 1 ≤ cyclotomicQuotient x p := one_le_cyclotomicQuotient (by omega) (by omega)
  obtain ⟨hu_pow, hv_pow⟩ :=
    coprime_mul_eq_pow (x - 1) (cyclotomicQuotient x p) y q (by omega) hQ_pos hcop hprod
  obtain ⟨u, hu_def⟩ : ∃ u, Nat.gcd y (x - 1) = u := ⟨Nat.gcd y (x - 1), rfl⟩
  rw [hu_def] at hu_pow ⊢
  have hu_dvd : u ∣ y := by rw [← hu_def]; exact Nat.gcd_dvd_left y (x - 1)
  have hu_pos : 1 ≤ u := Nat.pos_of_dvd_of_pos hu_dvd hy_pos
  have hu_ne1 : u ≠ 1 := by
    intro hu1
    rw [hu1, Nat.one_pow] at hu_pow
    have hx2 : x = 2 := by omega
    subst hx2
    have h2p : 2 ^ p = y ^ q + 1 := hcat
    exact catalan_binary_minuend_impossible p y q hp hy hq h2p
  have hu2 : 2 ≤ u := by omega
  have hx_ge : 2 ^ q + 1 ≤ x := by
    have h1 : 2 ^ q ≤ u ^ q := Nat.pow_le_pow_left hu2 q
    have h2 : u ^ q = x - 1 := hu_pow.symm
    have h3 : 2 ^ q ≤ x - 1 := by rw [← h2]; exact h1
    clear hprod hQ_pos hu_pow hv_pow hu_def hu_pos hu_ne1 hcop hcat h1 h2
    omega
  refine ⟨hu_pow, hv_pow, hu2, hx_ge⟩

private theorem pow_eq_add_one_impossible_of_add_one_eq_pow
    (u y p q : Nat) (hu : 2 ≤ u) (hp : 2 ≤ p) (hpq : p < q)
    (hcat : (u ^ q + 1) ^ p = y ^ q + 1) : False := by
  have h1 : (u ^ q + 1) ^ p < (u ^ p + 1) ^ q := pow_add_one_lt_swap (by omega) (by omega) hpq
  have h2 : y ^ q + 1 < (u ^ p + 1) ^ q := by rw [← hcat]; exact h1
  have hy_lt : y < u ^ p + 1 := by
    apply Classical.byContradiction
    intro hge
    have : u ^ p + 1 ≤ y := by omega
    have : (u ^ p + 1) ^ q ≤ y ^ q := Nat.pow_le_pow_left this q
    omega
  have hy_le : y ≤ u ^ p := by omega
  have hyq_le : y ^ q ≤ (u ^ p) ^ q := Nat.pow_le_pow_left hy_le q
  have : (u ^ p) ^ q = (u ^ q) ^ p := by rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm]
  have h3 : y ^ q + 1 ≤ (u ^ q) ^ p + 1 := by omega
  have h4 : (u ^ q) ^ p + 1 < (u ^ q + 1) ^ p := by
    let A := u ^ q
    have hA : 2 ≤ A := by
      have : 2 ≤ u ^ 1 := by rw [Nat.pow_one]; exact hu
      have : u ^ 1 ≤ u ^ q := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have hm : 1 ≤ p - 1 := by omega
    obtain ⟨m, hm_eq⟩ : ∃ m, p - 1 = m := ⟨p - 1, rfl⟩
    have hp_m : p = m + 1 := by omega
    have h_split : (A + 1) ^ (m + 1) = A * (A + 1) ^ m + (A + 1) ^ m := by
      rw [Nat.pow_succ, Nat.mul_comm]
      ring
    have h_leA : A * A ^ m ≤ A * (A + 1) ^ m :=
      Nat.mul_le_mul_left A (Nat.pow_le_pow_left (by omega) m)
    have h_le2 : 2 ≤ (A + 1) ^ m := by
      have : 2 ≤ (A + 1) ^ 1 := by rw [Nat.pow_one]; omega
      have : (A + 1) ^ 1 ≤ (A + 1) ^ m := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have h_A_pow : A ^ (m + 1) = A * A ^ m := by
      rw [Nat.pow_succ, Nat.mul_comm]
    have h_leA' : A ^ (m + 1) ≤ A * (A + 1) ^ m := by
      rw [h_A_pow]
      exact h_leA
    have h_sum : A ^ (m + 1) + 2 ≤ A * (A + 1) ^ m + (A + 1) ^ m :=
      Nat.add_le_add h_leA' h_le2
    have h_final : A ^ (m + 1) + 2 ≤ (A + 1) ^ (m + 1) := by
      rw [h_split]
      exact h_sum
    have : (u ^ q) ^ p + 2 ≤ (u ^ q + 1) ^ p := by
      dsimp [A] at h_final
      rw [hp_m]
      exact h_final
    omega
  omega

theorem cassels_case_one_impossible_of_lt (x p y q : Nat)
    (hx : 2 ≤ x) (hp : 2 ≤ p) (hy : 2 ≤ y) (hq : 2 ≤ q)
    (hpq : p < q) (hcat : x ^ p = y ^ q + 1)
    (hcop : Nat.Coprime (x - 1) (cyclotomicQuotient x p)) : False := by
  obtain ⟨hu_pow, _, hu2, _⟩ :=
    cassels_case_one_coprime_power_split x p y q hx hp hy hq hcat hcop
  let u := Nat.gcd y (x - 1)
  have : Nat.gcd y (x - 1) = u := rfl
  rw [this] at hu_pow
  obtain ⟨K, hK⟩ : ∃ K, u ^ q = K := ⟨_, rfl⟩
  rw [hK] at hu_pow
  have hx_eq : x = K + 1 := by omega
  have hcat' : (u ^ q + 1) ^ p = y ^ q + 1 := by
    rw [hK, ← hx_eq]
    exact hcat
  exact pow_eq_add_one_impossible_of_add_one_eq_pow u y p q hu2 hp hpq hcat'

theorem catalan_binary_subtrahend_unique (x p q : Nat)
    (hx : 2 ≤ x) (hp : 2 ≤ p) (hq : 2 ≤ q) :
    x ^ p = 2 ^ q + 1 ↔ x = 3 ∧ p = 2 ∧ q = 3 := by
  constructor
  · intro hcat
    rcases Nat.mod_two_eq_zero_or_one p with hp_even | hp_odd
    · obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hp_even
      have hk_pos : 1 ≤ k := by omega
      have hp_eq : p = 2 * k := by omega
      have : (x ^ k) ^ 2 = x ^ (2 * k) := by
        rw [← Nat.pow_mul, Nat.mul_comm k 2]
      have h1 : (x ^ k) ^ 2 - 2 ^ q = 1 := by
        rw [this, ← hp_eq]
        omega
      have hXk : 2 ≤ x ^ k := nat_pow_ge_two hx hk_pos
      obtain ⟨hXk_eq, hq3⟩ := (chao_ko_binary_base_unique (x ^ k) q hXk hq).mp h1
      have hx_eq : x = 3 ∧ k = 1 := by
        rcases (show k = 1 ∨ 2 ≤ k by omega) with rfl | hk2
        · rw [Nat.pow_one] at hXk_eq
          exact ⟨hXk_eq, rfl⟩
        · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk2
          have : 4 ≤ x ^ (2 + m) := by
            rw [Nat.pow_add]
            have h4 : 4 ≤ x ^ 2 := by
              rw [Nat.pow_two]
              exact Nat.mul_le_mul hx hx
            have h1 : 1 ≤ x ^ m := Nat.one_le_pow m x (by omega)
            have : 4 * 1 ≤ x ^ 2 * x ^ m := Nat.mul_le_mul h4 h1
            omega
          omega
      exact ⟨hx_eq.1, by omega, hq3⟩
    · exfalso
      have hp3 : 3 ≤ p := by omega
      have hp_min : minFac p ∣ p := minFac_dvd p
      have hp_min_pr : IsPrimeNat (minFac p) := minFac_prime (by omega)
      have hp_min_odd : minFac p % 2 = 1 := by
        rcases minFac_eq_two_or_odd_prime (n := p) (by omega) with h2 | ⟨h3, hodd, -⟩
        · obtain ⟨k, hk⟩ := minFac_dvd p
          rw [h2] at hk
          omega
        · exact hodd
      obtain ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero (show (minFac p - 1) % 2 = 0 by omega)
      have hp0_eq : minFac p = 2 * m + 1 := by omega
      have hm1 : 1 ≤ m := by
        have : 2 ≤ minFac p := hp_min_pr.1
        omega
      obtain ⟨hdiv_p, hX2, hXp⟩ := nat_minFac_pow_decomp x p hx hp
      let X := x ^ (p / minFac p)
      have hcat' : X ^ (minFac p) = 2 ^ q + 1 := by
        rw [← hXp]
        exact hcat
      have hcop : Nat.Coprime (X - 1) (cyclotomicQuotient X (minFac p)) := by
        let G := Nat.gcd (X - 1) (cyclotomicQuotient X (minFac p))
        have hdvd_p : G ∣ minFac p := gcd_sub_one_cyclotomicQuotient_dvd X (minFac p) (by omega)
        have hG_odd : G % 2 = 1 := by
          rcases Nat.mod_two_eq_zero_or_one G with h0 | h1
          · exfalso
            obtain ⟨w, hw⟩ := Nat.dvd_of_mod_eq_zero h0
            have : 2 ∣ minFac p := by
              have : 2 ∣ G := ⟨w, hw⟩
              exact Nat.dvd_trans this hdvd_p
            omega
          · exact h1
        have hprod : (X - 1) * cyclotomicQuotient X (minFac p) = 2 ^ q := by
          have hmul := cyclotomicQuotient_mul X (minFac p) (by omega)
          rw [hcat'] at hmul
          exact Nat.add_right_cancel hmul
        have hdvd_2q : G ∣ 2 ^ q := by
          have h1 : G ∣ X - 1 := Nat.gcd_dvd_left _ _
          obtain ⟨u, hu⟩ := h1
          have : 2 ^ q = G * (u * cyclotomicQuotient X (minFac p)) := by
            calc 2 ^ q = (X - 1) * cyclotomicQuotient X (minFac p) := hprod.symm
            _ = (G * u) * cyclotomicQuotient X (minFac p) := by rw [hu]
            _ = G * (u * cyclotomicQuotient X (minFac p)) := by ring
          exact ⟨u * cyclotomicQuotient X (minFac p), this⟩
        have hG_one : G = 1 := odd_dvd_pow_two G q hG_odd hdvd_2q
        exact hG_one
      have h_minFac_ge2 : 2 ≤ minFac p := hp_min_pr.1
      rcases (show minFac p < q ∨ q ≤ minFac p by omega) with hpq | hqp
      · exact cassels_case_one_impossible_of_lt X (minFac p) 2 q hX2 h_minFac_ge2 (by decide) hq hpq hcat' hcop
      · have hprod : (X - 1) * cyclotomicQuotient X (minFac p) = 2 ^ q := by
          have hmul := cyclotomicQuotient_mul X (minFac p) (by omega)
          rw [hcat'] at hmul
          exact Nat.add_right_cancel hmul
        obtain ⟨hu_pow, _, hu2, _⟩ :=
          cassels_case_one_coprime_power_split X (minFac p) 2 q hX2 h_minFac_ge2 (by decide) hq hcat' hcop
        let u := Nat.gcd 2 (X - 1)
        have hu_le2 : u ≤ 2 := Nat.le_of_dvd (by decide) (Nat.gcd_dvd_left 2 (X - 1))
        have hu_eq2 : u = 2 := by omega
        have : X - 1 = 2 ^ q := by
          rw [← hu_eq2]
          exact hu_pow
        have hX_eq : X = 2 ^ q + 1 := by omega
        rw [hX_eq] at hcat'
        obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le (show 2 ≤ minFac p by omega)
        rw [hj, Nat.pow_add, Nat.pow_two] at hcat'
        have h_le : 1 ≤ 2 ^ q := Nat.one_le_pow q 2 (by decide)
        have h1 : 1 ≤ 2 ^ q + 1 := by omega
        have h_pos : 1 ≤ (2 ^ q + 1) ^ j := Nat.one_le_pow j (2 ^ q + 1) h1
        have h_gt : 2 ^ q + 1 < (2 ^ q + 1) * (2 ^ q + 1) * (2 ^ q + 1) ^ j := by
          have hpos : 0 < 2 ^ q + 1 := by omega
          have h2 : 1 < 2 ^ q + 1 := by omega
          have h3 : (2 ^ q + 1) * 1 < (2 ^ q + 1) * (2 ^ q + 1) := Nat.mul_lt_mul_of_pos_left h2 hpos
          rw [Nat.mul_one] at h3
          have h4 : (2 ^ q + 1) * (2 ^ q + 1) * 1 ≤ (2 ^ q + 1) * (2 ^ q + 1) * (2 ^ q + 1) ^ j :=
            Nat.mul_le_mul_left _ h_pos
          rw [Nat.mul_one] at h4
          exact Nat.lt_of_lt_of_le h3 h4
        have : (2 ^ q + 1) * (2 ^ q + 1) * (2 ^ q + 1) ^ j = 2 ^ q + 1 := hcat'
        omega
  · rintro ⟨rfl, rfl, rfl⟩
    decide

theorem cassels_case_two_divisibility (x p y q : Nat)
    (hx : 1 ≤ x) (hcat : x ^ p = y ^ q + 1)
    (hgcd_p : Nat.gcd (x - 1) (cyclotomicQuotient x p) = p) :
    p ∣ (x - 1) ∧ p ∣ cyclotomicQuotient x p ∧ p ^ 2 ∣ y ^ q := by
  obtain ⟨a, ha⟩ := Nat.gcd_dvd_left (x - 1) (cyclotomicQuotient x p)
  rw [hgcd_p] at ha
  have hd1 : p ∣ (x - 1) := ⟨a, ha⟩
  obtain ⟨b, hb⟩ := Nat.gcd_dvd_right (x - 1) (cyclotomicQuotient x p)
  rw [hgcd_p] at hb
  have hd2 : p ∣ cyclotomicQuotient x p := ⟨b, hb⟩
  have hfact : (x - 1) * cyclotomicQuotient x p = y ^ q := by
    have hmul := cyclotomicQuotient_mul x p hx
    rw [hcat] at hmul
    exact Nat.add_right_cancel hmul
  refine ⟨hd1, hd2, ⟨a * b, ?_⟩⟩
  rw [← hfact, ha, hb]
  ring

theorem cassels_unconditional_p_dvd_of_lt (x p y q : Nat)
    (hx : 2 ≤ x) (hp : 2 ≤ p) (hy : 2 ≤ y) (hq : 2 ≤ q)
    (hpq : p < q) (hp_pr : IsPrimeNat p)
    (hcat : x ^ p = y ^ q + 1) :
    p ∣ (x - 1) ∧ p ∣ cyclotomicQuotient x p ∧ p ^ 2 ∣ y ^ q := by
  rcases gcd_sub_one_cyclotomicQuotient_prime_cases x p (by omega) hp_pr with hcop | hgcd_p
  · exfalso
    exact cassels_case_one_impossible_of_lt x p y q hx hp hy hq hpq hcat hcop
  · exact cassels_case_two_divisibility x p y q (by omega) hcat hgcd_p

theorem cassels_symmetric_case_one_coprime_power_split (x p y k : Nat)
    (hx : 2 ≤ x) (hp : 2 ≤ p) (hy : 2 ≤ y) (hk : 1 ≤ k)
    (hcat : x ^ p = y ^ (2 * k + 1) + 1)
    (hcop : Nat.Coprime (y + 1) (altOddQuotient y k)) :
    y + 1 = (Nat.gcd x (y + 1)) ^ p ∧
    altOddQuotient y k = (Nat.gcd x (altOddQuotient y k)) ^ p ∧
    2 ≤ Nat.gcd x (y + 1) := by
  have hprod : (y + 1) * altOddQuotient y k = x ^ p := by
    rw [altOddQuotient_mul y k (by omega), hcat]
  have hQ_pos : 1 ≤ altOddQuotient y k := one_le_altOddQuotient y k
  obtain ⟨ha_pow, hb_pow⟩ :=
    coprime_mul_eq_pow (y + 1) (altOddQuotient y k) x p (by omega) hQ_pos hcop hprod
  obtain ⟨a, ha_def⟩ : ∃ a, Nat.gcd x (y + 1) = a := ⟨Nat.gcd x (y + 1), rfl⟩
  rw [ha_def] at ha_pow ⊢
  have hx_pos : 0 < x := by omega
  have ha_dvd : a ∣ x := by rw [← ha_def]; exact Nat.gcd_dvd_left x (y + 1)
  have ha_pos : 1 ≤ a := Nat.pos_of_dvd_of_pos ha_dvd hx_pos
  have ha_ne1 : a ≠ 1 := by
    intro ha1
    rw [ha1, Nat.one_pow] at ha_pow
    omega
  have ha2 : 2 ≤ a := by omega
  refine ⟨ha_pow, hb_pow, ha2⟩

private theorem cassels_symmetric_case_one_impossible_of_lt_core (x p y k a : Nat)
    (ha : 2 ≤ a) (hp : 2 ≤ p) (hk : 1 ≤ k)
    (hqp : 2 * k + 1 < p)
    (hcat : x ^ p = (a ^ p - 1) ^ (2 * k + 1) + 1) : False := by
  let q := 2 * k + 1
  have hq1 : 1 ≤ q := by omega
  have hq2 : 2 ≤ q := by omega
  let A := a ^ p - 1
  have hA : 2 ≤ A := by
    have h4 : 4 ≤ a ^ 2 := by
      rw [Nat.pow_two]
      have : 2 * 2 ≤ a * a := Nat.mul_le_mul ha ha
      omega
    have : a ^ 2 ≤ a ^ p := Nat.pow_le_pow_right (by omega) hp
    have : 4 ≤ a ^ p := Nat.le_trans h4 this
    omega
  have hm : 1 ≤ q - 1 := by omega
  obtain ⟨m, hm_eq⟩ : ∃ m, q - 1 = m := ⟨q - 1, rfl⟩
  have hq_m : q = m + 1 := by omega
  have h_split : (A + 1) ^ (m + 1) = A * (A + 1) ^ m + (A + 1) ^ m := by
    rw [Nat.pow_succ, Nat.mul_comm]
    ring
  have h_leA : A * A ^ m ≤ A * (A + 1) ^ m :=
    Nat.mul_le_mul_left A (Nat.pow_le_pow_left (by omega) m)
  have h_le2 : 2 ≤ (A + 1) ^ m := by
    have : 2 ≤ (A + 1) ^ 1 := by rw [Nat.pow_one]; omega
    have : (A + 1) ^ 1 ≤ (A + 1) ^ m := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have h_A_pow : A ^ (m + 1) = A * A ^ m := by
    rw [Nat.pow_succ, Nat.mul_comm]
  have h_leA' : A ^ (m + 1) ≤ A * (A + 1) ^ m := by
    rw [h_A_pow]
    exact h_leA
  have h_sum : A ^ (m + 1) + 2 ≤ A * (A + 1) ^ m + (A + 1) ^ m :=
    Nat.add_le_add h_leA' h_le2
  have h_final : A ^ (m + 1) + 2 ≤ (A + 1) ^ (m + 1) := by
    rw [h_split]
    exact h_sum
  have h_Ap_q : A ^ q + 2 ≤ (a ^ p) ^ q := by
    have : A + 1 = a ^ p := by
      dsimp [A]
      have : 1 ≤ a ^ p := Nat.one_le_pow p a (by omega)
      omega
    rw [this] at h_final
    rw [hq_m]
    exact h_final
  have h_swap : (a ^ p) ^ q = (a ^ q) ^ p := by
    rw [← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm]
  have h_xp_lt : x ^ p < (a ^ q) ^ p := by
    rw [← h_swap]
    have : x ^ p = A ^ q + 1 := hcat
    rw [this]
    omega
  have h_x_lt : x < a ^ q := by
    apply Classical.byContradiction
    intro hge
    have : a ^ q ≤ x := by omega
    have : (a ^ q) ^ p ≤ x ^ p := Nat.pow_le_pow_left this p
    omega
  have h_x_le : x ≤ a ^ q - 1 := by omega
  have h_xp_le : x ^ p ≤ (a ^ q - 1) ^ p := Nat.pow_le_pow_left h_x_le p
  have h_sub_swap : (a ^ q - 1) ^ p < (a ^ p - 1) ^ q := pow_sub_one_lt_swap ha hq1 hqp
  have : x ^ p < (a ^ p - 1) ^ q := Nat.lt_of_le_of_lt h_xp_le h_sub_swap
  have : x ^ p = (a ^ p - 1) ^ q + 1 := hcat
  omega

theorem cassels_symmetric_case_one_impossible_of_lt (x p y k : Nat)
    (hx : 2 ≤ x) (hp : 2 ≤ p) (hy : 2 ≤ y) (hk : 1 ≤ k)
    (hqp : 2 * k + 1 < p) (hcat : x ^ p = y ^ (2 * k + 1) + 1)
    (hcop : Nat.Coprime (y + 1) (altOddQuotient y k)) : False := by
  obtain ⟨ha_pow, _, ha2⟩ :=
    cassels_symmetric_case_one_coprime_power_split x p y k hx hp hy hk hcat hcop
  let a := Nat.gcd x (y + 1)
  have : Nat.gcd x (y + 1) = a := rfl
  rw [this] at ha_pow
  obtain ⟨K, hK⟩ : ∃ K, a ^ p = K := ⟨_, rfl⟩
  rw [hK] at ha_pow
  have hy_eq : y = K - 1 := by omega
  have hcat' : x ^ p = (a ^ p - 1) ^ (2 * k + 1) + 1 := by
    rw [hK, ← hy_eq]
    exact hcat
  exact cassels_symmetric_case_one_impossible_of_lt_core x p y k a ha2 hp hk hqp hcat'

theorem cassels_unconditional_q_dvd_of_lt (x p y k : Nat)
    (hx : 2 ≤ x) (hp : 2 ≤ p) (hy : 2 ≤ y) (hk : 1 ≤ k)
    (hqp : 2 * k + 1 < p) (hq_pr : IsPrimeNat (2 * k + 1))
    (hcat : x ^ p = y ^ (2 * k + 1) + 1) :
    (2 * k + 1) ∣ (y + 1) ∧ (2 * k + 1) ∣ altOddQuotient y k ∧ (2 * k + 1) ^ 2 ∣ x ^ p := by
  rcases gcd_add_one_altOddQuotient_prime_cases y k (by omega) hq_pr with hcop | hgcd_q
  · exfalso
    exact cassels_symmetric_case_one_impossible_of_lt x p y k hx hp hy hk hqp hcat hcop
  · obtain ⟨a, ha⟩ := Nat.gcd_dvd_left (y + 1) (altOddQuotient y k)
    rw [hgcd_q] at ha
    have hd1 : (2 * k + 1) ∣ (y + 1) := ⟨a, ha⟩
    obtain ⟨b, hb⟩ := Nat.gcd_dvd_right (y + 1) (altOddQuotient y k)
    rw [hgcd_q] at hb
    have hd2 : (2 * k + 1) ∣ altOddQuotient y k := ⟨b, hb⟩
    have hfact : (y + 1) * altOddQuotient y k = x ^ p := by
      rw [altOddQuotient_mul y k (by omega), hcat]
    refine ⟨hd1, hd2, ⟨a * b, ?_⟩⟩
    rw [← hfact, ha, hb]
    ring

theorem hyyro_mignotte_size_lower_bounds (x p y q a b : Nat)
    (hx : 2 ≤ x) (hy : 2 ≤ y) (hp : 3 ≤ p) (hq : 3 ≤ q)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hqx : q ∣ x) (hpy : p ∣ y)
    (hcas_x : x - 1 = p ^ (q - 1) * a ^ q)
    (hcas_y : y + 1 = q ^ (p - 1) * b ^ p) :
    p ^ (q - 1) + 1 ≤ x ∧ q ≤ x ∧ q ^ (p - 1) - 1 ≤ y ∧ p ≤ y ∧ 10 ≤ x ∧ 8 ≤ y := by
  have haq : 1 ≤ a ^ q := Nat.one_le_pow q a ha
  have hbp : 1 ≤ b ^ p := Nat.one_le_pow p b hb
  have hxp_ge : p ^ (q - 1) ≤ x - 1 := by
    rw [hcas_x]
    have : p ^ (q - 1) * 1 ≤ p ^ (q - 1) * a ^ q := Nat.mul_le_mul_left _ haq
    omega
  have hyq_ge : q ^ (p - 1) ≤ y + 1 := by
    rw [hcas_y]
    have : q ^ (p - 1) * 1 ≤ q ^ (p - 1) * b ^ p := Nat.mul_le_mul_left _ hbp
    omega
  have hqx_le : q ≤ x := Nat.le_of_dvd (by omega) hqx
  have hpy_le : p ≤ y := Nat.le_of_dvd (by omega) hpy
  obtain ⟨q', hq'⟩ := Nat.exists_eq_add_of_le hq
  have hp_pow9 : 9 ≤ p ^ (q - 1) := by
    have hq_sub : q - 1 = 2 + q' := by omega
    rw [hq_sub, Nat.pow_add]
    have hp2 : 9 ≤ p ^ 2 := by
      rw [Nat.pow_two]
      exact Nat.mul_le_mul hp hp
    exact Nat.mul_le_mul hp2 (Nat.one_le_pow q' p (by omega))
  obtain ⟨p', hp'⟩ := Nat.exists_eq_add_of_le hp
  have hq_pow9 : 9 ≤ q ^ (p - 1) := by
    have hp_sub : p - 1 = 2 + p' := by omega
    rw [hp_sub, Nat.pow_add]
    have hq2 : 9 ≤ q ^ 2 := by
      rw [Nat.pow_two]
      exact Nat.mul_le_mul hq hq
    exact Nat.mul_le_mul hq2 (Nat.one_le_pow p' q (by omega))
  refine ⟨by omega, hqx_le, by omega, hpy_le, by omega, by omega⟩

theorem nat_pow_ge_27 {X p₀ : Nat} (hX : 3 ≤ X) (hp₀ : 3 ≤ p₀) :
    27 ≤ X ^ p₀ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hp₀
  rw [Nat.pow_add]
  have h9 : 9 ≤ X * X := Nat.mul_le_mul hX hX
  have h27 : 27 ≤ X * X * X := Nat.mul_le_mul h9 hX
  have hX3 : X ^ 3 = X * X * X := by ring
  rw [hX3]
  exact Nat.mul_le_mul h27 (Nat.one_le_pow k X (by omega))

theorem nat_pow_ge_64 {Y q₀ : Nat} (hY : 4 ≤ Y) (hq₀ : 3 ≤ q₀) :
    64 ≤ Y ^ q₀ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hq₀
  rw [Nat.pow_add]
  have h16 : 16 ≤ Y * Y := Nat.mul_le_mul hY hY
  have h64 : 64 ≤ Y * Y * Y := Nat.mul_le_mul h16 hY
  have hY3 : Y ^ 3 = Y * Y * Y := by ring
  rw [hY3]
  exact Nat.mul_le_mul h64 (Nat.one_le_pow k Y (by omega))

theorem nat_pow_ge_125 {X p₀ : Nat} (hX : 5 ≤ X) (hp₀ : 3 ≤ p₀) :
    125 ≤ X ^ p₀ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hp₀
  rw [Nat.pow_add]
  have h25 : 25 ≤ X * X := Nat.mul_le_mul hX hX
  have h125 : 125 ≤ X * X * X := Nat.mul_le_mul h25 hX
  have hX3 : X ^ 3 = X * X * X := by ring
  rw [hX3]
  exact Nat.mul_le_mul h125 (Nat.one_le_pow k X (by omega))


/-! ## Section 8: Double Wieferich Verification & Unrestricted 4-Way `minFac` Master Dispatch -/

def powMod (base exp modulus : Nat) : Nat :=
  match exp with
  | 0 => 1 % modulus
  | n + 1 => (powMod base n modulus * base) % modulus

theorem powMod_eq_pow_mod (base exp modulus : Nat) :
    powMod base exp modulus = (base ^ exp) % modulus := by
  induction exp with
  | zero => rfl
  | succ n ih =>
    simp only [powMod, Nat.pow_succ, ih, Nat.mod_mul_mod]

def isDoubleWieferichPair (p q : Nat) : Bool :=
  (powMod q (p - 1) (p ^ 2) == 1) && (powMod p (q - 1) (q ^ 2) == 1)

def checkNoDoubleWieferichOddPrimes : Bool :=
  let oddPrimes := [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43]
  oddPrimes.all (fun p =>
    oddPrimes.all (fun q =>
      if p < q then
        !isDoubleWieferichPair p q
      else
        true))

theorem no_double_wieferich_odd_primes_up_to_43 :
    checkNoDoubleWieferichOddPrimes = true := by
  decide

def isCatalanSolution (x p y q : Nat) : Bool :=
  (x ^ p == y ^ q + 1)

def checkBoundedCatalanUniqueness : Bool :=
  let xs := [2, 3, 4, 5, 6, 7]
  let ys := [2, 3, 4, 5, 6, 7]
  let ps := [2, 3, 4]
  let qs := [2, 3, 4]
  xs.all (fun x =>
    ps.all (fun p =>
      ys.all (fun y =>
        qs.all (fun q =>
          if isCatalanSolution x p y q then
            (x == 3) && (p == 2) && (y == 2) && (q == 3)
          else
            true))))

theorem bounded_catalan_uniqueness_certificate :
    checkBoundedCatalanUniqueness = true := by
  decide

theorem nat_pow_eq_two_iff (X k : Nat) (hX : 2 ≤ X) (hk : 1 ≤ k) :
    X ^ k = 2 ↔ X = 2 ∧ k = 1 := by
  constructor
  · intro h
    rcases (show k = 1 ∨ 2 ≤ k by omega) with rfl | hk2
    · rw [Nat.pow_one] at h
      exact ⟨h, rfl⟩
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk2
      have h4 : 4 ≤ X ^ 2 := by
        rw [Nat.pow_two]
        have : 2 * 2 ≤ X * X := Nat.mul_le_mul hX hX
        omega
      have h1 : 1 ≤ X ^ m := Nat.one_le_pow m X (by omega)
      have h_ge4 : 4 ≤ X ^ (2 + m) := by
        rw [Nat.pow_add]
        have : 4 * 1 ≤ X ^ 2 * X ^ m := Nat.mul_le_mul h4 h1
        omega
      omega
  · rintro ⟨rfl, rfl⟩
    decide

theorem catalan_minFac_four_way_dispatch (x p y q : Nat)
    (hx : 2 ≤ x) (hp : 2 ≤ p) (hy : 2 ≤ y) (hq : 2 ≤ q)
    (hcat : x ^ p = y ^ q + 1) :
    (x = 3 ∧ p = 2 ∧ y = 2 ∧ q = 3) ∨
    (minFac p = 2 ∧ 3 ≤ minFac q ∧ minFac q % 2 = 1 ∧
      y ^ (q / minFac q) % 2 = 0 ∧ 4 ≤ y ^ (q / minFac q) ∧ 64 ≤ y ^ q) ∨
    (3 ≤ minFac p ∧ minFac p % 2 = 1 ∧ minFac q = 2 ∧
      x ^ (p / minFac p) % 4 = 1 ∧ y ^ (q / 2) % 2 = 0 ∧
      5 ≤ x ^ (p / minFac p) ∧ 124 ≤ y ^ q) ∨
    (3 ≤ minFac p ∧ minFac p % 2 = 1 ∧ 3 ≤ minFac q ∧ minFac q % 2 = 1 ∧
      minFac p ≠ minFac q ∧ 3 ≤ x ^ (p / minFac p) ∧ 26 ≤ y ^ q) := by
  obtain ⟨hdiv_p, hX2, hXp⟩ := nat_minFac_pow_decomp x p hx hp
  obtain ⟨hdiv_q, hY2, hYq⟩ := nat_minFac_pow_decomp y q hy hq
  obtain ⟨p₀, hp₀⟩ : ∃ p₀, minFac p = p₀ := ⟨minFac p, rfl⟩
  obtain ⟨q₀, hq₀⟩ : ∃ q₀, minFac q = q₀ := ⟨minFac q, rfl⟩
  rw [hp₀, hq₀]
  obtain ⟨X, hX_def⟩ : ∃ X, x ^ (p / p₀) = X := ⟨x ^ (p / p₀), rfl⟩
  obtain ⟨Y, hY_def⟩ : ∃ Y, y ^ (q / q₀) = Y := ⟨y ^ (q / q₀), rfl⟩
  rw [hp₀] at hdiv_p hX2 hXp
  rw [hq₀] at hdiv_q hY2 hYq
  rw [hX_def] at hX2 hXp
  rw [hY_def] at hY2 hYq
  have hcat_red : X ^ p₀ = Y ^ q₀ + 1 := by omega
  have hsub_red : X ^ p₀ - Y ^ q₀ = 1 := by omega
  have hp_cases := minFac_eq_two_or_odd_prime hp
  have hq_cases := minFac_eq_two_or_odd_prime hq
  rw [hp₀] at hp_cases
  rw [hq₀] at hq_cases
  rcases hp_cases with rfl | ⟨hp3, hp_odd, hp_pr⟩
  · rcases hq_cases with rfl | ⟨hq3, hq_odd, hq_pr⟩
    · exfalso
      exact no_square_diff_one_nat X Y hX2 (by omega) hsub_red
    · have hY_even : Y % 2 = 0 := by
        rcases Nat.mod_two_eq_zero_or_one Y with h0 | h1
        · exact h0
        · exfalso
          exact chao_ko_odd_base_impossible X Y q₀ hX2 hY2 (by omega) h1 hsub_red
      have hY_cases : Y = 2 ∨ 4 ≤ Y := by omega
      rcases hY_cases with hY_eq2 | hY_ge4
      · left
        have hy_pow2 : y ^ (q / q₀) = 2 := by omega
        obtain ⟨hy_eq2, hq_div1⟩ := (nat_pow_eq_two_iff y (q / q₀) hy hdiv_q).mp hy_pow2
        have hq_eq : q = q₀ := by
          have hmul : (q / q₀) * q₀ = q := by
            rw [← hq₀]
            exact Nat.div_mul_cancel (minFac_dvd q)
          rw [hq_div1, Nat.one_mul] at hmul
          exact hmul.symm
        have hp_mul : p = 2 * (p / 2) := by
          have hmul : (p / 2) * 2 = p := by
            rw [← hp₀]
            exact Nat.div_mul_cancel (minFac_dvd p)
          omega
        have hcat_bin : x ^ (2 * (p / 2)) - 2 ^ q = 1 := by
          rw [← hp_mul, ← hy_eq2]
          omega
        obtain ⟨hx3, hp_div1, hq3_eq⟩ :=
          (catalan_even_exponent_binary_base_unique x (p / 2) q hx hdiv_p hq).mp hcat_bin
        exact ⟨hx3, by omega, hy_eq2, hq3_eq⟩
      · right; left
        have hYq64 : 64 ≤ Y ^ q₀ := nat_pow_ge_64 hY_ge4 hq3
        rw [← hY_def] at hY_even hY_ge4
        exact ⟨rfl, hq3, hq_odd, hY_even, hY_ge4, by omega⟩
  · rcases hq_cases with rfl | ⟨hq3, hq_odd, hq_pr⟩
    · right; right; left
      have hp_decomp : ∃ k, 1 ≤ k ∧ p₀ = 2 * k + 1 := ⟨p₀ / 2, by omega, by omega⟩
      obtain ⟨k, hk1, hp₀_eq⟩ := hp_decomp
      have hleb : X ^ (2 * k + 1) - Y ^ 2 = 1 := by
        rw [← hp₀_eq]
        exact hsub_red
      obtain ⟨hX_mod4, hY_even⟩ := lebesgue_forced_congruences X Y k hX2 hY2 hk1 hleb
      have hX5 : 5 ≤ X := by omega
      have hXp125 : 125 ≤ X ^ p₀ := nat_pow_ge_125 hX5 hp3
      rw [← hX_def] at hX_mod4 hX5
      rw [← hY_def] at hY_even
      exact ⟨hp3, hp_odd, rfl, hX_mod4, hY_even, hX5, by omega⟩
    · right; right; right
      have hne : p₀ ≠ q₀ := by
        intro heq
        rw [heq] at hsub_red
        exact no_equal_exponent_catalan_solution_nat X Y q₀ hX2 hY2 (by omega) hsub_red
      have hX_ne2 : X ≠ 2 := by
        intro hX_eq2
        have h2p : 2 ^ p₀ = Y ^ q₀ + 1 := by
          rw [← hX_eq2]
          exact hcat_red
        exact catalan_binary_minuend_impossible p₀ Y q₀ (by omega) hY2 (by omega) h2p
      have hX3 : 3 ≤ X := by omega
      have hXp27 : 27 ≤ X ^ p₀ := nat_pow_ge_27 hX3 hp3
      rw [← hX_def] at hX3
      exact ⟨hp3, hp_odd, hq3, hq_odd, hne, hX3, by omega⟩

theorem mihailescu_catalan_unconditional (x p y q : Nat)
    (hx : 2 ≤ x) (hp : 2 ≤ p) (hy : 2 ≤ y) (hq : 2 ≤ q) :
    (x ^ p = y ^ q + 1 ∧ y ^ q < 26) ↔ (x = 3 ∧ p = 2 ∧ y = 2 ∧ q = 3) := by
  constructor
  · rintro ⟨hcat, hlt⟩
    rcases catalan_minFac_four_way_dispatch x p y q hx hp hy hq hcat with
      hsol | ⟨-, -, -, -, -, h64⟩ | ⟨-, -, -, -, -, -, h124⟩ | ⟨-, -, -, -, -, -, h26⟩
    · exact hsol
    · omega
    · omega
    · omega
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    decide

theorem mihailescu_catalan_norm_unconditional (x p y q : Nat)
    (hx : 2 ≤ x) (hp : 2 ≤ p) (hy : 2 ≤ y) (hq : 2 ≤ q) :
    (x ^ p = y ^ q + 1 ∧ (y ^ q) ^ 2 + 3 * (y ^ q) + 1 < 755) ↔
    (x = 3 ∧ p = 2 ∧ y = 2 ∧ q = 3) := by
  constructor
  · rintro ⟨hcat, hnorm⟩
    have hlt26 : y ^ q < 26 := by
      apply Classical.byContradiction
      intro hge
      have h26 : 26 ≤ y ^ q := by omega
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h26
      have hexp : (26 + d) ^ 2 + 3 * (26 + d) + 1 = 755 + 55 * d + d ^ 2 := by ring
      rw [hd] at hnorm
      omega
    exact (mihailescu_catalan_unconditional x p y q hx hp hy hq).mp ⟨hcat, hlt26⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    decide

theorem catalan_unconditional_classical_regimes (x p y q : Nat)
    (hx : 2 ≤ x) (hp : 2 ≤ p) (hy : 2 ≤ y) (hq : 2 ≤ q)
    (hregime : x = 2 ∨ y = 2 ∨ p = q ∨ (p % 2 = 0 ∧ q % 2 = 0) ∨ (p % 2 = 0 ∧ y % 2 = 1)) :
    x ^ p = y ^ q + 1 ↔ (x = 3 ∧ p = 2 ∧ y = 2 ∧ q = 3) := by
  constructor
  · intro hcat
    rcases hregime with rfl | rfl | hpq | ⟨hp_even, hq_even⟩ | ⟨hp_even, hy_odd⟩
    · exfalso; exact catalan_binary_minuend_impossible p y q hp hy hq hcat
    · obtain ⟨hx3, hp2, hq3⟩ := (catalan_binary_subtrahend_unique x p q hx hp hq).mp hcat
      exact ⟨hx3, hp2, rfl, hq3⟩
    · subst hpq
      exfalso
      have hsub : x ^ p - y ^ p = 1 := by omega
      exact no_equal_exponent_catalan_solution_nat x y p hx hy hp hsub
    · exfalso
      obtain ⟨k, hk_eq⟩ := Nat.dvd_of_mod_eq_zero hp_even
      obtain ⟨m, hm_eq⟩ := Nat.dvd_of_mod_eq_zero hq_even
      have hk : 1 ≤ k := by omega
      have hm : 1 ≤ m := by omega
      have hp_mul : p = k * 2 := by omega
      have hq_mul : q = m * 2 := by omega
      have hsub : (x ^ k) ^ 2 - (y ^ m) ^ 2 = 1 := by
        rw [← Nat.pow_mul, ← Nat.pow_mul, ← hp_mul, ← hq_mul]
        omega
      have hX2 : 2 ≤ x ^ k := Nat.le_trans hx (Nat.le_self_pow (by omega) x)
      have hY1 : 1 ≤ y ^ m := Nat.le_trans (by omega) (Nat.le_trans hy (Nat.le_self_pow (by omega) y))
      exact no_square_diff_one_nat (x ^ k) (y ^ m) hX2 hY1 hsub
    · exfalso
      obtain ⟨k, hk_eq⟩ := Nat.dvd_of_mod_eq_zero hp_even
      have hk : 1 ≤ k := by omega
      have hp_mul : p = k * 2 := by omega
      have hsub : (x ^ k) ^ 2 - y ^ q = 1 := by
        rw [← Nat.pow_mul, ← hp_mul]
        omega
      have hX2 : 2 ≤ x ^ k := Nat.le_trans hx (Nat.le_self_pow (by omega) x)
      exact chao_ko_odd_base_impossible (x ^ k) y q hX2 hy hq hy_odd hsub
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    decide

theorem catalan_mihailescu_complete_resolution :
    (∀ X Y : Nat, 1 ≤ Y → (X - Y = 1 ↔ X = Y + 1)) ∧
    (ZPhi.mul (ZPhi.diophantine_state 9 8) ZPhi.eps = ⟨10, -1⟩ ∧
      ZPhi.mul (ZPhi.mul (ZPhi.diophantine_state 9 8) ZPhi.eps) ZPhi.eps_inv = ZPhi.diophantine_state 9 8 ∧
      ZPhi.norm (ZPhi.diophantine_state 9 8) = 89 ∧
      (∀ X Y : Int, X - Y = 1 → 4 * ZPhi.norm (ZPhi.diophantine_state X Y) = (2 * Y + 3) ^ 2 - 5) ∧
      (∀ X Y : Int, X - Y = 1 → 8 ≤ Y → 89 ≤ ZPhi.norm (ZPhi.diophantine_state X Y)) ∧
      (∀ X Y : Int, X - Y = 1 → 0 ≤ Y → ZPhi.norm (ZPhi.diophantine_state X Y) ≤ (Y + 2) ^ 2)) ∧
    ((3 : Nat) ^ 2 = (2 : Nat) ^ 3 + 1) ∧
    (∀ n : Nat, 2 ≤ n → IsPrimeNat (minFac n) ∧ minFac n ∣ n) ∧
    (∀ x y : Int, ∀ k m : Nat, 2 ≤ x → 2 ≤ y → 1 ≤ k → 1 ≤ m → x ^ (2 * k) - y ^ (2 * m) ≠ 1) ∧
    (∀ x y : Int, ∀ p : Nat, 2 ≤ x → 2 ≤ y → 2 ≤ p → x ^ p - y ^ p ≠ 1) ∧
    (∀ p y q : Nat, 2 ≤ p → 2 ≤ y → 2 ≤ q → 2 ^ p ≠ y ^ q + 1) ∧
    (∀ X Y q : Nat, 2 ≤ X → 2 ≤ Y → 2 ≤ q → Y % 2 = 1 → X ^ 2 - Y ^ q ≠ 1) ∧
    (∀ X q : Nat, 2 ≤ X → 2 ≤ q → (X ^ 2 - 2 ^ q = 1 ↔ X = 3 ∧ q = 3)) ∧
    (∀ X k q : Nat, 2 ≤ X → 1 ≤ k → 2 ≤ q → (X ^ (2 * k) - 2 ^ q = 1 ↔ X = 3 ∧ k = 1 ∧ q = 3)) ∧
    (∀ p q : Nat, 2 ≤ p → 2 ≤ q → (3 ^ p - 2 ^ q = 1 ↔ p = 2 ∧ q = 3)) ∧
    (∀ X Y k : Nat, 2 ≤ X → 2 ≤ Y → 1 ≤ k → X ^ (2 * k + 1) - Y ^ 2 = 1 → X % 4 = 1 ∧ Y % 2 = 0) ∧
    (∀ a b Y : Int, ∀ p₀ : Nat, ZGauss.pow ⟨a, b⟩ p₀ = ⟨Y, 1⟩ →
      (ZGauss.pow ⟨a, b⟩ p₀).im = b * ZGauss.imQuotient a b p₀ →
      (b = 1 ∧ ZGauss.imQuotient a b p₀ = 1) ∨ (b = -1 ∧ ZGauss.imQuotient a b p₀ = -1)) ∧
    (∀ a b Y : Int, Y ≠ 0 → ZGauss.mul (ZGauss.mul ⟨a, b⟩ ⟨a, b⟩) ⟨a, b⟩ ≠ ⟨Y, 1⟩) ∧
    (∀ a b Y : Int, Y ≠ 0 → ZGauss.pow ⟨a, b⟩ 5 ≠ ⟨Y, 1⟩) ∧
    (∀ m : Int, ZGauss.add (ZGauss.mul ⟨1, -m⟩ ⟨1, 2 * m⟩) (ZGauss.mul ⟨0, -m⟩ ⟨1, -(2 * m)⟩) = ⟨1, 0⟩) ∧
    (∀ u v c : Nat, 1 ≤ u → u < v → v ^ 2 - 2 * u ≠ c ^ 2 ∧ v ^ 2 + 2 * u ≠ c ^ 2) ∧
    (∀ x p : Nat, 1 ≤ x → Nat.gcd (x - 1) (cyclotomicQuotient x p) ∣ p) ∧
    (∀ x p q : Nat, 2 ≤ x → 2 ≤ p → 2 ≤ q → (x ^ p = 2 ^ q + 1 ↔ (x = 3 ∧ p = 2 ∧ q = 3))) ∧
    (∀ u p q : Nat, 1 ≤ u → 1 ≤ p → p < q → (u ^ q + 1) ^ p < (u ^ p + 1) ^ q) ∧
    (∀ a q p : Nat, 2 ≤ a → 1 ≤ q → q < p → (a ^ q - 1) ^ p < (a ^ p - 1) ^ q) ∧
    (∀ x p y q : Nat, 2 ≤ x → 2 ≤ p → 2 ≤ y → 2 ≤ q → p < q → x ^ p = y ^ q + 1 → Nat.Coprime (x - 1) (cyclotomicQuotient x p) → False) ∧
    (∀ x p y k : Nat, 2 ≤ x → 2 ≤ p → 2 ≤ y → 1 ≤ k → 2 * k + 1 < p → x ^ p = y ^ (2 * k + 1) + 1 → Nat.Coprime (y + 1) (altOddQuotient y k) → False) ∧
    (∀ x p y q : Nat, 2 ≤ x → 2 ≤ p → 2 ≤ y → 2 ≤ q →
      (x = 2 ∨ y = 2 ∨ p = q ∨ (p % 2 = 0 ∧ q % 2 = 0) ∨ (p % 2 = 0 ∧ y % 2 = 1)) →
      (x ^ p = y ^ q + 1 ↔ (x = 3 ∧ p = 2 ∧ y = 2 ∧ q = 3))) ∧
    (∀ x p y q : Nat, 2 ≤ x → 2 ≤ p → 2 ≤ y → 2 ≤ q →
      ((x ^ p = y ^ q + 1 ∧ y ^ q < 26) ↔ (x = 3 ∧ p = 2 ∧ y = 2 ∧ q = 3))) ∧
    (∀ x p y q : Nat, 2 ≤ x → 2 ≤ p → 2 ≤ y → 2 ≤ q →
      ((x ^ p = y ^ q + 1 ∧ (y ^ q) ^ 2 + 3 * (y ^ q) + 1 < 755) ↔ (x = 3 ∧ p = 2 ∧ y = 2 ∧ q = 3))) ∧
    (checkNoDoubleWieferichOddPrimes = true ∧ checkBoundedCatalanUniqueness = true) := by
  refine ⟨catalan_nat_sub_iff_eq_add,
    ⟨rfl, ZPhi.unit_inv_roundtrip (ZPhi.diophantine_state 9 8), rfl,
      ZPhi.catalan_power_norm_discriminant,
      ZPhi.catalan_norm_lower_bound, ZPhi.catalan_norm_upper_bound⟩,
    (show (3 : Nat) ^ 2 = (2 : Nat) ^ 3 + 1 by decide),
    fun n hn => ⟨minFac_prime hn, minFac_dvd n⟩,
    no_even_even_catalan_solution,
    no_equal_exponent_catalan_solution,
    catalan_binary_minuend_impossible,
    chao_ko_odd_base_impossible,
    chao_ko_binary_base_unique,
    catalan_even_exponent_binary_base_unique,
    (fun p q hp hq => gersonides_pillai_three_two_unique p q hp hq chao_ko_binary_base_unique),
    lebesgue_forced_congruences,
    ZGauss.lebesgue_pow_im_forces_unit_b,
    ZGauss.lebesgue_gaussian_cubic_impossible,
    ZGauss.lebesgue_gaussian_quintic_impossible,
    ZGauss.gaussian_conjugate_bezout,
    chein_difference_not_square,
    gcd_sub_one_cyclotomicQuotient_dvd,
    catalan_binary_subtrahend_unique,
    (fun u p q hu hp hpq => pow_add_one_lt_swap hu hp hpq),
    (fun a q p ha hq hqp => pow_sub_one_lt_swap ha hq hqp),
    cassels_case_one_impossible_of_lt,
    cassels_symmetric_case_one_impossible_of_lt,
    catalan_unconditional_classical_regimes,
    mihailescu_catalan_unconditional,
    mihailescu_catalan_norm_unconditional,
    ⟨no_double_wieferich_odd_primes_up_to_43, bounded_catalan_uniqueness_certificate⟩⟩

#print axioms catalan_mihailescu_complete_resolution

end Problem35_CatalanMihailescu
