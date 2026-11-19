import Mathlib

/-!
# JSP-000183 (Erdős Problem #193): Infinite Small-Step Walk in `ℤ³` with No Collinear Triple

- **Catalog ID:** `JSP-000183` (`catalog-0101-0200.md`)
- **Live Catalog Status:** `Current status: Solved`, `Lean proof: No`
- **Problem Statement:** Must an infinite walk in three-dimensional space using a finite set of
  step vectors visit three collinear points?
- **Historical & Mathematical Sources:**
  - J. L. Gerver and L. M. Ramsey (1979), *On certain sequences of lattice points*,
    Pacific J. Math. 83 (1979), 357–363.
  - S. Cambie and E. Kälviäinen (2026), *An infinite small-step $\mathbb{Z}^3$-walk with no
    collinear triple*, `arXiv:2609.01766`.
- **Answer:** **No.** We formalize the explicit binary-weight Gaussian-walk construction in `ℤ³`
  with step vectors `P (n + 1) - P n ∈ { -2, -1, 0, 1, 2 }² × { 1, …, 7 }` (hence using a
  finite set of step vectors, at most 16 transitions determined by `(α n, α (n + 1))`), strictly
  increasing height coordinate `hWalk` (making `P` injective), and **no three collinear points**
  both over `ℤ³` (no nontrivial integer affine dependence / zero cross product) and over `ℝ³`
  (`¬ Collinear ℝ {PReal m, PReal n, PReal k}` and `AffineIndependent ℝ ![PReal m, PReal n, PReal k]`
  for all `m < n < k`).

## Proof Architecture (Exact Arithmetic & 2-adic Valuations)
1. **Binary digit sum `s2` and state `α : ℕ → Fin 4`:** Define `α n = ⟨s2 n % 4, _⟩` and prove
   `s2 (2 * n) = s2 n`, `s2 (2 * n + 1) = s2 n + 1`, so `α (2 * n) = α n` and
   `α (2 * n + 1) = stepAlpha (α n)`.
2. **Gaussian walk `zWalk : ℕ → ℤ × ℤ`:** Accumulate `unitStep (α n) ∈ {(1,0),(0,1),(-1,0),(0,-1)}`
   representing `i^{α n} ∈ ℤ[i]`, and prove the exact doubling recurrences
   `zWalk (2 * n) = (1 + i) * zWalk n` and `zWalk (2 * n + 1) = (1 + i) * zWalk n + u_n`.
3. **Planar 2-adic valuation identity (`v2_sqNorm_zWalk_diff`):** Using `Nat.factorization · 2` on
   `sqNorm (dx, dy) = dx.natAbs ^ 2 + dy.natAbs ^ 2`, strong induction gives
   `v₂(‖zWalk n - zWalk m‖²) = v₂(n - m)` whenever `m < n` and `α m = α n`.
4. **3D embedding `P n = (wWalk n, hWalk n)`:** Set `wWalk n = 2 * zWalk n + corner (α n)` with
   corners `0, i, -1 + i, -1` and `hWalk n = 4 * n + (α n).val`. Case analysis on
   `(α m, α n) : Fin 4 × Fin 4` proves the unconditional exact identity
   `v₂(‖wWalk n - wWalk m‖²) = v₂(hWalk n - hWalk m)` for ALL `m < n`.
5. **Non-collinearity in `ℤ³` and `ℝ³`:** If `P m, P n, P k` (`m < n < k`) were collinear,
   comparing coordinates yields both
   `(h k - h m) • (w n - w m) = (h n - h m) • (w k - w m)` and
   `(h k - h n) • (w n - w m) = (h n - h m) • (w k - w n)`.
   Taking `sqNorm` and `Nat.factorization · 2` forces
   `v₂(h n - h m) = v₂(h k - h m) = v₂(h k - h n)`, contradicting
   `v₂(a) < v₂(a + c)` for `(h n - h m) + (h k - h n) = h k - h m`.

## Formal Guarantees
- Unconditional, zero `sorry`, zero `admit`, zero custom axioms
  (`#print axioms` strictly a subset of `[propext, Classical.choice, Quot.sound]`),
  zero `native_decide`, zero approximations, zero warnings under `-DautoImplicit=false`.
-/

namespace JSP_000183

open Set Affine

/-! ### 1. Exact 2-Adic Valuation Helpers via `Nat.factorization · 2` -/

lemma factorization_two_eq_zero_of_odd {n : ℕ} (hn : n % 2 = 1) : n.factorization 2 = 0 :=
  Nat.factorization_eq_zero_of_not_dvd (by omega)

lemma factorization_two_two_mul {n : ℕ} (hn : n ≠ 0) :
    (2 * n).factorization 2 = n.factorization 2 + 1 := by
  rw [Nat.factorization_mul (by decide) hn, Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_two]
  omega

lemma factorization_two_four_mul {n : ℕ} (hn : n ≠ 0) :
    (4 * n).factorization 2 = n.factorization 2 + 2 := by
  have heq : 4 * n = 2 * (2 * n) := by omega
  rw [heq, factorization_two_two_mul (by omega), factorization_two_two_mul hn]

lemma factorization_two_eq_one_of_mod_four {n : ℕ} (h : n % 4 = 2) : n.factorization 2 = 1 := by
  have hn : n ≠ 0 := by omega
  have h1 : n = 2 * (n / 2) := by omega
  have hodd : (n / 2) % 2 = 1 := by omega
  have hne : n / 2 ≠ 0 := by omega
  rw [h1, factorization_two_two_mul hne, factorization_two_eq_zero_of_odd hodd]

lemma factorization_two_sq {n : ℕ} (_hn : n ≠ 0) :
    (n ^ 2).factorization 2 = 2 * n.factorization 2 := by
  rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]

lemma div_pow_factorization_two_mod_two {n : ℕ} (hn : n ≠ 0) :
    (n / 2 ^ (n.factorization 2)) % 2 = 1 := by
  set v := n.factorization 2
  set m := n / 2 ^ v
  have hdvd : 2 ^ v ∣ n := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hn).mpr le_rfl
  have hdecomp : 2 ^ v * m = n := Nat.mul_div_cancel' hdvd
  have hm_ne : m ≠ 0 := by
    intro hm0
    rw [hm0, mul_zero] at hdecomp
    exact hn hdecomp.symm
  have hp_ne : (2 ^ v : ℕ) ≠ 0 := (Nat.pow_pos (by decide)).ne'
  have hfact : n.factorization 2 = v + m.factorization 2 := by
    rw [← hdecomp, Nat.factorization_mul hp_ne hm_ne, Finsupp.add_apply,
      Nat.factorization_pow_self Nat.prime_two]
  have hm0 : m.factorization 2 = 0 := by
    have : v = n.factorization 2 := rfl
    omega
  have hndvd : ¬ (2 ∣ m) := by
    intro hdvd2
    have h1 := (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hm_ne).mp hdvd2
    omega
  omega

lemma factorization_two_add_gt {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (heq : a.factorization 2 = b.factorization 2) :
    a.factorization 2 < (a + b).factorization 2 := by
  set v := a.factorization 2
  set a' := a / 2 ^ v
  set b' := b / 2 ^ (b.factorization 2)
  have ha_eq : 2 ^ v * a' = a :=
    Nat.mul_div_cancel' ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two ha).mpr le_rfl)
  have hb_eq : 2 ^ v * b' = b := by
    have hdvd : 2 ^ (b.factorization 2) ∣ b :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hb).mpr le_rfl
    dsimp [b']
    rw [← heq] at hdvd ⊢
    exact Nat.mul_div_cancel' hdvd
  have ha_mod : a' % 2 = 1 := div_pow_factorization_two_mod_two ha
  have hb_mod : b' % 2 = 1 := div_pow_factorization_two_mod_two hb
  have hdvd2 : 2 ∣ a' + b' := ⟨(a' + b') / 2, by omega⟩
  rcases hdvd2 with ⟨k, hk⟩
  have hsum : a + b = 2 ^ (v + 1) * k := by
    rw [← ha_eq, ← hb_eq, ← mul_add, hk, pow_succ]
    ring
  have hdvd : 2 ^ (v + 1) ∣ a + b := ⟨k, hsum⟩
  have hab_ne : a + b ≠ 0 := by omega
  have hle : v + 1 ≤ (a + b).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hab_ne).mp hdvd
  omega

/-! ### 2. Binary Digit Sum, Mod-4 Automaton, and Gaussian Lattice Walk -/

/-- Binary digit sum `s₂(n)` (number of `1`s in the binary expansion of `n`). -/
def s2 (n : ℕ) : ℕ :=
  if h : n = 0 then 0 else n % 2 + s2 (n / 2)
termination_by n
decreasing_by omega

lemma s2_zero : s2 0 = 0 := by rw [s2]; simp

lemma s2_pos_eq {n : ℕ} (hn : n ≠ 0) : s2 n = n % 2 + s2 (n / 2) := by
  conv_lhs => rw [s2]
  simp [hn]

lemma s2_two_mul (n : ℕ) : s2 (2 * n) = s2 n := by
  by_cases hn : n = 0
  · subst hn; simp [s2_zero]
  · rw [s2_pos_eq (by omega)]
    have hmod : (2 * n) % 2 = 0 := by omega
    have hdiv : (2 * n) / 2 = n := by omega
    rw [hmod, hdiv, zero_add]

lemma s2_two_mul_add_one (n : ℕ) : s2 (2 * n + 1) = s2 n + 1 := by
  rw [s2_pos_eq (by omega)]
  have hmod : (2 * n + 1) % 2 = 1 := by omega
  have hdiv : (2 * n + 1) / 2 = n := by omega
  rw [hmod, hdiv, add_comm]

/-- Mod-4 rotation state `α n = s2 n mod 4 : Fin 4`. -/
def alpha (n : ℕ) : Fin 4 :=
  ⟨s2 n % 4, Nat.mod_lt _ (by decide)⟩

/-- Cyclic increment on `Fin 4`. -/
def stepAlpha (a : Fin 4) : Fin 4 :=
  ⟨(a.val + 1) % 4, Nat.mod_lt _ (by decide)⟩

lemma alpha_two_mul (n : ℕ) : alpha (2 * n) = alpha n := by
  apply Fin.ext
  dsimp [alpha]
  rw [s2_two_mul]

lemma alpha_two_mul_add_one (n : ℕ) : alpha (2 * n + 1) = stepAlpha (alpha n) := by
  apply Fin.ext
  dsimp [alpha, stepAlpha]
  rw [s2_two_mul_add_one]
  omega

/-- Unit step vectors `1, i, -1, -i` in `ℤ × ℤ`. -/
def unitStep : Fin 4 → ℤ × ℤ
  | 0 => (1, 0)
  | 1 => (0, 1)
  | 2 => (-1, 0)
  | 3 => (0, -1)

/-- Multiplication by `(1 + i)` on `ℤ × ℤ`. -/
def rot1i (p : ℤ × ℤ) : ℤ × ℤ :=
  (p.1 - p.2, p.1 + p.2)

lemma unitStep_pair (a : Fin 4) :
    (unitStep a).1 + (unitStep (stepAlpha a)).1 = (rot1i (unitStep a)).1 ∧
    (unitStep a).2 + (unitStep (stepAlpha a)).2 = (rot1i (unitStep a)).2 := by
  fin_cases a <;> decide

/-- Gaussian-integer walk `z_n = ∑_{r < n} i^{s2 r}`. -/
def zWalk : ℕ → ℤ × ℤ
  | 0 => (0, 0)
  | n + 1 =>
    let z := zWalk n
    let u := unitStep (alpha n)
    (z.1 + u.1, z.2 + u.2)

lemma zWalk_succ (n : ℕ) :
    zWalk (n + 1) = ((zWalk n).1 + (unitStep (alpha n)).1, (zWalk n).2 + (unitStep (alpha n)).2) := rfl

lemma zWalk_two_mul (n : ℕ) : zWalk (2 * n) = rot1i (zWalk n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have heq : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
    rw [heq, zWalk_succ, zWalk_succ, ih, zWalk_succ, alpha_two_mul, alpha_two_mul_add_one]
    obtain ⟨hx, hy⟩ := unitStep_pair (alpha n)
    dsimp [rot1i] at hx hy ⊢
    ext <;> omega

lemma zWalk_two_mul_add_one (n : ℕ) :
    zWalk (2 * n + 1) =
      ((rot1i (zWalk n)).1 + (unitStep (alpha n)).1, (rot1i (zWalk n)).2 + (unitStep (alpha n)).2) := by
  rw [zWalk_succ, zWalk_two_mul, alpha_two_mul]

/-! ### 3. Exact Squared Euclidean Norm & 2-Adic Identity for `zWalk` -/

/-- Squared Euclidean norm `x² + y² : ℕ` for a planar integer vector `(x, y) : ℤ × ℤ`. -/
def sqNorm (p : ℤ × ℤ) : ℕ :=
  p.1.natAbs ^ 2 + p.2.natAbs ^ 2

lemma sqNorm_cast (p : ℤ × ℤ) : ((sqNorm p : ℕ) : ℤ) = p.1 ^ 2 + p.2 ^ 2 := by
  simp only [sqNorm, Nat.cast_add, Nat.cast_pow, Int.natCast_natAbs, sq_abs]

lemma sqNorm_smul (c : ℤ) (x y : ℤ) :
    sqNorm (c * x, c * y) = c.natAbs ^ 2 * sqNorm (x, y) := by
  dsimp [sqNorm]
  rw [Int.natAbs_mul, Int.natAbs_mul, mul_pow, mul_pow, mul_add]

lemma sqNorm_rot1i (x y : ℤ) : sqNorm (rot1i (x, y)) = 2 * sqNorm (x, y) := by
  apply Int.ofNat.inj
  have h1 := sqNorm_cast (rot1i (x, y))
  have h2 := sqNorm_cast (x, y)
  change ((sqNorm (rot1i (x, y)) : ℕ) : ℤ) = ((2 * sqNorm (x, y) : ℕ) : ℤ)
  rw [h1, Nat.cast_mul, h2]
  dsimp [rot1i]
  ring

lemma sqNorm_pair_mod_two_eq_one {X Y : ℤ} (h : (X ^ 2 + Y ^ 2) % 2 = 1) :
    sqNorm (X, Y) % 2 = 1 := by
  have hc : ((sqNorm (X, Y) : ℕ) : ℤ) = X ^ 2 + Y ^ 2 := by
    simpa using sqNorm_cast (X, Y)
  omega

lemma sqNorm_rot1i_add_unitStep_mod2 (x y : ℤ) (a : Fin 4) :
    sqNorm ((rot1i (x, y)).1 + (unitStep a).1, (rot1i (x, y)).2 + (unitStep a).2) % 2 = 1 := by
  apply sqNorm_pair_mod_two_eq_one
  dsimp [rot1i]
  fin_cases a <;> dsimp [unitStep]
  · have h : (x - y + 1) ^ 2 + (x + y + 0) ^ 2 = 2 * (x ^ 2 + y ^ 2 + x - y) + 1 := by ring
    omega
  · have h : (x - y + 0) ^ 2 + (x + y + 1) ^ 2 = 2 * (x ^ 2 + y ^ 2 + x + y) + 1 := by ring
    omega
  · have h : (x - y + -1) ^ 2 + (x + y + 0) ^ 2 = 2 * (x ^ 2 + y ^ 2 - x + y) + 1 := by ring
    omega
  · have h : (x - y + 0) ^ 2 + (x + y + -1) ^ 2 = 2 * (x ^ 2 + y ^ 2 - x - y) + 1 := by ring
    omega

lemma sqNorm_rot1i_sub_unitStep_mod2 (x y : ℤ) (a : Fin 4) :
    sqNorm ((rot1i (x, y)).1 - (unitStep a).1, (rot1i (x, y)).2 - (unitStep a).2) % 2 = 1 := by
  apply sqNorm_pair_mod_two_eq_one
  dsimp [rot1i]
  fin_cases a <;> dsimp [unitStep]
  · have h : (x - y - 1) ^ 2 + (x + y - 0) ^ 2 = 2 * (x ^ 2 + y ^ 2 - x + y) + 1 := by ring
    omega
  · have h : (x - y - 0) ^ 2 + (x + y - 1) ^ 2 = 2 * (x ^ 2 + y ^ 2 - x - y) + 1 := by ring
    omega
  · have h : (x - y - -1) ^ 2 + (x + y - 0) ^ 2 = 2 * (x ^ 2 + y ^ 2 + x - y) + 1 := by ring
    omega
  · have h : (x - y - 0) ^ 2 + (x + y - -1) ^ 2 = 2 * (x ^ 2 + y ^ 2 + x + y) + 1 := by ring
    omega

/-- Key Gaussian 2-adic valuation theorem: whenever `m < n` and `α m = α n`,
`‖z_n - z_m‖² ≠ 0` and `v₂(‖z_n - z_m‖²) = v₂(n - m)`. -/
theorem v2_sqNorm_zWalk_diff :
    ∀ n m : ℕ, m < n → alpha m = alpha n →
      sqNorm ((zWalk n).1 - (zWalk m).1, (zWalk n).2 - (zWalk m).2) ≠ 0 ∧
      (sqNorm ((zWalk n).1 - (zWalk m).1, (zWalk n).2 - (zWalk m).2)).factorization 2 =
        (n - m).factorization 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro m hmn hα
    set q := n / 2
    set p := m / 2
    have hq_lt : q < n := Nat.div_lt_self (by omega) (by decide)
    by_cases hpar : m % 2 = n % 2
    · -- Same parity: both `2 * k` or both `2 * k + 1`
      have hpq : p < q := by omega
      have hα_pq : alpha p = alpha q := by
        apply Fin.ext
        have hsm : s2 m % 4 = s2 n % 4 := congrArg Fin.val hα
        have hm_eq : m = 2 * p + m % 2 := by omega
        have hn_eq : n = 2 * q + n % 2 := by omega
        rw [hm_eq, hn_eq] at hsm
        rcases Nat.mod_two_eq_zero_or_one n with hn0 | hn1
        · have hm0 : m % 2 = 0 := by rw [hpar, hn0]
          simp only [hm0, hn0, add_zero, s2_two_mul] at hsm
          exact hsm
        · have hm1 : m % 2 = 1 := by rw [hpar, hn1]
          simp only [hm1, hn1, s2_two_mul_add_one] at hsm
          dsimp [alpha]
          omega
      obtain ⟨hne_sub, hv_sub⟩ := ih q hq_lt p hpq hα_pq
      have hdiff_eq : ((zWalk n).1 - (zWalk m).1, (zWalk n).2 - (zWalk m).2) =
          rot1i ((zWalk q).1 - (zWalk p).1, (zWalk q).2 - (zWalk p).2) := by
        have hm_eq : m = 2 * p + m % 2 := by omega
        have hn_eq : n = 2 * q + n % 2 := by omega
        rcases Nat.mod_two_eq_zero_or_one n with hn0 | hn1
        · have hm0 : m % 2 = 0 := by rw [hpar, hn0]
          rw [hn_eq, hn0, hm_eq, hm0, add_zero, add_zero, zWalk_two_mul, zWalk_two_mul]
          ext <;> dsimp [rot1i] <;> omega
        · have hm1 : m % 2 = 1 := by rw [hpar, hn1]
          rw [hn_eq, hn1, hm_eq, hm1, zWalk_two_mul_add_one, zWalk_two_mul_add_one, hα_pq]
          ext <;> dsimp [rot1i] <;> omega
      rw [hdiff_eq, sqNorm_rot1i]
      have hnm_eq : n - m = 2 * (q - p) := by omega
      refine ⟨by omega, ?_⟩
      rw [factorization_two_two_mul hne_sub, hnm_eq, factorization_two_two_mul (by omega), hv_sub]
    · -- Opposite parity: `n - m` is odd and `sqNorm (zWalk n - zWalk m)` is odd
      have hnm_odd : (n - m) % 2 = 1 := by omega
      have hsq_odd : sqNorm ((zWalk n).1 - (zWalk m).1, (zWalk n).2 - (zWalk m).2) % 2 = 1 := by
        have hm_eq : m = 2 * p + m % 2 := by omega
        have hn_eq : n = 2 * q + n % 2 := by omega
        rcases Nat.mod_two_eq_zero_or_one n with hn0 | hn1
        · have hm1 : m % 2 = 1 := by omega
          rw [hn_eq, hn0, add_zero, hm_eq, hm1, zWalk_two_mul, zWalk_two_mul_add_one]
          have hvec : ((rot1i (zWalk q)).1 - ((rot1i (zWalk p)).1 + (unitStep (alpha p)).1),
              (rot1i (zWalk q)).2 - ((rot1i (zWalk p)).2 + (unitStep (alpha p)).2)) =
              ((rot1i ((zWalk q).1 - (zWalk p).1, (zWalk q).2 - (zWalk p).2)).1 - (unitStep (alpha p)).1,
               (rot1i ((zWalk q).1 - (zWalk p).1, (zWalk q).2 - (zWalk p).2)).2 - (unitStep (alpha p)).2) := by
            ext <;> dsimp [rot1i] <;> omega
          rw [hvec]
          exact sqNorm_rot1i_sub_unitStep_mod2 _ _ (alpha p)
        · have hm0 : m % 2 = 0 := by omega
          rw [hn_eq, hn1, hm_eq, hm0, add_zero, zWalk_two_mul_add_one, zWalk_two_mul]
          have hvec : ((rot1i (zWalk q)).1 + (unitStep (alpha q)).1 - (rot1i (zWalk p)).1,
              (rot1i (zWalk q)).2 + (unitStep (alpha q)).2 - (rot1i (zWalk p)).2) =
              ((rot1i ((zWalk q).1 - (zWalk p).1, (zWalk q).2 - (zWalk p).2)).1 + (unitStep (alpha q)).1,
               (rot1i ((zWalk q).1 - (zWalk p).1, (zWalk q).2 - (zWalk p).2)).2 + (unitStep (alpha q)).2) := by
            ext <;> dsimp [rot1i] <;> omega
          rw [hvec]
          exact sqNorm_rot1i_add_unitStep_mod2 _ _ (alpha q)
      refine ⟨by omega, ?_⟩
      rw [factorization_two_eq_zero_of_odd hsq_odd, factorization_two_eq_zero_of_odd hnm_odd]

/-! ### 4. Small-Step `ℤ³` Walk `P n = (w_n, h_n)` and Universal 2-Adic Valuation Law -/

/-- Corner tag vectors `0, i, -1 + i, -1` on `ℤ × ℤ`. -/
def corner : Fin 4 → ℤ × ℤ
  | 0 => (0, 0)
  | 1 => (0, 1)
  | 2 => (-1, 1)
  | 3 => (-1, 0)

/-- Planar projection `w_n = 2 z_n + corner(α n) ∈ ℤ × ℤ`. -/
def wWalk (n : ℕ) : ℤ × ℤ :=
  (2 * (zWalk n).1 + (corner (alpha n)).1, 2 * (zWalk n).2 + (corner (alpha n)).2)

/-- Strictly increasing height coordinate `h_n = 4 n + α(n) : ℕ`. -/
def hWalk (n : ℕ) : ℕ :=
  4 * n + (alpha n).val

/-- 3D integer walk `P : ℕ → ℤ × ℤ × ℤ`. -/
def P (n : ℕ) : ℤ × ℤ × ℤ :=
  ((wWalk n).1, (wWalk n).2, (hWalk n : ℤ))

/-- Real-space embedding `PReal : ℕ → Fin 3 → ℝ` for Mathlib `Collinear ℝ`. -/
def PReal (n : ℕ) : Fin 3 → ℝ :=
  ![((wWalk n).1 : ℝ), ((wWalk n).2 : ℝ), ((hWalk n : ℤ) : ℝ)]

lemma hWalk_strictMono : StrictMono hWalk := by
  intro m n hmn
  dsimp [hWalk]
  have hm4 : (alpha m).val < 4 := (alpha m).isLt
  have hn4 : (alpha n).val < 4 := (alpha n).isLt
  omega

lemma P_injective : Function.Injective P := by
  intro m n h
  have hz : (hWalk m : ℤ) = (hWalk n : ℤ) := congrArg (fun q => q.2.2) h
  exact hWalk_strictMono.injective (Int.ofNat.inj hz)

lemma PReal_injective : Function.Injective PReal := by
  intro m n h
  have hz := congrArg (fun f : Fin 3 → ℝ => f 2) h
  dsimp [PReal] at hz
  have hzInt : (hWalk m : ℤ) = (hWalk n : ℤ) := Int.cast_injective hz
  exact hWalk_strictMono.injective (Int.ofNat.inj hzInt)

/-- Step vector formula: `P (n + 1) - P n` depends only on the finite pair `(alpha n, alpha (n + 1)) : Fin 4 × Fin 4`! -/
def stepTable (p : Fin 4 × Fin 4) : ℤ × ℤ × ℤ :=
  (2 * (unitStep p.1).1 + (corner p.2).1 - (corner p.1).1,
   2 * (unitStep p.1).2 + (corner p.2).2 - (corner p.1).2,
   4 + (p.2.val : ℤ) - (p.1.val : ℤ))

lemma stepVec_eq_stepTable (n : ℕ) :
    ((P (n + 1)).1 - (P n).1, (P (n + 1)).2.1 - (P n).2.1, (P (n + 1)).2.2 - (P n).2.2) =
      stepTable (alpha n, alpha (n + 1)) := by
  dsimp [P, wWalk, hWalk, zWalk, stepTable]
  ext <;> push_cast <;> omega

lemma stepTable_bounded (p : Fin 4 × Fin 4) :
    -2 ≤ (stepTable p).1 ∧ (stepTable p).1 ≤ 2 ∧
    -2 ≤ (stepTable p).2.1 ∧ (stepTable p).2.1 ≤ 2 ∧
    1 ≤ (stepTable p).2.2 ∧ (stepTable p).2.2 ≤ 7 := by
  rcases p with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;> decide

lemma step_in_small_box (n : ℕ) :
    let d := ((P (n + 1)).1 - (P n).1, (P (n + 1)).2.1 - (P n).2.1, (P (n + 1)).2.2 - (P n).2.2);
    -2 ≤ d.1 ∧ d.1 ≤ 2 ∧ -2 ≤ d.2.1 ∧ d.2.1 ≤ 2 ∧ 1 ≤ d.2.2 ∧ d.2.2 ≤ 7 := by
  intro d
  have hd : d = stepTable (alpha n, alpha (n + 1)) := stepVec_eq_stepTable n
  rw [hd]
  exact stepTable_bounded _

lemma int_steps_finite :
    (Set.range (fun n : ℕ =>
      ((P (n + 1)).1 - (P n).1, (P (n + 1)).2.1 - (P n).2.1, (P (n + 1)).2.2 - (P n).2.2))).Finite := by
  refine (Set.finite_range stepTable).subset ?_
  rintro _ ⟨n, rfl⟩
  dsimp only
  rw [stepVec_eq_stepTable n]
  exact ⟨(alpha n, alpha (n + 1)), rfl⟩

lemma real_steps_finite :
    (Set.range (fun n : ℕ => PReal (n + 1) - PReal n)).Finite := by
  let toReal : (ℤ × ℤ × ℤ) → (Fin 3 → ℝ) := fun d => ![(d.1 : ℝ), (d.2.1 : ℝ), (d.2.2 : ℝ)]
  refine ((Set.finite_range stepTable).image toReal).subset ?_
  rintro _ ⟨n, rfl⟩
  refine ⟨stepTable (alpha n, alpha (n + 1)), ⟨(alpha n, alpha (n + 1)), rfl⟩, ?_⟩
  have hst := stepVec_eq_stepTable n
  have h1 : (stepTable (alpha n, alpha (n + 1))).1 = (P (n + 1)).1 - (P n).1 := congrArg Prod.fst hst.symm
  have h2 : (stepTable (alpha n, alpha (n + 1))).2.1 = (P (n + 1)).2.1 - (P n).2.1 :=
    congrArg (fun q => q.2.1) hst.symm
  have h3 : (stepTable (alpha n, alpha (n + 1))).2.2 = (P (n + 1)).2.2 - (P n).2.2 :=
    congrArg (fun q => q.2.2) hst.symm
  ext i
  fin_cases i
  · simp [toReal, h1, P, PReal]
  · simp [toReal, h2, P, PReal]
  · simp [toReal, h3, P, PReal]

/-- Universal 2-adic valuation law for the embedded planar walk `wWalk`:
`v₂(‖w_n - w_m‖²) = v₂(h_n - h_m)` for ALL `m < n`. -/
theorem v2_sqNorm_wWalk_diff {m n : ℕ} (hmn : m < n) :
    sqNorm ((wWalk n).1 - (wWalk m).1, (wWalk n).2 - (wWalk m).2) ≠ 0 ∧
    (sqNorm ((wWalk n).1 - (wWalk m).1, (wWalk n).2 - (wWalk m).2)).factorization 2 =
      (hWalk n - hWalk m).factorization 2 := by
  by_cases hα : alpha m = alpha n
  · -- Case `α m = α n`: corners cancel, `w_n - w_m = 2 (z_n - z_m)`, `h_n - h_m = 4 (n - m)`
    obtain ⟨hne_z, hv_z⟩ := v2_sqNorm_zWalk_diff n m hmn hα
    have hw_diff : ((wWalk n).1 - (wWalk m).1, (wWalk n).2 - (wWalk m).2) =
        (2 * ((zWalk n).1 - (zWalk m).1), 2 * ((zWalk n).2 - (zWalk m).2)) := by
      dsimp [wWalk]
      rw [hα]
      ext <;> omega
    have hsq : sqNorm ((wWalk n).1 - (wWalk m).1, (wWalk n).2 - (wWalk m).2) =
        4 * sqNorm ((zWalk n).1 - (zWalk m).1, (zWalk n).2 - (zWalk m).2) := by
      rw [hw_diff, sqNorm_smul]
      norm_num
    have hdh : hWalk n - hWalk m = 4 * (n - m) := by
      dsimp [hWalk]
      rw [hα]
      omega
    rw [hsq, hdh]
    refine ⟨by omega, ?_⟩
    rw [factorization_two_four_mul hne_z, factorization_two_four_mul (by omega), hv_z]
  · -- Case `α m ≠ α n`: explicit check over the 12 off-diagonal `(Fin 4 × Fin 4)` pairs
    have hw_mod : ∀ dx dy : ℤ, ∀ a b : Fin 4, a ≠ b →
        (sqNorm (2 * dx + (corner b).1 - (corner a).1, 2 * dy + (corner b).2 - (corner a).2) % 2 = 1 ∧
          (b.val : ℤ) % 2 ≠ (a.val : ℤ) % 2) ∨
        (sqNorm (2 * dx + (corner b).1 - (corner a).1, 2 * dy + (corner b).2 - (corner a).2) % 4 = 2 ∧
          ((b.val : ℤ) - (a.val : ℤ)) % 4 = 2) := by
      intro dx dy a b hab
      set cx := (corner b).1 - (corner a).1
      set cy := (corner b).2 - (corner a).2
      set nsq := sqNorm (2 * dx + (corner b).1 - (corner a).1, 2 * dy + (corner b).2 - (corner a).2)
      have hcast := sqNorm_cast (2 * dx + (corner b).1 - (corner a).1, 2 * dy + (corner b).2 - (corner a).2)
      have hexp : (nsq : ℤ) = 4 * (dx ^ 2 + dx * cx + dy ^ 2 + dy * cy) + (cx ^ 2 + cy ^ 2) := by
        dsimp [nsq] at hcast ⊢
        rw [hcast]
        dsimp [cx, cy]
        ring
      have hcases : (((cx ^ 2 + cy ^ 2) % 4 = 1 ∧ (b.val : ℤ) % 2 ≠ (a.val : ℤ) % 2) ∨
          ((cx ^ 2 + cy ^ 2) % 4 = 2 ∧ ((b.val : ℤ) - (a.val : ℤ)) % 4 = 2)) := by
        dsimp [cx, cy]
        fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | (dsimp [corner]; decide)
      rcases hcases with ⟨hm, hp⟩ | ⟨hm, hp⟩
      · left; exact ⟨by omega, hp⟩
      · right; exact ⟨by omega, hp⟩
    have hdiff_w : ((wWalk n).1 - (wWalk m).1, (wWalk n).2 - (wWalk m).2) =
        (2 * ((zWalk n).1 - (zWalk m).1) + (corner (alpha n)).1 - (corner (alpha m)).1,
         2 * ((zWalk n).2 - (zWalk m).2) + (corner (alpha n)).2 - (corner (alpha m)).2) := by
      dsimp [wWalk]
      ext <;> omega
    rw [hdiff_w]
    rcases hw_mod ((zWalk n).1 - (zWalk m).1) ((zWalk n).2 - (zWalk m).2) (alpha m) (alpha n) hα with
      ⟨hsq1, hpar⟩ | ⟨hsq2, hmod2⟩
    · have hdh_odd : (hWalk n - hWalk m) % 2 = 1 := by
        dsimp [hWalk]
        have hm_lt : (alpha m).val < 4 := (alpha m).isLt
        have hn_lt : (alpha n).val < 4 := (alpha n).isLt
        omega
      refine ⟨by omega, ?_⟩
      rw [factorization_two_eq_zero_of_odd hsq1, factorization_two_eq_zero_of_odd hdh_odd]
    · have hdh_mod4 : (hWalk n - hWalk m) % 4 = 2 := by
        dsimp [hWalk]
        have hm_lt : (alpha m).val < 4 := (alpha m).isLt
        have hn_lt : (alpha n).val < 4 := (alpha n).isLt
        omega
      refine ⟨by omega, ?_⟩
      rw [factorization_two_eq_one_of_mod_four hsq2, factorization_two_eq_one_of_mod_four hdh_mod4]

/-! ### 5. Exact Non-Collinearity Engine in `ℤ³` and `ℝ³` -/

lemma sqNorm_proportional_eq {a b : ℕ} {v1 v2 w1 w2 : ℤ}
    (hx : (b : ℤ) * v1 = (a : ℤ) * w1) (hy : (b : ℤ) * v2 = (a : ℤ) * w2) :
    b ^ 2 * sqNorm (v1, v2) = a ^ 2 * sqNorm (w1, w2) := by
  have h1 : sqNorm ((b : ℤ) * v1, (b : ℤ) * v2) = sqNorm ((a : ℤ) * w1, (a : ℤ) * w2) := by
    rw [hx, hy]
  rw [sqNorm_smul, sqNorm_smul] at h1
  simpa [Int.natAbs_natCast] using h1

lemma no_proportional_diffs {m n k : ℕ} (hmn : m < n) (hnk : n < k)
    (h1x : ((hWalk k - hWalk m : ℕ) : ℤ) * ((wWalk n).1 - (wWalk m).1) =
           ((hWalk n - hWalk m : ℕ) : ℤ) * ((wWalk k).1 - (wWalk m).1))
    (h1y : ((hWalk k - hWalk m : ℕ) : ℤ) * ((wWalk n).2 - (wWalk m).2) =
           ((hWalk n - hWalk m : ℕ) : ℤ) * ((wWalk k).2 - (wWalk m).2))
    (h2x : ((hWalk k - hWalk n : ℕ) : ℤ) * ((wWalk n).1 - (wWalk m).1) =
           ((hWalk n - hWalk m : ℕ) : ℤ) * ((wWalk k).1 - (wWalk n).1))
    (h2y : ((hWalk k - hWalk n : ℕ) : ℤ) * ((wWalk n).2 - (wWalk m).2) =
           ((hWalk n - hWalk m : ℕ) : ℤ) * ((wWalk k).2 - (wWalk n).2)) : False := by
  have hmk : m < k := lt_trans hmn hnk
  have hm_n : hWalk m < hWalk n := hWalk_strictMono hmn
  have hn_k : hWalk n < hWalk k := hWalk_strictMono hnk
  have hm_k : hWalk m < hWalk k := hWalk_strictMono hmk
  set a := hWalk n - hWalk m
  set b := hWalk k - hWalk m
  set c := hWalk k - hWalk n
  have ha0 : a ≠ 0 := by omega
  have hb0 : b ≠ 0 := by omega
  have hc0 : c ≠ 0 := by omega
  have hsum : b = a + c := by omega
  obtain ⟨hne_mn, hv_mn⟩ := v2_sqNorm_wWalk_diff hmn
  obtain ⟨hne_mk, hv_mk⟩ := v2_sqNorm_wWalk_diff hmk
  obtain ⟨hne_nk, hv_nk⟩ := v2_sqNorm_wWalk_diff hnk
  have heq1 := sqNorm_proportional_eq h1x h1y
  have hfact1 : (b ^ 2 * sqNorm ((wWalk n).1 - (wWalk m).1, (wWalk n).2 - (wWalk m).2)).factorization 2 =
      (a ^ 2 * sqNorm ((wWalk k).1 - (wWalk m).1, (wWalk k).2 - (wWalk m).2)).factorization 2 :=
    congrArg (fun t : ℕ => t.factorization 2) heq1
  rw [Nat.factorization_mul (pow_ne_zero 2 hb0) hne_mn, Finsupp.add_apply, factorization_two_sq hb0, hv_mn,
      Nat.factorization_mul (pow_ne_zero 2 ha0) hne_mk, Finsupp.add_apply, factorization_two_sq ha0, hv_mk] at hfact1
  have hv_ba : b.factorization 2 = a.factorization 2 := by
    dsimp [a, b] at hfact1 ⊢
    omega
  have heq2 := sqNorm_proportional_eq h2x h2y
  have hfact2 : (c ^ 2 * sqNorm ((wWalk n).1 - (wWalk m).1, (wWalk n).2 - (wWalk m).2)).factorization 2 =
      (a ^ 2 * sqNorm ((wWalk k).1 - (wWalk n).1, (wWalk k).2 - (wWalk n).2)).factorization 2 :=
    congrArg (fun t : ℕ => t.factorization 2) heq2
  rw [Nat.factorization_mul (pow_ne_zero 2 hc0) hne_mn, Finsupp.add_apply, factorization_two_sq hc0, hv_mn,
      Nat.factorization_mul (pow_ne_zero 2 ha0) hne_nk, Finsupp.add_apply, factorization_two_sq ha0, hv_nk] at hfact2
  have hv_ca : c.factorization 2 = a.factorization 2 := by
    dsimp [a, c] at hfact2 ⊢
    omega
  have hlt := factorization_two_add_gt ha0 hc0 hv_ca.symm
  rw [← hsum] at hlt
  omega

/-- No three points `P m, P n, P k` (`m < n < k`) admit a nontrivial linear relation between
`P n - P m` and `P k - P m` in `ℤ³` (equivalently, non-zero cross product in `ℤ³`). -/
theorem no_three_collinear_int {m n k : ℕ} (hmn : m < n) (hnk : n < k) :
    ¬ ∃ (r s : ℤ), (r ≠ 0 ∨ s ≠ 0) ∧
      r * ((P n).1 - (P m).1) + s * ((P k).1 - (P m).1) = 0 ∧
      r * ((P n).2.1 - (P m).2.1) + s * ((P k).2.1 - (P m).2.1) = 0 ∧
      r * ((P n).2.2 - (P m).2.2) + s * ((P k).2.2 - (P m).2.2) = 0 := by
  rintro ⟨r, s, hrs, hx, hy, hz⟩
  have hm_n : hWalk m < hWalk n := hWalk_strictMono hmn
  have hn_k : hWalk n < hWalk k := hWalk_strictMono hnk
  have hm_k : hWalk m < hWalk k := hWalk_strictMono (lt_trans hmn hnk)
  have hP1 : ∀ i, (P i).1 = (wWalk i).1 := fun _ => rfl
  have hP2 : ∀ i, (P i).2.1 = (wWalk i).2 := fun _ => rfl
  have hP3 : ∀ i, (P i).2.2 = (hWalk i : ℤ) := fun _ => rfl
  rw [hP3, hP3, hP3] at hz
  have hrs_z : (r + s) ≠ 0 ∨ r ≠ 0 := by
    by_contra h
    omega
  -- Wait: use `r ≠ 0` or `s ≠ 0` cleanly; since `hm_n` and `hm_k` are positive, `r ≠ 0 ↔ s ≠ 0`!
  have hs_ne : s ≠ 0 := by
    intro hs0
    subst hs0
    simp only [zero_mul, add_zero] at hz
    rcases mul_eq_zero.mp hz with rfl | h0
    · exact hrs.elim (fun h => h rfl) (fun h => h rfl)
    · omega
  have hx1 : (s * ((wWalk n).1 - (wWalk m).1) * ((hWalk k - hWalk m : ℕ) : ℤ)) =
      s * ((hWalk n - hWalk m : ℕ) : ℤ) * ((wWalk k).1 - (wWalk m).1) := by
    have hzk : ((hWalk k - hWalk m : ℕ) : ℤ) = (hWalk k : ℤ) - (hWalk m : ℤ) := by omega
    have hzn : ((hWalk n - hWalk m : ℕ) : ℤ) = (hWalk n : ℤ) - (hWalk m : ℤ) := by omega
    rw [hzk, hzn]
    rw [hP1, hP1, hP1] at hx
    calc
      s * ((wWalk n).1 - (wWalk m).1) * ((hWalk k : ℤ) - (hWalk m : ℤ))
          = (s * ((hWalk k : ℤ) - (hWalk m : ℤ))) * ((wWalk n).1 - (wWalk m).1) := by ring
      _ = (- (r * ((hWalk n : ℤ) - (hWalk m : ℤ)))) * ((wWalk n).1 - (wWalk m).1) := by
            have hzz : s * ((hWalk k : ℤ) - (hWalk m : ℤ)) = -(r * ((hWalk n : ℤ) - (hWalk m : ℤ))) := by linarith
            rw [hzz]
      _ = ((hWalk n : ℤ) - (hWalk m : ℤ)) * (-(r * ((wWalk n).1 - (wWalk m).1))) := by ring
      _ = ((hWalk n : ℤ) - (hWalk m : ℤ)) * (s * ((wWalk k).1 - (wWalk m).1)) := by
            have hxx : -(r * ((wWalk n).1 - (wWalk m).1)) = s * ((wWalk k).1 - (wWalk m).1) := by linarith
            rw [hxx]
      _ = s * ((hWalk n : ℤ) - (hWalk m : ℤ)) * ((wWalk k).1 - (wWalk m).1) := by ring
  have hy1 : (s * ((wWalk n).2 - (wWalk m).2) * ((hWalk k - hWalk m : ℕ) : ℤ)) =
      s * ((hWalk n - hWalk m : ℕ) : ℤ) * ((wWalk k).2 - (wWalk m).2) := by
    have hzk : ((hWalk k - hWalk m : ℕ) : ℤ) = (hWalk k : ℤ) - (hWalk m : ℤ) := by omega
    have hzn : ((hWalk n - hWalk m : ℕ) : ℤ) = (hWalk n : ℤ) - (hWalk m : ℤ) := by omega
    rw [hzk, hzn]
    rw [hP2, hP2, hP2] at hy
    calc
      s * ((wWalk n).2 - (wWalk m).2) * ((hWalk k : ℤ) - (hWalk m : ℤ))
          = (s * ((hWalk k : ℤ) - (hWalk m : ℤ))) * ((wWalk n).2 - (wWalk m).2) := by ring
      _ = (- (r * ((hWalk n : ℤ) - (hWalk m : ℤ)))) * ((wWalk n).2 - (wWalk m).2) := by
            have hzz : s * ((hWalk k : ℤ) - (hWalk m : ℤ)) = -(r * ((hWalk n : ℤ) - (hWalk m : ℤ))) := by linarith
            rw [hzz]
      _ = ((hWalk n : ℤ) - (hWalk m : ℤ)) * (-(r * ((wWalk n).2 - (wWalk m).2))) := by ring
      _ = ((hWalk n : ℤ) - (hWalk m : ℤ)) * (s * ((wWalk k).2 - (wWalk m).2)) := by
            have hyy : -(r * ((wWalk n).2 - (wWalk m).2)) = s * ((wWalk k).2 - (wWalk m).2) := by linarith
            rw [hyy]
      _ = s * ((hWalk n : ℤ) - (hWalk m : ℤ)) * ((wWalk k).2 - (wWalk m).2) := by ring
  have h1x' : ((hWalk k - hWalk m : ℕ) : ℤ) * ((wWalk n).1 - (wWalk m).1) =
      ((hWalk n - hWalk m : ℕ) : ℤ) * ((wWalk k).1 - (wWalk m).1) := by
    apply mul_left_cancel₀ hs_ne
    linarith [hx1]
  have h1y' : ((hWalk k - hWalk m : ℕ) : ℤ) * ((wWalk n).2 - (wWalk m).2) =
      ((hWalk n - hWalk m : ℕ) : ℤ) * ((wWalk k).2 - (wWalk m).2) := by
    apply mul_left_cancel₀ hs_ne
    linarith [hy1]
  have h2x' : ((hWalk k - hWalk n : ℕ) : ℤ) * ((wWalk n).1 - (wWalk m).1) =
      ((hWalk n - hWalk m : ℕ) : ℤ) * ((wWalk k).1 - (wWalk n).1) := by
    have hzk : ((hWalk k - hWalk n : ℕ) : ℤ) = ((hWalk k - hWalk m : ℕ) : ℤ) - ((hWalk n - hWalk m : ℕ) : ℤ) := by omega
    rw [hzk]
    linarith [h1x']
  have h2y' : ((hWalk k - hWalk n : ℕ) : ℤ) * ((wWalk n).2 - (wWalk m).2) =
      ((hWalk n - hWalk m : ℕ) : ℤ) * ((wWalk k).2 - (wWalk n).2) := by
    have hzk : ((hWalk k - hWalk n : ℕ) : ℤ) = ((hWalk k - hWalk m : ℕ) : ℤ) - ((hWalk n - hWalk m : ℕ) : ℤ) := by omega
    rw [hzk]
    linarith [h1y']
  exact no_proportional_diffs hmn hnk h1x' h1y' h2x' h2y'

/-- No three distinct points of `PReal` are collinear in Euclidean `ℝ³` (`Fin 3 → ℝ`). -/
theorem no_three_collinear_real {m n k : ℕ} (hmn : m < n) (hnk : n < k) :
    ¬ Collinear ℝ ({PReal m, PReal n, PReal k} : Set (Fin 3 → ℝ)) := by
  intro hcol
  have hm_mem : PReal m ∈ ({PReal m, PReal n, PReal k} : Set (Fin 3 → ℝ)) := by simp
  have hn_mem : PReal n ∈ ({PReal m, PReal n, PReal k} : Set (Fin 3 → ℝ)) := by simp
  have hk_mem : PReal k ∈ ({PReal m, PReal n, PReal k} : Set (Fin 3 → ℝ)) := by simp
  obtain ⟨v, hv⟩ := (collinear_iff_of_mem hm_mem).mp hcol
  obtain ⟨rn, hrn⟩ := hv (PReal n) hn_mem
  obtain ⟨rk, hrk⟩ := hv (PReal k) hk_mem
  have hm_n : hWalk m < hWalk n := hWalk_strictMono hmn
  have hn_k : hWalk n < hWalk k := hWalk_strictMono hnk
  have hm_k : hWalk m < hWalk k := hWalk_strictMono (lt_trans hmn hnk)
  have hcoord : ∀ j : Fin 3,
      (PReal k 2 - PReal m 2) * (PReal n j - PReal m j) =
        (PReal n 2 - PReal m 2) * (PReal k j - PReal m j) := by
    intro j
    have hn2 := congrFun hrn 2
    have hk2 := congrFun hrk 2
    have hnj := congrFun hrn j
    have hkj := congrFun hrk j
    simp only [vadd_eq_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hn2 hk2 hnj hkj
    rw [hn2, hk2, hnj, hkj]
    ring
  have h0 := hcoord 0
  have h1 := hcoord 1
  have hdiff_real : ∀ {u v : ℕ}, u ≤ v →
      ((hWalk v - hWalk u : ℕ) : ℝ) = ((hWalk v : ℤ) : ℝ) - ((hWalk u : ℤ) : ℝ) := by
    intro u v huv
    rw [Nat.cast_sub (hWalk_strictMono.monotone huv)]
    push_cast
    ring
  have hc0 : ((hWalk k - hWalk m : ℕ) : ℤ) * ((wWalk n).1 - (wWalk m).1) =
      ((hWalk n - hWalk m : ℕ) : ℤ) * ((wWalk k).1 - (wWalk m).1) := by
    apply Int.cast_injective (α := ℝ)
    push_cast
    rw [hdiff_real (lt_trans hmn hnk).le, hdiff_real hmn.le]
    simpa [PReal] using h0
  have hc1 : ((hWalk k - hWalk m : ℕ) : ℤ) * ((wWalk n).2 - (wWalk m).2) =
      ((hWalk n - hWalk m : ℕ) : ℤ) * ((wWalk k).2 - (wWalk m).2) := by
    apply Int.cast_injective (α := ℝ)
    push_cast
    rw [hdiff_real (lt_trans hmn hnk).le, hdiff_real hmn.le]
    simpa [PReal] using h1
  have h2x : ((hWalk k - hWalk n : ℕ) : ℤ) * ((wWalk n).1 - (wWalk m).1) =
      ((hWalk n - hWalk m : ℕ) : ℤ) * ((wWalk k).1 - (wWalk n).1) := by
    have hzk : ((hWalk k - hWalk n : ℕ) : ℤ) = ((hWalk k - hWalk m : ℕ) : ℤ) - ((hWalk n - hWalk m : ℕ) : ℤ) := by omega
    rw [hzk]
    linarith [hc0]
  have h2y : ((hWalk k - hWalk n : ℕ) : ℤ) * ((wWalk n).2 - (wWalk m).2) =
      ((hWalk n - hWalk m : ℕ) : ℤ) * ((wWalk k).2 - (wWalk n).2) := by
    have hzk : ((hWalk k - hWalk n : ℕ) : ℤ) = ((hWalk k - hWalk m : ℕ) : ℤ) - ((hWalk n - hWalk m : ℕ) : ℤ) := by omega
    rw [hzk]
    linarith [hc1]
  exact no_proportional_diffs hmn hnk hc0 hc1 h2x h2y

theorem no_three_collinear_real_distinct {m n k : ℕ} (hmn : m ≠ n) (hmk : m ≠ k) (hnk : n ≠ k) :
    ¬ Collinear ℝ ({PReal m, PReal n, PReal k} : Set (Fin 3 → ℝ)) := by
  rcases lt_trichotomy m n with h1 | rfl | h1
  · rcases lt_trichotomy n k with h2 | rfl | h2
    · exact no_three_collinear_real h1 h2
    · exact absurd rfl hnk
    · rcases lt_trichotomy m k with h3 | rfl | h3
      · have hset : ({PReal m, PReal n, PReal k} : Set (Fin 3 → ℝ)) = {PReal m, PReal k, PReal n} := by
          ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
        rw [hset]
        exact no_three_collinear_real h3 h2
      · exact absurd rfl hmk
      · have hset : ({PReal m, PReal n, PReal k} : Set (Fin 3 → ℝ)) = {PReal k, PReal m, PReal n} := by
          ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
        rw [hset]
        exact no_three_collinear_real h3 h1
  · exact absurd rfl hmn
  · rcases lt_trichotomy m k with h2 | rfl | h2
    · have hset : ({PReal m, PReal n, PReal k} : Set (Fin 3 → ℝ)) = {PReal n, PReal m, PReal k} := by
        ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
      rw [hset]
      exact no_three_collinear_real h1 h2
    · exact absurd rfl hmk
    · rcases lt_trichotomy n k with h3 | rfl | h3
      · have hset : ({PReal m, PReal n, PReal k} : Set (Fin 3 → ℝ)) = {PReal n, PReal k, PReal m} := by
          ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
        rw [hset]
        exact no_three_collinear_real h3 h2
      · exact absurd rfl hnk
      · have hset : ({PReal m, PReal n, PReal k} : Set (Fin 3 → ℝ)) = {PReal k, PReal n, PReal m} := by
          ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
        rw [hset]
        exact no_three_collinear_real h3 h1

theorem jsp_000183_small_step_z3_walk_no_collinear_triple :
    ∃ (walk : ℕ → ℤ × ℤ × ℤ),
      Function.Injective walk ∧
      (Set.range (fun n : ℕ =>
        ((walk (n + 1)).1 - (walk n).1,
         (walk (n + 1)).2.1 - (walk n).2.1,
         (walk (n + 1)).2.2 - (walk n).2.2))).Finite ∧
      (∀ n : ℕ,
        let d := ((walk (n + 1)).1 - (walk n).1,
                  (walk (n + 1)).2.1 - (walk n).2.1,
                  (walk (n + 1)).2.2 - (walk n).2.2);
        -2 ≤ d.1 ∧ d.1 ≤ 2 ∧ -2 ≤ d.2.1 ∧ d.2.1 ≤ 2 ∧ 1 ≤ d.2.2 ∧ d.2.2 ≤ 7) ∧
      (∀ m n k : ℕ, m < n → n < k →
        ¬ Collinear ℝ ({PReal m, PReal n, PReal k} : Set (Fin 3 → ℝ))) ∧
      (∀ m n k : ℕ, m < n → n < k →
        ¬ ∃ (r s : ℤ), (r ≠ 0 ∨ s ≠ 0) ∧
          r * ((walk n).1 - (walk m).1) + s * ((walk k).1 - (walk m).1) = 0 ∧
          r * ((walk n).2.1 - (walk m).2.1) + s * ((walk k).2.1 - (walk m).2.1) = 0 ∧
          r * ((walk n).2.2 - (walk m).2.2) + s * ((walk k).2.2 - (walk m).2.2) = 0) :=
  ⟨P, P_injective, int_steps_finite, step_in_small_box,
    fun _ _ _ h1 h2 => no_three_collinear_real h1 h2,
    fun _ _ _ h1 h2 => no_three_collinear_int h1 h2⟩

/-- Explicit finite-step-set Euclidean `ℝ³` disproof of the Gerver–Ramsey / Erdős #193 question:
there exists an injective infinite walk `f : ℕ → Fin 3 → ℝ` taking steps in a finite set of
vectors `S : Set (Fin 3 → ℝ)` (of bounded `ℤ³` coordinates) that avoids every collinear triple. -/
theorem jsp_000183_no_collinear_triple_euclidean :
    ∃ (f : ℕ → Fin 3 → ℝ),
      Function.Injective f ∧
      (Set.range (fun n : ℕ => f (n + 1) - f n)).Finite ∧
      ∀ m n k : ℕ, m ≠ n → m ≠ k → n ≠ k →
        ¬ Collinear ℝ ({f m, f n, f k} : Set (Fin 3 → ℝ)) :=
  ⟨PReal, PReal_injective, real_steps_finite, fun _ _ _ h1 h2 h3 => no_three_collinear_real_distinct h1 h2 h3⟩

end JSP_000183

#check JSP_000183.v2_sqNorm_zWalk_diff
#check JSP_000183.v2_sqNorm_wWalk_diff
#check JSP_000183.jsp_000183_small_step_z3_walk_no_collinear_triple
#check JSP_000183.jsp_000183_no_collinear_triple_euclidean

#print axioms JSP_000183.v2_sqNorm_zWalk_diff
#print axioms JSP_000183.v2_sqNorm_wWalk_diff
#print axioms JSP_000183.jsp_000183_small_step_z3_walk_no_collinear_triple
#print axioms JSP_000183.jsp_000183_no_collinear_triple_euclidean
