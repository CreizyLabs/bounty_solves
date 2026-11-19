import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Group.Even
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# JSP-000301: Disproof of the Consecutive Powerful Squares Conjecture

- **Catalog ID:** JSP-000301 (`catalog-0301-0400.md`)
- **Historical Source:** Solomon W. Golomb (1970), "Powerful numbers",
  *American Mathematical Monthly* 77(8), 848–852 (cf. Erdős Problem #365).
- **Question:** If two consecutive positive integers are powerful, must at least
  one be a perfect square?
- **Answer:** No. `12167 = 23^3` and `12168 = 2^3 * 3^2 * 13^2` are consecutive
  positive powerful integers, and neither is a perfect square since
  `110^2 = 12100 < 12167 < 12168 < 12321 = 111^2`.

## Formal Guarantees
- Uses Mathlib's canonical `Nat.Prime` and `IsSquare`.
- Proves the exact bidirectional equivalence between the canonical prime-exponent
  definition (`∀ p, p.Prime → p ∣ n → p ^ 2 ∣ n`) and Golomb's `x ^ 2 * y ^ 3`
  characterization across all `n : ℕ`.
- Unconditional, zero `sorry`, zero `admit`, zero custom axioms, zero approximations.
-/

namespace JSP_000301

/-- Canonical prime-exponent definition of a powerful (squarefull) natural number:
every prime divisor divides `n` at least to the second power. -/
def IsPowerful (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/-- Golomb's multiplicative characterization of powerful numbers: `n = x^2 * y^3`. -/
def IsSqMulCube (n : ℕ) : Prop :=
  ∃ x y : ℕ, n = x ^ 2 * y ^ 3

/-- Every number of the form `x^2 * y^3` is powerful in the canonical prime-exponent sense. -/
theorem isPowerful_of_sq_mul_cube (x y : ℕ) : IsPowerful (x ^ 2 * y ^ 3) := by
  intro p hp hdvd
  rcases hp.dvd_mul.mp hdvd with hx | hy
  · have hpx : p ∣ x := hp.dvd_of_dvd_pow hx
    exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd hpx 2) (y ^ 3)
  · have hpy : p ∣ y := hp.dvd_of_dvd_pow hy
    have hp2 : p ^ 2 ∣ y ^ 2 := pow_dvd_pow_of_dvd hpy 2
    have hy23 : y ^ 2 ∣ y ^ 3 := pow_dvd_pow y (by decide : 2 ≤ 3)
    exact dvd_mul_of_dvd_right (dvd_trans hp2 hy23) (x ^ 2)

/-- Every powerful natural number can be written in the form `x^2 * y^3`. -/
theorem isSqMulCube_of_isPowerful : ∀ n : ℕ, IsPowerful n → IsSqMulCube n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hpow
    by_cases hn0 : n = 0
    · exact ⟨0, 0, by simp [hn0]⟩
    by_cases hn1 : n = 1
    · exact ⟨1, 1, by simp [hn1]⟩
    have hn2 : 2 ≤ n := by omega
    let p := n.minFac
    have hp : p.Prime := Nat.minFac_prime (by omega)
    have hpn : p ∣ n := Nat.minFac_dvd n
    let e := n.factorization p
    have hp2n : p ^ 2 ∣ n := hpow p hp hpn
    have he2 : 2 ≤ e := by
      have hord : p ^ 2 ∣ n ↔ 2 ≤ n.factorization p := hp.pow_dvd_iff_le_factorization hn0
      exact hord.mp hp2n
    have hpe_dvd : p ^ e ∣ n := Nat.ordProj_dvd n p
    let m := n / p ^ e
    have hmul : p ^ e * m = n := Nat.mul_div_cancel' hpe_dvd
    have hp_ge2 : 2 ≤ p := hp.two_le
    have hpe_gt1 : 1 < p ^ e := by
      have h1 : 1 < p := by omega
      have h2 : p ^ 1 < p ^ e := Nat.pow_lt_pow_right h1 (by omega)
      rw [pow_one] at h2
      exact lt_trans h1 h2
    have hm_pos : 0 < m := by
      refine Nat.pos_of_ne_zero ?_
      intro hm_eq0
      rw [hm_eq0, mul_zero] at hmul
      exact hn0 hmul.symm
    have hm_lt : m < n := by
      calc m = 1 * m := (one_mul m).symm
        _ < p ^ e * m := Nat.mul_lt_mul_of_pos_right hpe_gt1 hm_pos
        _ = n := hmul
    have hp_not_dvd_m : ¬ p ∣ m := by
      intro hpm
      have hpe1 : p ^ (e + 1) ∣ n := by
        rw [← hmul, pow_succ]
        exact mul_dvd_mul_left (p ^ e) hpm
      have hle : e + 1 ≤ e := (hp.pow_dvd_iff_le_factorization hn0).mp hpe1
      omega
    have hm_pow : IsPowerful m := by
      intro q hq hqm
      have hqn : q ∣ n := by
        rw [← hmul]
        exact dvd_mul_of_dvd_right hqm (p ^ e)
      have hq2n : q ^ 2 ∣ n := hpow q hq hqn
      have hqp : q ≠ p := by
        intro heq
        rw [heq] at hqm
        exact hp_not_dvd_m hqm
      have hcop : Nat.Coprime (q ^ 2) (p ^ e) :=
        ((Nat.coprime_primes hq hp).mpr hqp).pow 2 e
      rw [← hmul] at hq2n
      exact hcop.dvd_of_dvd_mul_left hq2n
    obtain ⟨x, y, hm_eq⟩ := ih m hm_lt hm_pow
    rcases Nat.even_or_odd e with ⟨k, hk⟩ | ⟨k, hk⟩
    · refine ⟨p ^ k * x, y, ?_⟩
      have he_eq : e = 2 * k := by omega
      rw [← hmul, hm_eq, he_eq, mul_comm 2 k, pow_mul]
      ring
    · have hk1 : 1 ≤ k := by omega
      refine ⟨p ^ (k - 1) * x, p * y, ?_⟩
      have he_eq : e = 2 * (k - 1) + 3 := by omega
      rw [← hmul, hm_eq, he_eq, pow_add, mul_comm 2 (k - 1), pow_mul]
      ring

/-- Full equivalence between the canonical prime-exponent definition and `x^2 * y^3`. -/
theorem isPowerful_iff_isSqMulCube (n : ℕ) : IsPowerful n ↔ IsSqMulCube n :=
  ⟨isSqMulCube_of_isPowerful n, fun ⟨x, y, h⟩ => h ▸ isPowerful_of_sq_mul_cube x y⟩

/-- `12167 = 1^2 * 23^3` is powerful. -/
theorem isPowerful_12167 : IsPowerful 12167 := by
  have h : (12167 : ℕ) = 1 ^ 2 * 23 ^ 3 := by decide
  rw [h]
  exact isPowerful_of_sq_mul_cube 1 23

/-- `12168 = 39^2 * 2^3` is powerful. -/
theorem isPowerful_12168 : IsPowerful 12168 := by
  have h : (12168 : ℕ) = 39 ^ 2 * 2 ^ 3 := by decide
  rw [h]
  exact isPowerful_of_sq_mul_cube 39 2

/-- `12167` is not a perfect square (`110^2 < 12167 < 111^2`). -/
theorem not_isSquare_12167 : ¬ IsSquare (12167 : ℕ) := by
  rintro ⟨k, hk⟩
  have hle : k ≤ 110 ∨ 111 ≤ k := by omega
  rcases hle with h1 | h2
  · have : k * k ≤ 110 * 110 := Nat.mul_le_mul h1 h1
    omega
  · have : 111 * 111 ≤ k * k := Nat.mul_le_mul h2 h2
    omega

/-- `12168` is not a perfect square (`110^2 < 12168 < 111^2`). -/
theorem not_isSquare_12168 : ¬ IsSquare (12168 : ℕ) := by
  rintro ⟨k, hk⟩
  have hle : k ≤ 110 ∨ 111 ≤ k := by omega
  rcases hle with h1 | h2
  · have : k * k ≤ 110 * 110 := Nat.mul_le_mul h1 h1
    omega
  · have : 111 * 111 ≤ k * k := Nat.mul_le_mul h2 h2
    omega

/-- Explicit Golomb counterexample witness `(12167, 12168)`. -/
theorem jsp_000301_counterexample :
    0 < (12167 : ℕ) ∧
    IsPowerful 12167 ∧
    IsPowerful (12167 + 1) ∧
    ¬ IsSquare (12167 : ℕ) ∧
    ¬ IsSquare ((12167 + 1 : ℕ)) :=
  ⟨by decide, isPowerful_12167, isPowerful_12168, not_isSquare_12167, not_isSquare_12168⟩

/-- Formal statement of JSP-000301:
"If two consecutive positive integers are powerful, must at least one be a perfect square?" -/
def ConsecutivePowerfulSquaresStatement : Prop :=
  ∀ n : ℕ, 0 < n → IsPowerful n → IsPowerful (n + 1) → IsSquare n ∨ IsSquare (n + 1)

/-- Unconditional disproof of JSP-000301. -/
theorem jsp_000301_disproved : ¬ ConsecutivePowerfulSquaresStatement := by
  intro h
  rcases h 12167 (by decide) isPowerful_12167 isPowerful_12168 with h1 | h2
  · exact not_isSquare_12167 h1
  · exact not_isSquare_12168 h2

/-- Equivalent two-variable formulation of the unconditional disproof of JSP-000301. -/
theorem jsp_000301_disproved_pair :
    ¬ (∀ a b : ℕ, 0 < a → b = a + 1 → IsPowerful a → IsPowerful b → IsSquare a ∨ IsSquare b) := by
  intro h
  exact jsp_000301_disproved (fun n hn h1 h2 => h n (n + 1) hn rfl h1 h2)

#print axioms isPowerful_iff_isSqMulCube
#print axioms jsp_000301_counterexample
#print axioms jsp_000301_disproved
#print axioms jsp_000301_disproved_pair

end JSP_000301
