import Mathlib.Data.Nat.Prime.Basic

theorem singular_factor_exceeds_one (p : ℕ) (_hp : Nat.Prime p) (hp3 : p ≥ 3) :
    p - 1 > p - 2 := by omega

theorem goldbach_4 : ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = 4 := ⟨2, 2, by decide, by decide, by decide⟩
theorem goldbach_6 : ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = 6 := ⟨3, 3, by decide, by decide, by decide⟩
theorem goldbach_8 : ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = 8 := ⟨3, 5, by decide, by decide, by decide⟩
theorem goldbach_10 : ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = 10 := ⟨5, 5, by decide, by decide, by decide⟩
theorem goldbach_12 : ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = 12 := ⟨5, 7, by decide, by decide, by decide⟩
theorem goldbach_14 : ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = 14 := ⟨7, 7, by decide, by decide, by decide⟩
theorem goldbach_16 : ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = 16 := ⟨5, 11, by decide, by decide, by decide⟩
theorem goldbach_18 : ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = 18 := ⟨7, 11, by decide, by decide, by decide⟩
theorem goldbach_20 : ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = 20 := ⟨7, 13, by decide, by decide, by decide⟩
theorem goldbach_22 : ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = 22 := ⟨11, 11, by decide, by decide, by decide⟩
theorem goldbach_24 : ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = 24 := ⟨11, 13, by decide, by decide, by decide⟩
theorem goldbach_26 : ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = 26 := ⟨13, 13, by decide, by decide, by decide⟩
theorem goldbach_28 : ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = 28 := ⟨11, 17, by decide, by decide, by decide⟩
theorem goldbach_30 : ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = 30 := ⟨13, 17, by decide, by decide, by decide⟩
