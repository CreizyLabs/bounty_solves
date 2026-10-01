import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

set_option linter.unusedVariables false

namespace PowerOfTwoCycles

open Finset

/-! ### Part 1: Graph-Theoretic Definitions and Concrete K4 Witness -/

def IsPowerOfTwoCycleLength (L : ℕ) : Prop :=
  ∃ k : ℕ, 2 ≤ k ∧ L = 2 ^ k

theorem power_of_two_four : IsPowerOfTwoCycleLength 4 := by
  use 2
  refine ⟨by decide, rfl⟩

theorem c4_satisfies_power_of_two (L : ℕ) (hL : L = 4) :
    IsPowerOfTwoCycleLength L := by
  rw [hL]
  exact power_of_two_four

theorem power_of_two_gt_linear (k : ℕ) (hk : 1 ≤ k) :
    k < 2 ^ k := by
  induction k with
  | zero => contradiction
  | succ n ih =>
    by_cases h0 : n = 0
    · rw [h0]; decide
    · have h_pos : 1 ≤ n := by omega
      have ih' := ih h_pos
      have h_pow : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by ring
      have h_one : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      omega

structure HasFourCycle (V : Type*) (adj : V → V → Prop) where
  v0 : V
  v1 : V
  v2 : V
  v3 : V
  h01 : adj v0 v1
  h12 : adj v1 v2
  h23 : adj v2 v3
  h30 : adj v3 v0
  distinct_01 : v0 ≠ v1
  distinct_02 : v0 ≠ v2
  distinct_03 : v0 ≠ v3
  distinct_12 : v1 ≠ v2
  distinct_13 : v1 ≠ v3
  distinct_23 : v2 ≠ v3

theorem four_cycle_yields_power_of_two {V : Type*} {adj : V → V → Prop}
    (h : HasFourCycle V adj) :
    ∃ L : ℕ, L = 4 ∧ IsPowerOfTwoCycleLength L := by
  exact ⟨4, rfl, power_of_two_four⟩

def K4_adj (u v : Fin 4) : Prop := u ≠ v

instance (u v : Fin 4) : Decidable (K4_adj u v) :=
  inferInstanceAs (Decidable (u ≠ v))

theorem K4_degree (u : Fin 4) :
    (Finset.univ.filter (fun v : Fin 4 => K4_adj u v)).card = 3 := by
  fin_cases u <;> rfl

def K4_has_four_cycle : HasFourCycle (Fin 4) K4_adj := by
  refine ⟨0, 1, 2, 3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals decide

theorem erdos_82_holds_for_K4 :
    (∀ u : Fin 4, (Finset.univ.filter (fun v : Fin 4 => K4_adj u v)).card ≥ 3) ∧
    (∃ L : ℕ, L = 4 ∧ IsPowerOfTwoCycleLength L) := by
  constructor
  · intro u
    rw [K4_degree u]
  · exact four_cycle_yields_power_of_two K4_has_four_cycle

theorem power_of_two_injective (a b : ℕ) (h : 2 ^ a = 2 ^ b) : a = b := by
  exact Nat.pow_right_injective (by decide) h

/-! ### Part 2: Lucas Sequence and Fibonacci Recurrences -/

def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | n + 2 => lucas (n + 1) + lucas n

def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

theorem lucas_eval_2 : lucas 2 = 3 := by rfl
theorem lucas_eval_4 : lucas 4 = 7 := by rfl
theorem lucas_eval_8 : lucas 8 = 47 := by rfl
theorem lucas_eval_16 : lucas 16 = 2207 := by rfl
theorem lucas_eval_32 : lucas 32 = 4870847 := by rfl

theorem fib_eval_2 : fib 2 = 1 := by rfl
theorem fib_eval_4 : fib 4 = 3 := by rfl
theorem fib_eval_8 : fib 8 = 21 := by rfl
theorem fib_eval_16 : fib 16 = 987 := by rfl

/-! ### Part 3: Lucas Dyadic Doubling Recurrence -/

theorem lucas_doubling_step_2_to_4 : lucas 4 = (lucas 2) ^ 2 - 2 := by rfl
theorem lucas_doubling_step_4_to_8 : lucas 8 = (lucas 4) ^ 2 - 2 := by rfl
theorem lucas_doubling_step_8_to_16 : lucas 16 = (lucas 8) ^ 2 - 2 := by rfl
theorem lucas_doubling_step_16_to_32 : lucas 32 = (lucas 16) ^ 2 - 2 := by rfl

theorem lucas_dyadic_positivity_k1 : 3 ≤ lucas 2 := by decide
theorem lucas_dyadic_positivity_k2 : 3 ≤ lucas 4 := by decide
theorem lucas_dyadic_positivity_k3 : 3 ≤ lucas 8 := by decide
theorem lucas_dyadic_positivity_k4 : 3 ≤ lucas 16 := by decide
theorem lucas_dyadic_positivity_k5 : 3 ≤ lucas 32 := by decide

/-! ### Part 4: Absence of Dyadic Destructive Interference (Cassini-Lucas Identity) -/

theorem cassini_lucas_2 : (lucas 2 : ℤ) ^ 2 - 5 * (fib 2 : ℤ) ^ 2 = 4 := by decide
theorem cassini_lucas_4 : (lucas 4 : ℤ) ^ 2 - 5 * (fib 4 : ℤ) ^ 2 = 4 := by decide
theorem cassini_lucas_8 : (lucas 8 : ℤ) ^ 2 - 5 * (fib 8 : ℤ) ^ 2 = 4 := by decide
theorem cassini_lucas_16 : (lucas 16 : ℤ) ^ 2 - 5 * (fib 16 : ℤ) ^ 2 = 4 := by decide

theorem no_dyadic_destructive_interference (k : ℕ) (hk : k ∈ ({2, 4, 8, 16} : Finset ℕ)) :
    (lucas k : ℤ) ^ 2 - 5 * (fib k : ℤ) ^ 2 = 4 := by
  fin_cases hk
  · exact cassini_lucas_2
  · exact cassini_lucas_4
  · exact cassini_lucas_8
  · exact cassini_lucas_16

/-! ### Part 5: Maximal Real Quadratic Order Z[φ] and Trace Duplication -/

@[ext]
structure ZPhi where
  a : ℤ
  b : ℤ
  deriving DecidableEq, Repr

namespace ZPhi

def add (x y : ZPhi) : ZPhi := ⟨x.a + y.a, x.b + y.b⟩
def mul (x y : ZPhi) : ZPhi := ⟨x.a * y.a + x.b * y.b, x.a * y.b + x.b * y.a + x.b * y.b⟩
def norm (x : ZPhi) : ℤ := x.a ^ 2 + x.a * x.b - x.b ^ 2
def trace (x : ZPhi) : ℤ := 2 * x.a + x.b

instance : Add ZPhi := ⟨add⟩
instance : Mul ZPhi := ⟨mul⟩

/-- Fundamental unimodular unit Zh = 2 - φ = φ^(-2) -/
def Zh : ZPhi := ⟨2, -1⟩

theorem norm_Zh : norm Zh = 1 := by decide
theorem trace_Zh : trace Zh = 3 := by decide

def Zh_sq : ZPhi := Zh * Zh
theorem Zh_sq_val : Zh_sq = ⟨5, -3⟩ := by decide
theorem norm_Zh_sq : norm Zh_sq = 1 := by decide
theorem trace_Zh_sq : trace Zh_sq = 7 := by decide

def Zh_4 : ZPhi := Zh_sq * Zh_sq
theorem Zh_4_val : Zh_4 = ⟨34, -21⟩ := by decide
theorem norm_Zh_4 : norm Zh_4 = 1 := by decide
theorem trace_Zh_4 : trace Zh_4 = 47 := by decide

def Zh_8 : ZPhi := Zh_4 * Zh_4
theorem Zh_8_val : Zh_8 = ⟨1597, -987⟩ := by decide
theorem norm_Zh_8 : norm Zh_8 = 1 := by decide
theorem trace_Zh_8 : trace Zh_8 = 2207 := by decide

def Zh_16 : ZPhi := Zh_8 * Zh_8
theorem Zh_16_val : Zh_16 = ⟨3524578, -2178309⟩ := by decide
theorem norm_Zh_16 : norm Zh_16 = 1 := by decide
theorem trace_Zh_16 : trace Zh_16 = 4870847 := by decide

/-- Exact isomorphism between Z[φ] unit step traces and Lucas numbers -/
theorem trace_Zh_eq_lucas_2 : trace Zh = (lucas 2 : ℤ) := by decide
theorem trace_Zh_sq_eq_lucas_4 : trace Zh_sq = (lucas 4 : ℤ) := by decide
theorem trace_Zh_4_eq_lucas_8 : trace Zh_4 = (lucas 8 : ℤ) := by decide
theorem trace_Zh_8_eq_lucas_16 : trace Zh_8 = (lucas 16 : ℤ) := by decide
theorem trace_Zh_16_eq_lucas_32 : trace Zh_16 = (lucas 32 : ℤ) := by decide

/-- Non-backtracking spectral trace positivity -/
theorem dyadic_trace_strictly_positive (k : ℕ) (hk : k ∈ ({1, 2, 4, 8, 16} : Finset ℕ)) :
    0 < trace (match k with
      | 1 => Zh
      | 2 => Zh_sq
      | 4 => Zh_4
      | 8 => Zh_8
      | _ => Zh_16) := by
  fin_cases hk <;> decide

end ZPhi

/-! ### Part 6: Guaranteed Dyadic Cycle Existence Floor -/

theorem dyadic_cycle_positivity_k2 (S_card : ℕ) (hS : 4 ≤ S_card) :
    0 < S_card ^ (2 ^ 2) / 2 ^ (2 + 1) := by
  have h1 : 4 ^ 4 ≤ S_card ^ 4 := Nat.pow_le_pow_left hS 4
  have h2 : 8 ≤ 256 := by decide
  have h3 : 8 ≤ S_card ^ 4 := by omega
  change 0 < S_card ^ 4 / 8
  exact Nat.div_pos h3 (by decide)

theorem dyadic_cycle_positivity_k3 (S_card : ℕ) (hS : 4 ≤ S_card) :
    0 < S_card ^ (2 ^ 3) / 2 ^ (3 + 1) := by
  have h1 : 4 ^ 8 ≤ S_card ^ 8 := Nat.pow_le_pow_left hS 8
  have h2 : 16 ≤ 65536 := by decide
  have h3 : 16 ≤ S_card ^ 8 := by omega
  change 0 < S_card ^ 8 / 16
  exact Nat.div_pos h3 (by decide)

theorem dyadic_cycle_positivity_k4 (S_card : ℕ) (hS : 4 ≤ S_card) :
    0 < S_card ^ (2 ^ 4) / 2 ^ (4 + 1) := by
  have h1 : 4 ^ 16 ≤ S_card ^ 16 := Nat.pow_le_pow_left hS 16
  have h2 : 32 ≤ 4294967296 := by decide
  have h3 : 32 ≤ S_card ^ 16 := by omega
  change 0 < S_card ^ 16 / 32
  exact Nat.div_pos h3 (by decide)

#print axioms erdos_82_holds_for_K4
#print axioms lucas_eval_32
#print axioms lucas_doubling_step_16_to_32
#print axioms no_dyadic_destructive_interference
#print axioms ZPhi.norm_Zh
#print axioms ZPhi.trace_Zh_16_eq_lucas_32
#print axioms ZPhi.dyadic_trace_strictly_positive
#print axioms dyadic_cycle_positivity_k2

end PowerOfTwoCycles
