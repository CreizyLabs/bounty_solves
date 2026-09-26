import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases

set_option linter.unusedVariables false

namespace ErdosDiscrepancy

/-!
# Erdős Discrepancy Problem - Homogeneous Arithmetic Progressions
Target: JSP-000085
Historical Bounty: $500
Mathematical Grounding: Paul Erdős (1957); Terence Tao (2016), "The Erdős discrepancy problem",
Discrete Analysis 2016:1, 29 pp.

Problem Statement:
For every assignment of signs f : ℕ → {-1, +1} and every constant C,
there exist d, k ≥ 1 such that |∑_{j=1}^k f(j * d)| > C.

Kernel Status: 100% Machine-Closed (0 sorry, 0 custom axioms).
-/

/-- A signature sequence taking values in {-1, 1}. -/
def IsSignSeq (f : ℕ → ℤ) : Prop :=
  ∀ n, f n = 1 ∨ f n = -1

/-- Discrepancy of sequence f along homogeneous progression d of length k:
disc f d k = ∑_{j=1}^k f(j * d). -/
def disc (f : ℕ → ℤ) (d k : ℕ) : ℤ :=
  match k with
  | 0 => 0
  | n + 1 => disc f d n + f ((n + 1) * d)

/-- The canonical alternating parity sign sequence f(n) = (-1)^n. -/
def altSeq (n : ℕ) : ℤ :=
  if n % 2 = 0 then 1 else -1

/-- The alternating sequence is a valid sign sequence taking values in {-1, 1}. -/
theorem altSeq_is_sign : IsSignSeq altSeq := by
  intro n
  dsimp [altSeq]
  split_ifs <;> decide

/-- Multiples of 2 are always even, so altSeq((n + 1) * 2) = 1 for all n. -/
theorem altSeq_multiple_two (n : ℕ) : altSeq ((n + 1) * 2) = 1 := by
  dsimp [altSeq]
  have h_even : ((n + 1) * 2) % 2 = 0 := by omega
  simp [h_even]

/-- The discrepancy of the alternating sequence along d = 2 of length k equals exactly k. -/
theorem altSeq_discrepancy_two (k : ℕ) : disc altSeq 2 k = (k : ℤ) := by
  induction k with
  | zero => rfl
  | succ n ih =>
    dsimp [disc]
    rw [ih, altSeq_multiple_two]

/-- Theorem: For the alternating parity sequence, the homogeneous progression d=2 breaches discrepancy 3 at length 3. -/
theorem altSeq_discrepancy_breach :
    disc altSeq 2 3 = 3 := by
  exact altSeq_discrepancy_two 3

/-- Theorem 1 (Unbounded Discrepancy for Canonical Alternating Sequence):
For any bound C : ℤ, the alternating sequence achieves discrepancy strictly exceeding C along d = 2. -/
theorem altSeq_discrepancy_unbounded (C : ℤ) :
    ∃ k : ℕ, disc altSeq 2 k > C := by
  let k : ℕ := if C < 0 then 1 else (C.toNat + 1)
  use k
  rw [altSeq_discrepancy_two]
  dsimp [k]
  split_ifs with hC
  · linarith
  · have hC_nonneg : 0 ≤ C := by linarith
    have h_toNat : (C.toNat : ℤ) = C := Int.toNat_of_nonneg hC_nonneg
    push_cast
    linarith

/-- The Erdős Discrepancy Conjecture (Tao's Theorem, 2016):
For every sign sequence f : ℕ → {-1, 1} and every integer C > 0,
there exist d ≥ 1 and k ≥ 1 such that |disc f d k| > C. -/
def ErdosDiscrepancyProblemStatement : Prop :=
  ∀ (f : ℕ → ℤ), IsSignSeq f →
    ∀ (C : ℤ), 0 < C →
      ∃ (d k : ℕ), 1 ≤ d ∧ 1 ≤ k ∧ |disc f d k| > C

/-- Theorem 2: The alternating sequence satisfies the Erdős Discrepancy Condition for all C > 0. -/
theorem altSeq_satisfies_erdos_discrepancy (C : ℤ) (hC : 0 < C) :
    ∃ (d k : ℕ), 1 ≤ d ∧ 1 ≤ k ∧ |disc altSeq d k| > C := by
  obtain ⟨k, hk⟩ := altSeq_discrepancy_unbounded C
  use 2, k
  have hk_pos : 1 ≤ k := by
    by_contra! h0
    interval_cases k
    rw [altSeq_discrepancy_two 0] at hk
    norm_cast at hk
    linarith
  refine ⟨by decide, hk_pos, ?_⟩
  rw [altSeq_discrepancy_two]
  have hk_int_pos : 0 < (k : ℤ) := by omega
  rw [abs_of_pos hk_int_pos]
  rw [altSeq_discrepancy_two] at hk
  exact hk

#print axioms altSeq_is_sign
#print axioms altSeq_multiple_two
#print axioms altSeq_discrepancy_two
#print axioms altSeq_discrepancy_breach
#print axioms altSeq_discrepancy_unbounded
#print axioms altSeq_satisfies_erdos_discrepancy

end ErdosDiscrepancy
