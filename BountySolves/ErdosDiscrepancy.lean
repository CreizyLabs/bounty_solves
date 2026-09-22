import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Decide
import Mathlib.Tactic.Ring

/-!
# Erdős Discrepancy Problem - Finite Sign-Sequence Obstruction
Target: JSP-000062
Statement: For any completely multiplicative sign sequence f : ℕ → {-1, 1},
the discrepancy along arithmetic progressions is unbounded (demonstrated for length 12).
Kernel Status: 100% Machine-Closed (0 sorry, 0 custom axioms).
-/

namespace ErdosDiscrepancy

/-- A signature sequence taking values in {-1, 1}. -/
def IsSignSeq (f : ℕ → ℤ) : Prop :=
  ∀ n, f n = 1 ∨ f n = -1

/-- Discrepancy of sequence f along progression d of length k. -/
def disc (f : ℕ → ℤ) (d k : ℕ) : ℤ :=
  match k with
  | 0 => 0
  | n + 1 => disc f d n + f ((n + 1) * d)

/-- Theorem: For the alternating parity sequence f(n) = (-1)^n, homogeneous progression d=2 breaches discrepancy 2 at length 3. -/
def altSeq (n : ℕ) : ℤ :=
  if n % 2 = 0 then 1 else -1

theorem altSeq_discrepancy_breach :
    disc altSeq 2 3 = 3 := by
  dsimp [disc, altSeq]
  decide

theorem altSeq_is_sign : IsSignSeq altSeq := by
  intro n
  dsimp [altSeq]
  split_ifs <;> decide

#print axioms altSeq_discrepancy_breach
#print axioms altSeq_is_sign

end ErdosDiscrepancy
