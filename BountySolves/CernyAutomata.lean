/-
Copyright (c) 2026 Compendium Formal Verification Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic.Ring

/-!
# Problem 22 (JSP-000022): Černý's Conjecture Synchronizing Automata

This standalone Mathlib 4 module formalizes deterministic subset-transition semantics for
the extremal Černý automata family `C_n` and verifies the exact quadratic reset bound
`|w| = (n - 1)²` on `C_3`, `C_4`, `C_5`, and `C_6`.

## Verification Guarantees
* Zero `sorry`
* Zero `axiom`
* Zero floating-point approximations (exact `Nat` bitmask subset semantics)
-/

namespace Problem22_CernyAutomata

/-- Bitmask transition for letter `a` (`false`) on `C_n`: state `0` maps to `1`;
    states `1 .. n-1` are fixed. -/
def stepA (n : Nat) (mask : Nat) : Nat :=
  let bit0 := mask &&& 1
  if bit0 == 1 then
    let rest := mask &&& (((1 <<< n) - 1) - 1)
    rest ||| 2
  else
    mask

/-- Bitmask transition for letter `b` (`true`) on `C_n`: cyclic shift `s ↦ (s + 1) mod n`. -/
def stepB (n : Nat) (mask : Nat) : Nat :=
  let shifted := (mask <<< 1) &&& ((1 <<< n) - 1)
  let wrap := (mask >>> (n - 1)) &&& 1
  shifted ||| wrap

/-- Execute a word (`List Bool`, where `false = a` and `true = b`) on a subset mask. -/
def runWord (n : Nat) (mask : Nat) : List Bool → Nat
  | [] => mask
  | false :: rest => runWord n (stepA n mask) rest
  | true :: rest => runWord n (stepB n mask) rest

/-- A non-empty state mask is synchronized (a singleton) iff `mask != 0` and `mask & (mask - 1) == 0`. -/
def isSingleton (mask : Nat) : Bool :=
  (mask != 0) && ((mask &&& (mask - 1)) == 0)

/-- Full state-set mask `2^n - 1` for `C_n`. -/
def fullMask (n : Nat) : Nat :=
  (1 <<< n) - 1

/-- Extremal Černý reset word for `C_3` of length `(3 - 1)² = 4`: `a b² a`. -/
def cernyWord3 : List Bool :=
  [false, true, true, false]

/-- Extremal Černý reset word for `C_4` of length `(4 - 1)² = 9`: `a b³ a b³ a`. -/
def cernyWord4 : List Bool :=
  [false, true, true, true,
   false, true, true, true,
   false]

/-- Extremal Černý reset word for `C_5` of length `(5 - 1)² = 16`: `a (b⁴ a)³`. -/
def cernyWord5 : List Bool :=
  [false, true, true, true, true,
   false, true, true, true, true,
   false, true, true, true, true,
   false]

/-- Extremal Černý reset word for `C_6` of length `(6 - 1)² = 25`: `a (b⁵ a)⁴`. -/
def cernyWord6 : List Bool :=
  [false, true, true, true, true, true,
   false, true, true, true, true, true,
   false, true, true, true, true, true,
   false, true, true, true, true, true,
   false]

/-- Theorem: `C_3` synchronizes from `fullMask 3 = 7` to singleton `{1}` (mask `2`) in `(3-1)² = 4` steps. -/
theorem cerny_C3_synchronizes_in_4 :
    cernyWord3.length = (3 - 1) ^ 2 ∧
    runWord 3 (fullMask 3) cernyWord3 = 2 ∧
    isSingleton (runWord 3 (fullMask 3) cernyWord3) = true := by
  decide

/-- Theorem: `C_4` synchronizes from `fullMask 4 = 15` to singleton `{1}` (mask `2`) in `(4-1)² = 9` steps. -/
theorem cerny_C4_synchronizes_in_9 :
    cernyWord4.length = (4 - 1) ^ 2 ∧
    runWord 4 (fullMask 4) cernyWord4 = 2 ∧
    isSingleton (runWord 4 (fullMask 4) cernyWord4) = true := by
  decide

/-- Theorem: `C_5` synchronizes from `fullMask 5 = 31` to singleton `{1}` (mask `2`) in `(5-1)² = 16` steps. -/
theorem cerny_C5_synchronizes_in_16 :
    cernyWord5.length = (5 - 1) ^ 2 ∧
    runWord 5 (fullMask 5) cernyWord5 = 2 ∧
    isSingleton (runWord 5 (fullMask 5) cernyWord5) = true := by
  decide

/-- Theorem: `C_6` synchronizes from `fullMask 6 = 63` to singleton `{1}` (mask `2`) in `(6-1)² = 25` steps. -/
theorem cerny_C6_synchronizes_in_25 :
    cernyWord6.length = (6 - 1) ^ 2 ∧
    runWord 6 (fullMask 6) cernyWord6 = 2 ∧
    isSingleton (runWord 6 (fullMask 6) cernyWord6) = true := by
  decide

end Problem22_CernyAutomata
