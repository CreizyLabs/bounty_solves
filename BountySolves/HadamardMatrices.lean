/-
Copyright (c) 2026 Compendium Formal Verification Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic.Ring

/-!
# Problem 13 (JSP-000013): Hadamard Matrix Orthogonality `H * H^T = n * I_n`

This standalone Mathlib 4 module formalizes exact `±1` entry validation and row-orthogonality
verification `H * H^T = n * I_n` for Sylvester and Paley Hadamard matrices of orders
`n = 1, 2, 4, 8, 12` without relying on version-fragile list indexing helpers.

## Verification Guarantees
* Zero `sorry`
* Zero `axiom`
* Zero floating-point approximations (exact `Int` inner-product evaluation)
-/

namespace Problem13_HadamardMatrices

/-- Exact integer dot product of two matrix rows. -/
def dotRow : List Int → List Int → Int
  | [], _ => 0
  | _, [] => 0
  | x :: xs, y :: ys => x * y + dotRow xs ys

/-- Check that every entry in a row belongs to `{-1, +1}`. -/
def isUnitRow : List Int → Bool
  | [] => true

  | x :: xs => (x == 1 || x == -1) && isUnitRow xs

/-- Check that a matrix has `n` rows, each of length `n`, with all entries in `{-1, +1}`. -/
def isSignMatrix (H : List (List Int)) (n : Nat) : Bool :=
  (H.length == n) && H.all (fun r => (r.length == n) && isUnitRow r)

/-- Check that row `r` is orthogonal to every row in `rest` (`dotRow r r' == 0`). -/
def isOrthogonalToAll (r : List Int) : List (List Int) → Bool
  | [] => true
  | r' :: rest => (dotRow r r' == 0) && isOrthogonalToAll r rest

/-- Recursive upper-triangular verification of `H * H^T = n * I_n`:
    every row has self-inner-product `n` and is orthogonal to all subsequent rows. -/
def checkGramIdentity (n : Int) : List (List Int) → Bool
  | [] => true
  | r :: rest => (dotRow r r == n) && isOrthogonalToAll r rest && checkGramIdentity n rest

/-- Complete boolean predicate certifying that `H` is an `n × n` Hadamard matrix. -/
def isHadamardMatrix (H : List (List Int)) (n : Nat) : Bool :=
  isSignMatrix H n && checkGramIdentity (Int.ofNat n) H

/-- Order 1 Hadamard Matrix `H_1`. -/
def H1 : List (List Int) :=
  [[1]]

/-- Order 2 Sylvester Hadamard Matrix `H_2`. -/
def H2 : List (List Int) :=
  [[ 1,  1],
   [ 1, -1]]

/-- Order 4 Sylvester Hadamard Matrix `H_4`. -/
def H4 : List (List Int) :=
  [[ 1,  1,  1,  1],
   [ 1, -1,  1, -1],
   [ 1,  1, -1, -1],
   [ 1, -1, -1,  1]]

/-- Order 8 Sylvester Hadamard Matrix `H_8`. -/
def H8 : List (List Int) :=
  [[ 1,  1,  1,  1,  1,  1,  1,  1],
   [ 1, -1,  1, -1,  1, -1,  1, -1],
   [ 1,  1, -1, -1,  1,  1, -1, -1],
   [ 1, -1, -1,  1,  1, -1, -1,  1],
   [ 1,  1,  1,  1, -1, -1, -1, -1],
   [ 1, -1,  1, -1, -1,  1, -1,  1],
   [ 1,  1, -1, -1, -1, -1,  1,  1],
   [ 1, -1, -1,  1, -1,  1,  1, -1]]

/-- Order 12 Paley Hadamard Matrix `H_12` constructed from quadratic residues mod 11. -/
def H12 : List (List Int) :=
  [[ 1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1],
   [ 1, -1,  1, -1,  1,  1,  1, -1, -1, -1,  1, -1],
   [ 1, -1, -1,  1, -1,  1,  1,  1, -1, -1, -1,  1],
   [ 1,  1, -1, -1,  1, -1,  1,  1,  1, -1, -1, -1],
   [ 1, -1,  1, -1, -1,  1, -1,  1,  1,  1, -1, -1],
   [ 1, -1, -1,  1, -1, -1,  1, -1,  1,  1,  1, -1],
   [ 1, -1, -1, -1,  1, -1, -1,  1, -1,  1,  1,  1],
   [ 1,  1, -1, -1, -1,  1, -1, -1,  1, -1,  1,  1],
   [ 1,  1,  1, -1, -1, -1,  1, -1, -1,  1, -1,  1],
   [ 1,  1,  1,  1, -1, -1, -1,  1, -1, -1,  1, -1],
   [ 1, -1,  1,  1,  1, -1, -1, -1,  1, -1, -1,  1],
   [ 1,  1, -1,  1,  1,  1, -1, -1, -1,  1, -1, -1]]

/-- Theorem (JSP-000013 Hadamard Order 4): Exact verification of `H_4 * H_4^T = 4 * I_4`. -/
theorem hadamard_order_4_orthogonal : isHadamardMatrix H4 4 = true := by
  decide

/-- Theorem (JSP-000013 Sylvester & Paley Hadamard Spectrum `n ∈ {1, 2, 4, 8, 12}`):
    Exact verification of `H_n * H_n^T = n * I_n` and `±1` entries across orders 1, 2, 4, 8, and 12. -/
theorem hadamard_orders_1_2_4_8_12_verified :
    isHadamardMatrix H1 1 = true ∧
    isHadamardMatrix H2 2 = true ∧
    isHadamardMatrix H4 4 = true ∧
    isHadamardMatrix H8 8 = true ∧
    isHadamardMatrix H12 12 = true := by
  decide

end Problem13_HadamardMatrices
/-
Copyright (c) 2026 Compendium Formal Verification Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic.Ring

/-!
# Problem 13 (JSP-000013): Hadamard Matrix Orthogonality `H * H^T = n * I_n`

This standalone Mathlib 4 module formalizes exact `±1` entry validation and row-orthogonality
verification `H * H^T = n * I_n` for Sylvester and Paley Hadamard matrices of orders
`n = 1, 2, 4, 8, 12` without relying on version-fragile list indexing helpers.

## Verification Guarantees
* Zero `sorry`
* Zero `axiom`
* Zero floating-point approximations (exact `Int` inner-product evaluation)
-/

namespace Problem13_HadamardMatrices

/-- Exact integer dot product of two matrix rows. -/
def dotRow : List Int → List Int → Int
  | [], _ => 0
  | _, [] => 0
  | x :: xs, y :: ys => x * y + dotRow xs ys

/-- Check that every entry in a row belongs to `{-1, +1}`. -/
def isUnitRow : List Int → Bool
  | [] => true

  | x :: xs => (x == 1 || x == -1) && isUnitRow xs

/-- Check that a matrix has `n` rows, each of length `n`, with all entries in `{-1, +1}`. -/
def isSignMatrix (H : List (List Int)) (n : Nat) : Bool :=
  (H.length == n) && H.all (fun r => (r.length == n) && isUnitRow r)

/-- Check that row `r` is orthogonal to every row in `rest` (`dotRow r r' == 0`). -/
def isOrthogonalToAll (r : List Int) : List (List Int) → Bool
  | [] => true
  | r' :: rest => (dotRow r r' == 0) && isOrthogonalToAll r rest

/-- Recursive upper-triangular verification of `H * H^T = n * I_n`:
    every row has self-inner-product `n` and is orthogonal to all subsequent rows. -/
def checkGramIdentity (n : Int) : List (List Int) → Bool
  | [] => true
  | r :: rest => (dotRow r r == n) && isOrthogonalToAll r rest && checkGramIdentity n rest

/-- Complete boolean predicate certifying that `H` is an `n × n` Hadamard matrix. -/
def isHadamardMatrix (H : List (List Int)) (n : Nat) : Bool :=
  isSignMatrix H n && checkGramIdentity (Int.ofNat n) H

/-- Order 1 Hadamard Matrix `H_1`. -/
def H1 : List (List Int) :=
  [[1]]

/-- Order 2 Sylvester Hadamard Matrix `H_2`. -/
def H2 : List (List Int) :=
  [[ 1,  1],
   [ 1, -1]]

/-- Order 4 Sylvester Hadamard Matrix `H_4`. -/
def H4 : List (List Int) :=
  [[ 1,  1,  1,  1],
   [ 1, -1,  1, -1],
   [ 1,  1, -1, -1],
   [ 1, -1, -1,  1]]

/-- Order 8 Sylvester Hadamard Matrix `H_8`. -/
def H8 : List (List Int) :=
  [[ 1,  1,  1,  1,  1,  1,  1,  1],
   [ 1, -1,  1, -1,  1, -1,  1, -1],
   [ 1,  1, -1, -1,  1,  1, -1, -1],
   [ 1, -1, -1,  1,  1, -1, -1,  1],
   [ 1,  1,  1,  1, -1, -1, -1, -1],
   [ 1, -1,  1, -1, -1,  1, -1,  1],
   [ 1,  1, -1, -1, -1, -1,  1,  1],
   [ 1, -1, -1,  1, -1,  1,  1, -1]]

/-- Order 12 Paley Hadamard Matrix `H_12` constructed from quadratic residues mod 11. -/
def H12 : List (List Int) :=
  [[ 1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1],
   [ 1, -1,  1, -1,  1,  1,  1, -1, -1, -1,  1, -1],
   [ 1, -1, -1,  1, -1,  1,  1,  1, -1, -1, -1,  1],
   [ 1,  1, -1, -1,  1, -1,  1,  1,  1, -1, -1, -1],
   [ 1, -1,  1, -1, -1,  1, -1,  1,  1,  1, -1, -1],
   [ 1, -1, -1,  1, -1, -1,  1, -1,  1,  1,  1, -1],
   [ 1, -1, -1, -1,  1, -1, -1,  1, -1,  1,  1,  1],
   [ 1,  1, -1, -1, -1,  1, -1, -1,  1, -1,  1,  1],
   [ 1,  1,  1, -1, -1, -1,  1, -1, -1,  1, -1,  1],
   [ 1,  1,  1,  1, -1, -1, -1,  1, -1, -1,  1, -1],
   [ 1, -1,  1,  1,  1, -1, -1, -1,  1, -1, -1,  1],
   [ 1,  1, -1,  1,  1,  1, -1, -1, -1,  1, -1, -1]]

/-- Theorem (JSP-000013 Hadamard Order 4): Exact verification of `H_4 * H_4^T = 4 * I_4`. -/
theorem hadamard_order_4_orthogonal : isHadamardMatrix H4 4 = true := by
  decide

/-- Theorem (JSP-000013 Sylvester & Paley Hadamard Spectrum `n ∈ {1, 2, 4, 8, 12}`):
    Exact verification of `H_n * H_n^T = n * I_n` and `±1` entries across orders 1, 2, 4, 8, and 12. -/
theorem hadamard_orders_1_2_4_8_12_verified :
    isHadamardMatrix H1 1 = true ∧
    isHadamardMatrix H2 2 = true ∧
    isHadamardMatrix H4 4 = true ∧
    isHadamardMatrix H8 8 = true ∧
    isHadamardMatrix H12 12 = true := by
  decide

end Problem13_HadamardMatrices
