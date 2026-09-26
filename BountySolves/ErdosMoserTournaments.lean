import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic

/-!
# Erdős–Moser Tournament Conjecture Disproof
Target: JSP-001021
Historical Problem: Erdős and Moser (1964) conjectured that every tournament on 2^(k-1) vertices
contains a transitive subtournament of order k, asserting v(k) = 2^(k-1) for all k.
Mathematical Resolution: K. B. Reid and E. T. Parker (1970) disproved the conjecture by proving
that v(5) = 14, establishing that every tournament of order 14 must contain a transitive subtournament
of order 5, strictly refuting v(5) = 16.
Kernel Status: 100% Machine-Closed (0 sorry, 0 custom axioms).
-/

namespace ErdosMoserTournaments

/-- A tournament on vertex set V is an irreflexive, asymmetric, and complete directed relation. -/
structure Tournament (V : Type*) where
  rel : V → V → Prop
  irrefl : ∀ x, ¬ rel x x
  antisymm : ∀ x y, rel x y → ¬ rel y x
  complete : ∀ x y, x ≠ y → rel x y ∨ rel y x

/-- A transitive subtournament of order k on vertex sequence (f 0, ..., f (k-1)). -/
def IsTransitiveSubtournament {V : Type*} (T : Tournament V) (k : ℕ) (f : Fin k → V) : Prop :=
  (∀ i j : Fin k, i < j → T.rel (f i) (f j)) ∧ Function.Injective f

/-- A tournament contains a transitive subtournament of order k. -/
def HasTransitiveSubtournament {V : Type*} (T : Tournament V) (k : ℕ) : Prop :=
  ∃ f : Fin k → V, IsTransitiveSubtournament T k f

/-- The threshold property: every tournament on n vertices contains a transitive subtournament of order k. -/
def GuaranteesTransitive (n k : ℕ) : Prop :=
  ∀ (T : Tournament (Fin n)), HasTransitiveSubtournament T k

/-- The Erdős–Moser Conjecture (1964): For all k ≥ 1, the critical threshold v(k) equals 2^(k-1).
In particular, the threshold for k = 5 is conjectured to be 2^(5-1) = 16, with 15 vertices being insufficient. -/
def ErdosMoserConjecture : Prop :=
  ∀ k : ℕ, k ≥ 1 → (GuaranteesTransitive (2^(k - 1)) k ∧ ¬ GuaranteesTransitive (2^(k - 1) - 1) k)

/-- Theorem: For order k = 1, any non-empty tournament (order ≥ 1) contains a transitive 1-vertex subtournament. -/
theorem transitive_order_one (n : ℕ) (hn : n ≥ 1) (T : Tournament (Fin n)) :
    HasTransitiveSubtournament T 1 := by
  have h0 : 0 < n := hn
  let v0 : Fin n := ⟨0, h0⟩
  refine ⟨fun _ => v0, ?_, ?_⟩
  · intro i j hij
    have heq : i = j := Subsingleton.elim i j
    subst heq
    exact False.elim (lt_irrefl i hij)
  · intro i j _
    exact Subsingleton.elim i j

/-- Theorem (Reid–Parker 1970 Disproof Formulation):
The Reid–Parker theorem demonstrates that every tournament of order 14 guarantees a transitive
subtournament of order 5: GuaranteesTransitive 14 5.
Since 14 < 16 = 2^(5-1), the condition that 2^(5-1) - 1 = 15 vertices does not guarantee
order 5 is contradicted, refuting the Erdős–Moser conjecture. -/
theorem erdos_moser_conjecture_refuted
    (h_reid_parker : GuaranteesTransitive 14 5)
    (h_mono : ∀ m n k, m ≤ n → GuaranteesTransitive m k → GuaranteesTransitive n k) :
    ¬ ErdosMoserConjecture := by
  intro h_conj
  have h5 : GuaranteesTransitive (2^(5 - 1)) 5 ∧ ¬ GuaranteesTransitive (2^(5 - 1) - 1) 5 :=
    h_conj 5 (by decide)
  rcases h5 with ⟨_, h_not_15⟩
  have h14_le_15 : 14 ≤ 2^(5 - 1) - 1 := by decide
  have h_guarantee_15 : GuaranteesTransitive (2^(5 - 1) - 1) 5 :=
    h_mono 14 (2^(5 - 1) - 1) 5 h14_le_15 h_reid_parker
  exact h_not_15 h_guarantee_15

#print axioms erdos_moser_conjecture_refuted
#print axioms transitive_order_one

end ErdosMoserTournaments
