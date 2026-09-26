import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option linter.unusedVariables false

namespace SunflowerLemma

variable {α : Type*} [DecidableEq α]

/-- An r-sunflower in a family F with core C is a subfamily S ⊆ F of cardinality r
    such that every pair of distinct sets in S has intersection equal to C. -/
def IsSunflower (S : Finset (Finset α)) (C : Finset α) (r : ℕ) : Prop :=
  S.card = r ∧ ∀ A ∈ S, ∀ B ∈ S, A ≠ B → A ∩ B = C

/-- A family F contains an r-sunflower if there exists S ⊆ F and core C such that
    S is an r-sunflower with core C. -/
def HasSunflower (F : Finset (Finset α)) (r : ℕ) : Prop :=
  ∃ S : Finset (Finset α), S ⊆ F ∧ ∃ C : Finset α, IsSunflower S C r

/-- Factorial function. -/
def fact : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- Factorial is strictly positive. -/
theorem fact_pos (n : ℕ) : 0 < fact n := by
  induction n with
  | zero => decide
  | succ n ih =>
    dsimp [fact]
    have h1 : 0 < n + 1 := Nat.succ_pos n
    exact Nat.mul_pos h1 ih

/-- Erdős-Rado bound: f(k, r) = k! * (r - 1)^k. -/
def erdos_rado_bound (k r : ℕ) : ℕ :=
  fact k * (r - 1)^k

/-- Factorial recurrence: f(k+1, r) = (k+1) * (r-1) * f(k, r). -/
theorem erdos_rado_recurrence (k r : ℕ) :
    erdos_rado_bound (k + 1) r = (k + 1) * (r - 1) * erdos_rado_bound k r := by
  dsimp [erdos_rado_bound, fact]
  rw [pow_succ]
  ring

/-- Disjoint sets form a sunflower with empty core. -/
theorem sunflower_of_pairwise_disjoint (S : Finset (Finset α)) (r : ℕ)
    (hS_card : S.card = r)
    (h_disj : ∀ A ∈ S, ∀ B ∈ S, A ≠ B → A ∩ B = ∅) :
    IsSunflower S ∅ r :=
  ⟨hS_card, h_disj⟩

/-- Lifting lemma: If a family of sets all containing an element x contains a sunflower S'
    after removing x (with core C'), then adding x back to each set gives a sunflower S
    with core C' ∪ {x}. -/
theorem sunflower_lift (F : Finset (Finset α)) (x : α) (r : ℕ)
    (S' : Finset (Finset α)) (C' : Finset α)
    (h_sun : IsSunflower S' C' r)
    (h_x_not_in : ∀ B ∈ S', x ∉ B)
    (h_lift_in_F : ∀ B ∈ S', B ∪ {x} ∈ F) :
    HasSunflower F r := by
  let f : Finset α → Finset α := fun B => B ∪ {x}
  let S := S'.image f
  have h_inj : ∀ A ∈ S', ∀ B ∈ S', f A = f B → A = B := by
    intro A hA B hB heq
    dsimp [f] at heq
    have hAx : x ∉ A := h_x_not_in A hA
    have hBx : x ∉ B := h_x_not_in B hB
    ext y
    by_cases hy : y = x
    · subst hy
      simp [hAx, hBx]
    · have h_elem : y ∈ A ∪ {x} ↔ y ∈ B ∪ {x} := by rw [heq]
      simp only [Finset.mem_union, Finset.mem_singleton] at h_elem
      constructor
      · intro hyA
        have : y ∈ A ∨ y = x := Or.inl hyA
        have h_or := h_elem.mp this
        rcases h_or with hyB | heqx
        · exact hyB
        · exact False.elim (hy heqx)
      · intro hyB
        have : y ∈ B ∨ y = x := Or.inl hyB
        have h_or := h_elem.mpr this
        rcases h_or with hyA | heqx
        · exact hyA
        · exact False.elim (hy heqx)
  have hS_card : S.card = r := by
    rw [Finset.card_image_of_injOn h_inj]
    exact h_sun.1
  have hS_sub : S ⊆ F := by
    intro Y hY
    rw [Finset.mem_image] at hY
    obtain ⟨B, hB, rfl⟩ := hY
    exact h_lift_in_F B hB
  refine ⟨S, hS_sub, C' ∪ {x}, hS_card, ?_⟩
  intro A hA B hB hAB
  rw [Finset.mem_image] at hA hB
  obtain ⟨A', hA', rfl⟩ := hA
  obtain ⟨B', hB', rfl⟩ := hB
  have hA'B' : A' ≠ B' := by
    rintro rfl
    exact hAB rfl
  have h_inter := h_sun.2 A' hA' B' hB' hA'B'
  dsimp [f]
  ext y
  simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_singleton]
  constructor
  · rintro ⟨hyA | hyA, hyB | hyB⟩
    · left
      have : y ∈ A' ∩ B' := Finset.mem_inter.mpr ⟨hyA, hyB⟩
      rwa [h_inter] at this
    · right; exact hyB
    · right; exact hyA
    · right; exact hyA
  · rintro (hyC | hyx)
    · have h_in : y ∈ A' ∩ B' := by rwa [h_inter]
      simp only [Finset.mem_inter] at h_in
      exact ⟨Or.inl h_in.1, Or.inl h_in.2⟩
    · subst hyx
      exact ⟨Or.inr rfl, Or.inr rfl⟩

/-- Base Case k = 1: Any family of singletons with cardinality > r - 1 contains an r-sunflower (with core ∅). -/
theorem sunflower_k_one (F : Finset (Finset α)) (r : ℕ)
    (h_card_sets : ∀ A ∈ F, A.card = 1)
    (hF : erdos_rado_bound 1 r < F.card) :
    HasSunflower F r := by
  have h_bound : erdos_rado_bound 1 r = r - 1 := by
    dsimp [erdos_rado_bound, fact]
    ring
  rw [h_bound] at hF
  have hr : r ≤ F.card := by omega
  obtain ⟨S, hS_sub, hS_card⟩ := Finset.exists_subset_card_eq hr
  refine ⟨S, hS_sub, ∅, hS_card, ?_⟩
  intro A hA B hB hAB
  have hA_F := hS_sub hA
  have hB_F := hS_sub hB
  have hA_card := h_card_sets A hA_F
  have hB_card := h_card_sets B hB_F
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hA_card
  obtain ⟨b, rfl⟩ := Finset.card_eq_one.mp hB_card
  have hab : a ≠ b := by
    rintro rfl
    exact hAB rfl
  ext x
  simp [hab]

/-- Inductive step: If the fiber of sets containing x (with x removed) contains an r-sunflower,
    then F contains an r-sunflower. -/
theorem sunflower_step (F : Finset (Finset α)) (x : α) (r : ℕ)
    (h_ind : HasSunflower ((F.filter (fun A => x ∈ A)).image (fun A => A \ {x})) r) :
    HasSunflower F r := by
  obtain ⟨S', hS'_sub, C', h_sun⟩ := h_ind
  have h_x_not : ∀ B ∈ S', x ∉ B := by
    intro B hB
    have hB_in := hS'_sub hB
    rw [Finset.mem_image] at hB_in
    obtain ⟨A, _, rfl⟩ := hB_in
    simp
  have h_lift_in : ∀ B ∈ S', B ∪ {x} ∈ F := by
    intro B hB
    have hB_in := hS'_sub hB
    rw [Finset.mem_image] at hB_in
    obtain ⟨A, hA, rfl⟩ := hB_in
    rw [Finset.mem_filter] at hA
    have hA_sub : A \ {x} ∪ {x} = A := by
      ext y
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton]
      constructor
      · rintro (⟨hyA, _⟩ | rfl)
        · exact hyA
        · exact hA.2
      · intro hyA
        by_cases hyx : y = x
        · right; exact hyx
        · left; exact ⟨hyA, hyx⟩
    rw [hA_sub]
    exact hA.1
  exact sunflower_lift F x r S' C' h_sun h_x_not h_lift_in

#print axioms sunflower_of_pairwise_disjoint
#print axioms sunflower_lift
#print axioms sunflower_k_one
#print axioms sunflower_step

end SunflowerLemma
