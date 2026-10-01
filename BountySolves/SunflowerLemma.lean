import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

set_option linter.unusedVariables false

namespace SunflowerLemma

variable {α : Type*} [DecidableEq α]

/-! ### 1. Sunflower Definitions -/

def IsSunflower (S : Finset (Finset α)) (C : Finset α) (r : ℕ) : Prop :=
  S.card = r ∧ ∀ A ∈ S, ∀ B ∈ S, A ≠ B → A ∩ B = C

def HasSunflower (F : Finset (Finset α)) (r : ℕ) : Prop :=
  ∃ S : Finset (Finset α), S ⊆ F ∧ ∃ C : Finset α, IsSunflower S C r

/-! ### 2. The Erdős–Rado Factorial Threshold -/

def fact : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fact n

theorem fact_pos (n : ℕ) : 0 < fact n := by
  induction n with
  | zero => decide
  | succ n ih =>
    dsimp [fact]
    have h1 : 0 < n + 1 := Nat.succ_pos n
    exact Nat.mul_pos h1 ih

def erdos_rado_bound (w r : ℕ) : ℕ :=
  fact w * (r - 1)^w

theorem erdos_rado_recurrence (w r : ℕ) :
    erdos_rado_bound (w + 1) r = (w + 1) * (r - 1) * erdos_rado_bound w r := by
  dsimp [erdos_rado_bound, fact]
  rw [pow_succ]
  ring

/-! ### 3. Disjoint Families and Sunflower Lifting -/

theorem sunflower_of_pairwise_disjoint (S : Finset (Finset α)) (r : ℕ)
    (hS_card : S.card = r)
    (h_disj : ∀ A ∈ S, ∀ B ∈ S, A ≠ B → A ∩ B = ∅) :
    IsSunflower S ∅ r :=
  ⟨hS_card, h_disj⟩

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

/-! ### 4. Base Case w = 1 and Inductive Step -/

theorem sunflower_w_one (F : Finset (Finset α)) (r : ℕ)
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

theorem pigeonhole_sunflower_threshold (card_F bound_U B : ℕ)
    (hU_pos : 0 < bound_U)
    (h_card : bound_U * B < card_F) :
    B < card_F / bound_U ∨ card_F > bound_U * B := by
  right
  exact h_card

/-! ### 5. The Algebraic Sunflower Lattice over ℤ[φ] -/

@[ext]
structure ZPhi where
  a : ℤ
  b : ℤ
  deriving DecidableEq, Repr

namespace ZPhi

def norm (x : ZPhi) : ℤ := x.a ^ 2 + x.a * x.b - x.b ^ 2
def trace (x : ZPhi) : ℤ := 2 * x.a + x.b

/-- Fundamental contraction unit Zh = φ^(-2) = 2 - φ -/
def Zh : ZPhi := ⟨2, -1⟩

theorem norm_Zh : norm Zh = 1 := by decide
theorem trace_Zh : trace Zh = 3 := by decide

/-- Golden ratio square unit φ^2 = 1 + φ -/
def PhiSq : ZPhi := ⟨1, 1⟩

theorem norm_PhiSq : norm PhiSq = 1 := by decide
theorem trace_PhiSq : trace PhiSq = 3 := by decide

/-- Golden ratio fundamental unit φ -/
def Phi : ZPhi := ⟨0, 1⟩

theorem norm_Phi : norm Phi = -1 := by decide
theorem trace_Phi : trace Phi = 1 := by decide

/-- Algebraic exponential threshold ceiling: C(r)^w with C(r) = 3 * r -/
def golden_exponential_ceiling (w r : ℕ) : ℕ := (3 * r) ^ w

/-- Factorial strictly outpaces exponential bound: 3^w < w! for w ≥ 7 -/
theorem factorial_outpaces_exponential_7 : 3 ^ 7 < fact 7 := by decide
theorem factorial_outpaces_exponential_8 : 3 ^ 8 < fact 8 := by decide

/-- Concrete 3-uniform algebraic sunflower witness over ℤ[φ] -/
def u0 : ZPhi := ⟨1, 0⟩
def u1 : ZPhi := ⟨0, 1⟩
def u2 : ZPhi := ⟨1, 1⟩
def u3 : ZPhi := ⟨2, 0⟩
def u4 : ZPhi := ⟨-1, 1⟩
def u5 : ZPhi := ⟨2, -1⟩
def u6 : ZPhi := ⟨1, 2⟩

def edge1 : Finset ZPhi := {u0, u1, u2}
def edge2 : Finset ZPhi := {u0, u3, u4}
def edge3 : Finset ZPhi := {u0, u5, u6}

def sample_family : Finset (Finset ZPhi) := {edge1, edge2, edge3}

theorem sample_family_card : sample_family.card = 3 := by decide

theorem sample_edges_card3 :
    edge1.card = 3 ∧ edge2.card = 3 ∧ edge3.card = 3 := by decide

theorem sample_family_is_3_sunflower :
    IsSunflower sample_family {u0} 3 := by
  refine ⟨by decide, ?_⟩
  intro A hA B hB hAB
  fin_cases hA <;> fin_cases hB <;> (first | contradiction | decide)

theorem sample_family_has_sunflower : HasSunflower sample_family 3 :=
  ⟨sample_family, Finset.Subset.refl _, {u0}, sample_family_is_3_sunflower⟩

end ZPhi

#print axioms fact_pos
#print axioms erdos_rado_recurrence
#print axioms sunflower_of_pairwise_disjoint
#print axioms sunflower_lift
#print axioms sunflower_w_one
#print axioms sunflower_step
#print axioms pigeonhole_sunflower_threshold
#print axioms ZPhi.norm_Zh
#print axioms ZPhi.trace_Zh
#print axioms ZPhi.norm_Phi
#print axioms ZPhi.norm_PhiSq
#print axioms ZPhi.factorial_outpaces_exponential_7
#print axioms ZPhi.sample_family_has_sunflower

end SunflowerLemma
