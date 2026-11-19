import Mathlib

/-!
# JSP-000490 (Erdős Problem #603): Unconditional Disproof of Any Uniform Coloring Bound

- **Catalog ID:** JSP-000490 (`catalog-0401-0500.md`)
- **Erdős Problem:** #603 (posed by Péter Komjáth)
- **Question:** Let `(A_i)` be a family of countably infinite sets such that `|A_i ∩ A_j| ≠ 2`
  for all `i ≠ j`. Find the smallest cardinal `C` such that `⋃ A_i` can always be colored with
  at most `C` colors so that no `A_i` is monochromatic.
- **Answer:** No such cardinal bound exists. For every cardinal `κ` (and every color type
  `C : Type u`), there exists a ground set `X : Type u` and a family `ℱ : Set (Set X)` of
  countably infinite subsets covering `X` (`⋃₀ ℱ = Set.univ`) such that:
  1. Every `A ∈ ℱ` is countably infinite (`#A = ℵ₀`),
  2. Every pair of sets `A, B ∈ ℱ` satisfies `#(A ∩ B) ≠ 2` (in fact `|A ∩ B|` is a triangular
     number `n(n-1)/2` or `ℵ₀`, hence never `2`),
  3. Every coloring `f : X → C` admits a monochromatic member `A ∈ ℱ`.

## Proof Method
Given a color type `C : Type u`, let `μ = max ℵ₀ #C` and take a vertex set `V : Type u` with
`2 ^ μ < #V` (explicitly `V := Set (Set (C ⊕ ULift.{u} ℕ))`, so `#V = 2 ^ (2 ^ μ) > 2 ^ μ`).
Let `X := Pair V = { s : Finset V // s.card = 2 }` be the set of unordered pairs of distinct
elements of `V`, and let `ℱ := { pairSet S | S : Set V, #S = ℵ₀ }` where
`pairSet S := { e : Pair V | ∀ x ∈ e.1, x ∈ S }`.
- Pairwise intersections satisfy `pairSet S₁ ∩ pairSet S₂ = pairSet (S₁ ∩ S₂)`. Any two
  distinct pairs in `pairSet T` span at least 3 elements of `T`, generating at least 3 pairs
  in `pairSet T`, so `#(pairSet T) ≠ 2`.
- By a self-contained proof of the Erdős–Rado partition theorem (`2 ^ μ < #V → V → (ℵ₀)^2_C`)
  via transfinite recursion along `I := (Cardinal.ord (Order.succ μ)).toType`, every coloring
  `f : Pair V → C` admits a countably infinite homogeneous subset `S ⊆ V`, yielding a
  monochromatic `pairSet S ∈ ℱ`.

## Formal Guarantees
- Unconditional, zero `sorry`, zero `admit`, zero custom axioms
  (`[propext, Classical.choice, Quot.sound]`), zero approximations.
-/

namespace JSP_000490

open Cardinal Ordinal Set

universe u

section PairCombinatorics

/-- Unordered pairs of distinct elements of `V`. -/
abbrev Pair (V : Type u) : Type u := { s : Finset V // s.card = 2 }

/-- Construct an unordered pair from two distinct elements. -/
def mkPair {V : Type u} [DecidableEq V] {x y : V} (h : x ≠ y) : Pair V :=
  ⟨{x, y}, Finset.card_pair h⟩

lemma mkPair_comm {V : Type u} [DecidableEq V] {x y : V} (h : x ≠ y) :
    mkPair h = mkPair h.symm := by
  apply Subtype.ext
  exact Finset.pair_comm x y

/-- The set of all unordered pairs contained in `S`. -/
def pairSet {V : Type u} (S : Set V) : Set (Pair V) :=
  { e | ∀ x ∈ e.1, x ∈ S }

lemma mem_pairSet_mkPair {V : Type u} [DecidableEq V] {S : Set V} {x y : V}
    (h : x ≠ y) (hx : x ∈ S) (hy : y ∈ S) : mkPair h ∈ pairSet S := by
  intro z hz
  simp only [mkPair, Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl
  · exact hx
  · exact hy

lemma pairSet_inter {V : Type u} (S₁ S₂ : Set V) :
    pairSet S₁ ∩ pairSet S₂ = pairSet (S₁ ∩ S₂) := by
  ext e
  simp only [Set.mem_inter_iff, pairSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩ x hx
    exact ⟨h1 x hx, h2 x hx⟩
  · intro h
    exact ⟨fun x hx => (h x hx).1, fun x hx => (h x hx).2⟩

/-- For any set `T`, the set of unordered pairs `pairSet T` never has cardinality `2`:
two distinct pairs span at least `3` elements of `T`, which determine at least `3` pairs. -/
theorem pairSet_card_ne_two {V : Type u} (T : Set V) :
    Cardinal.mk (pairSet T) ≠ 2 := by
  classical
  intro hcard
  have h2 : Cardinal.mk (ULift.{u} (Fin 2)) = 2 := by simp
  have heq : Cardinal.mk (pairSet T) = Cardinal.mk (ULift.{u} (Fin 2)) := by
    rw [hcard, h2]
  obtain ⟨e⟩ := Cardinal.eq.mp heq
  let p₀ : pairSet T := e.symm ⟨0⟩
  let p₁ : pairSet T := e.symm ⟨1⟩
  have hp_ne : p₀ ≠ p₁ := by
    intro h
    have h01 : (⟨0⟩ : ULift.{u} (Fin 2)) = ⟨1⟩ := e.symm.injective h
    exact absurd (congrArg ULift.down h01) (by decide)
  have hs_ne : p₀.1.1 ≠ p₁.1.1 := by
    intro h
    exact hp_ne (Subtype.ext (Subtype.ext h))
  have hunion_ge3 : 3 ≤ (p₀.1.1 ∪ p₁.1.1).card := by
    by_contra hlt
    have hle : (p₀.1.1 ∪ p₁.1.1).card ≤ 2 := by omega
    have h0eq : p₀.1.1 = p₀.1.1 ∪ p₁.1.1 :=
      Finset.eq_of_subset_of_card_le Finset.subset_union_left (by rw [p₀.1.2]; exact hle)
    have h1eq : p₁.1.1 = p₀.1.1 ∪ p₁.1.1 :=
      Finset.eq_of_subset_of_card_le Finset.subset_union_right (by rw [p₁.1.2]; exact hle)
    exact hs_ne (h0eq.trans h1eq.symm)
  obtain ⟨t, ht_sub, ht_card⟩ := Finset.exists_subset_card_eq hunion_ge3
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp ht_card
  have hmemT : ∀ a ∈ ({x, y, z} : Finset V), a ∈ T := by
    intro a ha
    have ha_u : a ∈ p₀.1.1 ∪ p₁.1.1 := ht_sub ha
    rw [Finset.mem_union] at ha_u
    rcases ha_u with ha0 | ha1
    · exact p₀.2 a ha0
    · exact p₁.2 a ha1
  have hxT : x ∈ T := hmemT x (by simp)
  have hyT : y ∈ T := hmemT y (by simp)
  have hzT : z ∈ T := hmemT z (by simp)
  let q₀ : pairSet T := ⟨mkPair hxy, mem_pairSet_mkPair hxy hxT hyT⟩
  let q₁ : pairSet T := ⟨mkPair hxz, mem_pairSet_mkPair hxz hxT hzT⟩
  let q₂ : pairSet T := ⟨mkPair hyz, mem_pairSet_mkPair hyz hyT hzT⟩
  let g : ULift.{u} (Fin 3) → pairSet T := fun k =>
    match k.down with
    | ⟨0, _⟩ => q₀
    | ⟨1, _⟩ => q₁
    | ⟨2, _⟩ => q₂
  have hg_inj : Function.Injective g := by
    rintro ⟨⟨a, ha⟩⟩ ⟨⟨b, hb⟩⟩ hab
    have hval : (g ⟨⟨a, ha⟩⟩).1.1 = (g ⟨⟨b, hb⟩⟩).1.1 := congrArg (fun p => p.1.1) hab
    interval_cases a <;> interval_cases b
    · rfl
    · simp only [g, q₀, q₁, mkPair] at hval
      have hy_mem : y ∈ ({x, z} : Finset V) := by rw [← hval]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy_mem
      rcases hy_mem with rfl | rfl
      · exact absurd rfl hxy
      · exact absurd rfl hyz
    · simp only [g, q₀, q₂, mkPair] at hval
      have hx_mem : x ∈ ({y, z} : Finset V) := by rw [← hval]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx_mem
      rcases hx_mem with rfl | rfl
      · exact absurd rfl hxy
      · exact absurd rfl hxz
    · simp only [g, q₀, q₁, mkPair] at hval
      have hz_mem : z ∈ ({x, y} : Finset V) := by rw [← hval]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz_mem
      rcases hz_mem with rfl | rfl
      · exact absurd rfl hxz
      · exact absurd rfl hyz
    · rfl
    · simp only [g, q₁, q₂, mkPair] at hval
      have hx_mem : x ∈ ({y, z} : Finset V) := by rw [← hval]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx_mem
      rcases hx_mem with rfl | rfl
      · exact absurd rfl hxy
      · exact absurd rfl hxz
    · simp only [g, q₀, q₂, mkPair] at hval
      have hz_mem : z ∈ ({x, y} : Finset V) := by rw [← hval]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz_mem
      rcases hz_mem with rfl | rfl
      · exact absurd rfl hxz
      · exact absurd rfl hyz
    · simp only [g, q₁, q₂, mkPair] at hval
      have hy_mem : y ∈ ({x, z} : Finset V) := by rw [← hval]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy_mem
      rcases hy_mem with rfl | rfl
      · exact absurd rfl hxy
      · exact absurd rfl hyz
    · rfl
  have hle3 : (3 : Cardinal.{u}) ≤ Cardinal.mk (pairSet T) := by
    have h3 : Cardinal.mk (ULift.{u} (Fin 3)) = 3 := by simp
    rw [← h3]
    exact Cardinal.mk_le_of_injective hg_inj
  rw [hcard] at hle3
  have hlt23 : (2 : Cardinal.{u}) < 3 := by norm_num
  exact not_le_of_gt hlt23 hle3

/-- If `S` is countably infinite, then `pairSet S` is countably infinite. -/
theorem pairSet_mk_aleph0 {V : Type u} {S : Set V} (hS : Cardinal.mk S = Cardinal.aleph0) :
    Cardinal.mk (pairSet S) = Cardinal.aleph0 := by
  classical
  apply le_antisymm
  · have hex : ∀ p : pairSet S, ∃ q : S × S, p.1.1 = {(q.1 : V), (q.2 : V)} := by
      intro p
      obtain ⟨x, y, _, hxy⟩ := Finset.card_eq_two.mp p.1.2
      have hx : x ∈ S := p.2 x (by rw [hxy]; simp)
      have hy : y ∈ S := p.2 y (by rw [hxy]; simp)
      exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), hxy⟩
    let g : pairSet S → S × S := fun p => (hex p).choose
    have hg_inj : Function.Injective g := by
      intro p₁ p₂ h
      have h1 := (hex p₁).choose_spec
      have h2 := (hex p₂).choose_spec
      apply Subtype.ext
      apply Subtype.ext
      rw [h1, h2]
      change ({((g p₁).1 : V), ((g p₁).2 : V)} : Finset V) = {((g p₂).1 : V), ((g p₂).2 : V)}
      rw [h]
    calc
      Cardinal.mk (pairSet S) ≤ Cardinal.mk (S × S) := Cardinal.mk_le_of_injective hg_inj
      _ = Cardinal.mk S * Cardinal.mk S := by simp
      _ = Cardinal.aleph0 * Cardinal.aleph0 := by rw [hS]
      _ = Cardinal.aleph0 := Cardinal.mul_eq_self le_rfl
  · have hN : Cardinal.mk (ULift.{u} ℕ) = Cardinal.aleph0 := by simp
    obtain ⟨e⟩ := Cardinal.eq.mp (hN.trans hS.symm)
    have hne : ∀ n : ℕ, (e ⟨0⟩ : V) ≠ (e ⟨n + 1⟩ : V) := by
      intro n h
      have heq : (⟨0⟩ : ULift.{u} ℕ) = ⟨n + 1⟩ := e.injective (Subtype.ext h)
      exact Nat.succ_ne_zero n (congrArg ULift.down heq).symm
    let ι : ULift.{u} ℕ → pairSet S := fun n =>
      ⟨mkPair (hne n.down), mem_pairSet_mkPair (hne n.down) (e ⟨0⟩).2 (e ⟨n.down + 1⟩).2⟩
    have hι_inj : Function.Injective ι := by
      rintro ⟨m⟩ ⟨n⟩ hmn
      have hval : ({(e ⟨0⟩ : V), (e ⟨m + 1⟩ : V)} : Finset V) =
          {(e ⟨0⟩ : V), (e ⟨n + 1⟩ : V)} := congrArg (fun p => p.1.1) hmn
      have hm_mem : (e ⟨m + 1⟩ : V) ∈ ({(e ⟨0⟩ : V), (e ⟨n + 1⟩ : V)} : Finset V) := by
        rw [← hval]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm_mem
      rcases hm_mem with h0 | h1
      · exact absurd h0.symm (hne m)
      · have heq : (⟨m + 1⟩ : ULift.{u} ℕ) = ⟨n + 1⟩ := e.injective (Subtype.ext h1)
        exact congrArg ULift.up (Nat.succ.inj (congrArg ULift.down heq))
    rw [← hN]
    exact Cardinal.mk_le_of_injective hι_inj

end PairCombinatorics

section ErdosRado

open Classical in
/-- Transfinite Erdős–Rado tree node selection indexed by a well-ordered type `I`. -/
noncomputable def erdosRadoNode {V C : Type u} [DecidableEq V]
    {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (f : Pair V → C) : ∀ (i : I), ({ j : I // j < i } → C) → Option V :=
  WellFounded.fix wellFounded_lt fun i rec σ =>
    let U : Set V := { x | ∀ (j : I) (hj : j < i),
      ∃ w : V, rec j hj (fun k => σ ⟨k.1, lt_trans k.2 hj⟩) = some w ∧
        ∃ hne : w ≠ x, f (mkPair hne) = σ ⟨j, hj⟩ }
    if h : U.Nonempty then some h.choose else none

open Classical in
lemma erdosRadoNode_eq {V C : Type u} [DecidableEq V]
    {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (f : Pair V → C) (i : I) (σ : { j : I // j < i } → C) :
    erdosRadoNode f i σ =
      let U : Set V := { x | ∀ (j : I) (hj : j < i),
        ∃ w : V, erdosRadoNode f j (fun k => σ ⟨k.1, lt_trans k.2 hj⟩) = some w ∧
          ∃ hne : w ≠ x, f (mkPair hne) = σ ⟨j, hj⟩ }
      if h : U.Nonempty then some h.choose else none := by
  unfold erdosRadoNode
  rw [WellFounded.fix_eq]

/-- Set of all vertices placed anywhere in the Erdős–Rado tree. -/
def pickedSet {V C : Type u} [DecidableEq V]
    {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (f : Pair V → C) : Set V :=
  { w | ∃ (i : I) (σ : { j : I // j < i } → C), erdosRadoNode f i σ = some w }

/-- Color trace along the branch determined by an unpicked vertex `y`. -/
noncomputable def branchColor {V C : Type u} [DecidableEq V] [Nonempty C]
    {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (f : Pair V → C) (y : V) : I → C :=
  WellFounded.fix wellFounded_lt fun i rec =>
    let σ : { j : I // j < i } → C := fun j => rec j.1 j.2
    match erdosRadoNode f i σ with
    | some w => if hne : w ≠ y then f (mkPair hne) else Classical.arbitrary C
    | none => Classical.arbitrary C

lemma branchColor_eq {V C : Type u} [DecidableEq V] [Nonempty C]
    {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (f : Pair V → C) (y : V) (i : I) :
    branchColor f y i =
      match erdosRadoNode f i (fun j => branchColor f y j.1) with
      | some w => if hne : w ≠ y then f (mkPair hne) else Classical.arbitrary C
      | none => Classical.arbitrary C := by
  unfold branchColor
  rw [WellFounded.fix_eq]

/-- Every node along an unpicked vertex `y`'s branch is inhabited and agrees with `y`'s colors. -/
lemma branchColor_spec {V C : Type u} [DecidableEq V] [Nonempty C]
    {I : Type u} [LinearOrder I] [WellFoundedLT I]
    (f : Pair V → C) (y : V) (hy : y ∉ pickedSet (I := I) f) :
    ∀ i : I, ∃ w : V,
      erdosRadoNode f i (fun j => branchColor f y j.1) = some w ∧
      (∀ (j : I), j < i →
        ∃ u : V, erdosRadoNode f j (fun k => branchColor f y k.1) = some u ∧
          ∃ hne : u ≠ w, f (mkPair hne) = branchColor f y j) ∧
      ∃ hne : w ≠ y, f (mkPair hne) = branchColor f y i := by
  intro i
  have hwf : WellFounded ((· < ·) : I → I → Prop) := wellFounded_lt
  induction i using hwf.induction with
  | h i ih =>
    let σ : { j : I // j < i } → C := fun j => branchColor f y j.1
    let U : Set V := { x | ∀ (j : I) (hj : j < i),
      ∃ u : V, erdosRadoNode f j (fun k => σ ⟨k.1, lt_trans k.2 hj⟩) = some u ∧
        ∃ hne : u ≠ x, f (mkPair hne) = σ ⟨j, hj⟩ }
    have hyU : y ∈ U := by
      intro j hj
      obtain ⟨u, hu_eq, _, hne, hcol⟩ := ih j hj
      exact ⟨u, hu_eq, hne, hcol⟩
    have hU : U.Nonempty := ⟨y, hyU⟩
    let w : V := hU.choose
    have hwU : w ∈ U := hU.choose_spec
    have hnode : erdosRadoNode f i σ = some w := by
      classical
      rw [erdosRadoNode_eq]
      change (if h : U.Nonempty then some h.choose else none) = some w
      simp [hU, w]
    have hw_ne : w ≠ y := by
      intro hwy
      apply hy
      exact ⟨i, σ, hwy ▸ hnode⟩
    have hbc : branchColor f y i = f (mkPair hw_ne) := by
      rw [branchColor_eq]
      change (match erdosRadoNode f i σ with
        | some w' => if hne : w' ≠ y then f (mkPair hne) else Classical.arbitrary C
        | none => Classical.arbitrary C) = f (mkPair hw_ne)
      rw [hnode]
      simp [hw_ne]
    exact ⟨w, hnode, hwU, hw_ne, hbc.symm⟩

/-- Cardinality bound on the Erdős–Rado tree of height `(Order.succ μ).ord`. -/
lemma card_pickedSet_le {V C : Type u} [DecidableEq V]
    (f : Pair V → C) :
    let μ : Cardinal.{u} := max Cardinal.aleph0 (Cardinal.mk C)
    let I : Type u := Ordinal.ToType (Cardinal.ord (Order.succ μ))
    Cardinal.mk (pickedSet (I := I) f) ≤ (2 : Cardinal.{u}) ^ μ := by
  intro μ I
  have hμ_inf : Cardinal.aleph0 ≤ μ := le_max_left _ _
  have hC_le : Cardinal.mk C ≤ μ := le_max_right _ _
  have hμ_lt_pow : μ < (2 : Cardinal.{u}) ^ μ := Cardinal.cantor μ
  have hsucc_le : Order.succ μ ≤ (2 : Cardinal.{u}) ^ μ := Order.succ_le_of_lt hμ_lt_pow
  have hI_card : Cardinal.mk I = Order.succ μ := by
    dsimp [I]
    rw [Cardinal.mk_toType, Cardinal.card_ord]
  let g : pickedSet (I := I) f → (i : I) × ({ j : I // j < i } → C) := fun w =>
    ⟨w.2.choose, w.2.choose_spec.choose⟩
  have hg_inj : Function.Injective g := by
    intro w₁ w₂ h
    have h1 := w₁.2.choose_spec.choose_spec
    have h2 := w₂.2.choose_spec.choose_spec
    apply Subtype.ext
    have heq_node :
        erdosRadoNode f w₁.2.choose w₁.2.choose_spec.choose =
        erdosRadoNode f w₂.2.choose w₂.2.choose_spec.choose :=
      congrArg (fun p : (i : I) × ({ j : I // j < i } → C) => erdosRadoNode f p.1 p.2) h
    have heq_some : (some w₁.1 : Option V) = some w₂.1 := h1.symm.trans (heq_node.trans h2)
    exact Option.some.inj heq_some
  have hfiber : ∀ i : I, Cardinal.mk ({ j : I // j < i } → C) ≤ (2 : Cardinal.{u}) ^ μ := by
    intro i
    have hseg_lt : Cardinal.mk { j : I // j < i } < Order.succ μ := by
      have htype_lt : Ordinal.typein ((· < ·) : I → I → Prop) i <
          Cardinal.ord (Order.succ μ) :=
        Ordinal.typein_lt_self i
      have hcard_lt : (Ordinal.typein ((· < ·) : I → I → Prop) i).card < Order.succ μ :=
        Cardinal.lt_ord.mp htype_lt
      have hmk : Cardinal.mk { j : I // j < i } =
          (Ordinal.typein ((· < ·) : I → I → Prop) i).card := by
        simp
      rwa [hmk]
    have hseg_le : Cardinal.mk { j : I // j < i } ≤ μ := Order.le_of_lt_succ hseg_lt
    calc
      Cardinal.mk ({ j : I // j < i } → C) =
          (Cardinal.mk C) ^ (Cardinal.mk { j : I // j < i }) := by simp
      _ ≤ μ ^ (Cardinal.mk { j : I // j < i }) := Cardinal.power_le_power_right hC_le
      _ ≤ ((2 : Cardinal.{u}) ^ μ) ^ (Cardinal.mk { j : I // j < i }) :=
          Cardinal.power_le_power_right hμ_lt_pow.le
      _ = (2 : Cardinal.{u}) ^ (μ * Cardinal.mk { j : I // j < i }) := Cardinal.power_mul.symm
      _ ≤ (2 : Cardinal.{u}) ^ (μ * μ) := by
          apply Cardinal.power_le_power_left (by norm_num : (2 : Cardinal.{u}) ≠ 0)
          exact mul_le_mul' le_rfl hseg_le
      _ = (2 : Cardinal.{u}) ^ μ := by
          rw [Cardinal.mul_eq_self hμ_inf]
  calc
    Cardinal.mk (pickedSet (I := I) f)
        ≤ Cardinal.mk ((i : I) × ({ j : I // j < i } → C)) := Cardinal.mk_le_of_injective hg_inj
    _ = Cardinal.sum (fun i : I => Cardinal.mk ({ j : I // j < i } → C)) := Cardinal.mk_sigma _
    _ ≤ Cardinal.sum (fun _ : I => (2 : Cardinal.{u}) ^ μ) := Cardinal.sum_le_sum _ _ hfiber
    _ = Cardinal.mk I * (2 : Cardinal.{u}) ^ μ := by simp
    _ = Order.succ μ * (2 : Cardinal.{u}) ^ μ := by rw [hI_card]
    _ ≤ (2 : Cardinal.{u}) ^ μ * (2 : Cardinal.{u}) ^ μ := mul_le_mul' hsucc_le le_rfl
    _ = (2 : Cardinal.{u}) ^ μ := by
        apply Cardinal.mul_eq_self
        exact le_trans hμ_inf hμ_lt_pow.le

/-- Self-contained Erdős–Rado partition theorem for countable homogeneous sets:
whenever `2 ^ (max ℵ₀ #C) < #V`, every coloring `Pair V → C` has a countably infinite
monochromatic clique `pairSet S`. -/
theorem erdos_rado_countable {C V : Type u}
    (hV : (2 : Cardinal.{u}) ^ (max Cardinal.aleph0 (Cardinal.mk C)) < Cardinal.mk V)
    (f : Pair V → C) :
    ∃ S : Set V, Cardinal.mk S = Cardinal.aleph0 ∧
      ∃ c : C, ∀ e ∈ pairSet S, f e = c := by
  classical
  let μ : Cardinal.{u} := max Cardinal.aleph0 (Cardinal.mk C)
  have hμ_inf : Cardinal.aleph0 ≤ μ := le_max_left _ _
  have hC_le : Cardinal.mk C ≤ μ := le_max_right _ _
  have hV_inf : Cardinal.aleph0 < Cardinal.mk V :=
    lt_of_le_of_lt (le_trans hμ_inf (Cardinal.cantor μ).le) hV
  have hV_gt1 : (1 : Cardinal.{u}) < Cardinal.mk V :=
    lt_trans (by exact_mod_cast (Cardinal.one_lt_aleph0)) hV_inf
  have hC_nonempty : Nonempty C := by
    have hV_nontriv : Nontrivial V := Cardinal.one_lt_iff_nontrivial.mp hV_gt1
    obtain ⟨x, y, hxy⟩ := hV_nontriv.exists_pair_ne
    exact ⟨f (mkPair hxy)⟩
  let I : Type u := Ordinal.ToType (Cardinal.ord (Order.succ μ))
  have hpicked_lt : Cardinal.mk (pickedSet (I := I) f) < Cardinal.mk V :=
    lt_of_le_of_lt (card_pickedSet_le f) hV
  have hex_unpicked : ∃ y : V, y ∉ pickedSet (I := I) f := by
    by_contra hall
    push Not at hall
    have huniv : pickedSet (I := I) f = Set.univ := Set.eq_univ_of_forall hall
    rw [huniv, Cardinal.mk_univ] at hpicked_lt
    exact lt_irrefl _ hpicked_lt
  obtain ⟨y, hy⟩ := hex_unpicked
  have hspec := branchColor_spec (I := I) f y hy
  let w : I → V := fun i => (hspec i).choose
  have hw_node : ∀ i : I, erdosRadoNode f i (fun j => branchColor f y j.1) = some (w i) :=
    fun i => (hspec i).choose_spec.1
  have hw_hom : ∀ {j i : I}, j < i →
      ∃ hne : w j ≠ w i, f (mkPair hne) = branchColor f y j := by
    intro j i hji
    obtain ⟨u, hu_eq, hne, hcol⟩ := (hspec i).choose_spec.2.1 j hji
    have huw : u = w j := Option.some.inj (hu_eq.symm.trans (hw_node j))
    subst huw
    exact ⟨hne, hcol⟩
  have hw_inj : Function.Injective w := by
    intro i j hij
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · obtain ⟨hne, _⟩ := hw_hom hlt
      exact absurd hij hne
    · rfl
    · obtain ⟨hne, _⟩ := hw_hom hgt
      exact absurd hij.symm hne
  -- Pigeonhole on `branchColor f y : I → C`: since `#I = Order.succ μ > μ ≥ #C * ℵ₀`,
  -- some color fiber is infinite.
  have hex_inf_fiber : ∃ c : C, Set.Infinite { i : I | branchColor f y i = c } := by
    by_contra hfin
    push Not at hfin
    have hle_aleph0 : ∀ c : C, Cardinal.mk { i : I | branchColor f y i = c } ≤ Cardinal.aleph0 := by
      intro c
      have hfc : ({ i : I | branchColor f y i = c }).Finite := hfin c
      have : Finite { i : I | branchColor f y i = c } := hfc.to_subtype
      exact (Cardinal.lt_aleph0_of_finite _).le
    let φ : I → (c : C) × { i : I | branchColor f y i = c } :=
      fun i => ⟨branchColor f y i, ⟨i, rfl⟩⟩
    have hφ_inj : Function.Injective φ := by
      intro i₁ i₂ h
      have h2 := congrArg (fun p => p.2.1) h
      exact h2
    have hI_card : Cardinal.mk I = Order.succ μ := by
      dsimp [I]
      rw [Cardinal.mk_toType, Cardinal.card_ord]
    have hI_le : Cardinal.mk I ≤ μ := by
      calc
        Cardinal.mk I ≤ Cardinal.mk ((c : C) × { i : I | branchColor f y i = c }) :=
            Cardinal.mk_le_of_injective hφ_inj
        _ = Cardinal.sum (fun c : C => Cardinal.mk { i : I | branchColor f y i = c }) :=
            Cardinal.mk_sigma _
        _ ≤ Cardinal.sum (fun _ : C => Cardinal.aleph0) := Cardinal.sum_le_sum _ _ hle_aleph0
        _ = Cardinal.mk C * Cardinal.aleph0 := by simp
        _ ≤ μ * μ := mul_le_mul' hC_le hμ_inf
        _ = μ := Cardinal.mul_eq_self hμ_inf
    rw [hI_card] at hI_le
    exact not_le_of_gt (Order.lt_succ μ) hI_le
  obtain ⟨c, hc_inf⟩ := hex_inf_fiber
  have : Infinite { i : I | branchColor f y i = c } := hc_inf.to_subtype
  let emb : ℕ ↪ { i : I | branchColor f y i = c } := Infinite.natEmbedding _
  let g : ULift.{u} ℕ → V := fun n => w (emb n.down).1
  have hg_inj : Function.Injective g := by
    rintro ⟨m⟩ ⟨n⟩ hmn
    exact congrArg ULift.up (emb.injective (Subtype.ext (hw_inj hmn)))
  let S : Set V := Set.range g
  have hS_card : Cardinal.mk S = Cardinal.aleph0 := by
    have heq : Cardinal.mk S = Cardinal.mk (ULift.{u} ℕ) :=
      Cardinal.mk_range_eq g hg_inj
    rw [heq]
    simp
  refine ⟨S, hS_card, c, ?_⟩
  intro e he
  obtain ⟨a, b, hab, heq_ab⟩ := Finset.card_eq_two.mp e.2
  have ha : a ∈ S := he a (by rw [heq_ab]; simp)
  have hb : b ∈ S := he b (by rw [heq_ab]; simp)
  obtain ⟨m, rfl⟩ := ha
  obtain ⟨n, rfl⟩ := hb
  have he_eq : e = mkPair hab := Subtype.ext heq_ab
  rw [he_eq]
  have him_ne : (emb m.down).1 ≠ (emb n.down).1 := fun h => hab (by simp [g, h])
  rcases lt_trichotomy (emb m.down).1 (emb n.down).1 with hlt | heq_i | hgt
  · obtain ⟨hne, hcol⟩ := hw_hom hlt
    have : mkPair hab = mkPair hne := rfl
    rw [this, hcol]
    exact (emb m.down).2
  · exact absurd heq_i him_ne
  · obtain ⟨hne, hcol⟩ := hw_hom hgt
    rw [mkPair_comm hab]
    have : mkPair hab.symm = mkPair hne := rfl
    rw [this, hcol]
    exact (emb n.down).2

end ErdosRado

section MainTheorems

/-- Ground set `Pair V` for color type `C`, built inside the same universe `u`. -/
abbrev CounterexampleVertex (C : Type u) : Type u :=
  Set (Set (C ⊕ ULift.{u} ℕ))

/-- Ground set of unordered pairs for the counterexample family. -/
abbrev CounterexampleGround (C : Type u) : Type u :=
  Pair (CounterexampleVertex C)

/-- The counterexample family of countably infinite subsets of `CounterexampleGround C`. -/
def counterexampleFamily (C : Type u) : Set (Set (CounterexampleGround C)) :=
  { A | ∃ S : Set (CounterexampleVertex C), Cardinal.mk S = Cardinal.aleph0 ∧ A = pairSet S }

lemma counterexampleVertex_card_gt (C : Type u) :
    (2 : Cardinal.{u}) ^ (max Cardinal.aleph0 (Cardinal.mk C)) <
      Cardinal.mk (CounterexampleVertex C) := by
  let μ : Cardinal.{u} := max Cardinal.aleph0 (Cardinal.mk C)
  have hsum : Cardinal.mk (C ⊕ ULift.{u} ℕ) = μ := by
    simp only [Cardinal.mk_sum, Cardinal.mk_uLift, Cardinal.mk_nat, Cardinal.lift_id,
      Cardinal.lift_aleph0]
    rw [Cardinal.add_eq_max' le_rfl, max_comm]
  have hset1 : Cardinal.mk (Set (C ⊕ ULift.{u} ℕ)) = (2 : Cardinal.{u}) ^ μ := by
    rw [Cardinal.mk_set, hsum]
  have hset2 : Cardinal.mk (CounterexampleVertex C) = (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ μ) := by
    dsimp [CounterexampleVertex]
    rw [Cardinal.mk_set, hset1]
  rw [hset2]
  exact Cardinal.cantor ((2 : Cardinal.{u}) ^ μ)

/-- Every member of `counterexampleFamily C` is countably infinite. -/
theorem counterexampleFamily_countable_infinite (C : Type u) :
    ∀ A ∈ counterexampleFamily C, Cardinal.mk A = Cardinal.aleph0 := by
  rintro A ⟨S, hS, rfl⟩
  exact pairSet_mk_aleph0 hS

/-- No two members of `counterexampleFamily C` intersect in exactly `2` elements. -/
theorem counterexampleFamily_inter_ne_two (C : Type u) :
    ∀ A ∈ counterexampleFamily C, ∀ B ∈ counterexampleFamily C,
      A ≠ B → Cardinal.mk (A ∩ B : Set (CounterexampleGround C)) ≠ 2 := by
  rintro A ⟨S₁, _, rfl⟩ B ⟨S₂, _, rfl⟩ _
  rw [pairSet_inter]
  exact pairSet_card_ne_two (S₁ ∩ S₂)

/-- The union of `counterexampleFamily C` is the entire ground set `CounterexampleGround C`. -/
theorem counterexampleFamily_sUnion_eq_univ (C : Type u) :
    ⋃₀ counterexampleFamily C = Set.univ := by
  classical
  ext e
  simp only [Set.mem_sUnion, Set.mem_univ, iff_true]
  have hV_gt := counterexampleVertex_card_gt C
  have hV_inf : Cardinal.aleph0 ≤ Cardinal.mk (CounterexampleVertex C) := by
    have hμ : Cardinal.aleph0 ≤ max Cardinal.aleph0 (Cardinal.mk C) := le_max_left _ _
    exact le_trans (le_trans hμ (Cardinal.cantor _).le) hV_gt.le
  have : Infinite (CounterexampleVertex C) := Cardinal.infinite_iff.mpr hV_inf
  let emb : ULift.{u} ℕ ↪ CounterexampleVertex C :=
    ⟨fun n => Infinite.natEmbedding _ n.down,
     fun a b h => congrArg ULift.up ((Infinite.natEmbedding _).injective h)⟩
  let S : Set (CounterexampleVertex C) := (e.1 : Set (CounterexampleVertex C)) ∪ Set.range emb
  have hrange : Cardinal.mk (Set.range emb) = Cardinal.aleph0 := by
    rw [Cardinal.mk_range_eq emb emb.injective]
    simp
  have hS_card : Cardinal.mk S = Cardinal.aleph0 := by
    apply le_antisymm
    · calc
        Cardinal.mk S ≤ Cardinal.mk (e.1 : Set (CounterexampleVertex C)) +
            Cardinal.mk (Set.range emb) := Cardinal.mk_union_le _ _
        _ ≤ Cardinal.aleph0 + Cardinal.aleph0 := by
            apply add_le_add
            · exact (Cardinal.lt_aleph0_of_finite _).le
            · rw [hrange]
        _ = Cardinal.aleph0 := Cardinal.add_eq_self le_rfl
    · calc
        Cardinal.aleph0 = Cardinal.mk (Set.range emb) := hrange.symm
        _ ≤ Cardinal.mk S := Cardinal.mk_le_mk_of_subset Set.subset_union_right
  refine ⟨pairSet S, ⟨S, hS_card, rfl⟩, ?_⟩
  intro x hx
  exact Or.inl hx

/-- Every `C`-coloring of `CounterexampleGround C` admits a monochromatic member of
`counterexampleFamily C`. -/
theorem counterexampleFamily_monochromatic (C : Type u) (f : CounterexampleGround C → C) :
    ∃ A ∈ counterexampleFamily C, ∃ c : C, ∀ x ∈ A, f x = c := by
  obtain ⟨S, hS, c, hc⟩ := erdos_rado_countable (counterexampleVertex_card_gt C) f
  exact ⟨pairSet S, ⟨S, hS, rfl⟩, c, hc⟩

/-- Unconditional resolution of JSP-000490 (Erdős Problem #603):
for every color type `C : Type u`, there is a ground set `X : Type u` and a family `ℱ` of
countably infinite subsets covering `X` whose pairwise intersections never have cardinality `2`,
such that every `C`-coloring of `X` has a monochromatic member in `ℱ`. -/
theorem jsp_000490_for_every_color_type (C : Type u) :
    ∃ (X : Type u) (ℱ : Set (Set X)),
      ⋃₀ ℱ = Set.univ ∧
      (∀ A ∈ ℱ, Cardinal.mk A = Cardinal.aleph0) ∧
      (∀ A ∈ ℱ, ∀ B ∈ ℱ, A ≠ B → Cardinal.mk (A ∩ B : Set X) ≠ 2) ∧
      (∀ f : X → C, ∃ A ∈ ℱ, ∃ c : C, ∀ x ∈ A, f x = c) :=
  ⟨CounterexampleGround C, counterexampleFamily C,
    counterexampleFamily_sUnion_eq_univ C,
    counterexampleFamily_countable_infinite C,
    counterexampleFamily_inter_ne_two C,
    counterexampleFamily_monochromatic C⟩

/-- Cardinal-bound negation form of JSP-000490 (Erdős Problem #603):
there is no cardinal `κ` such that every family `ℱ` of countably infinite sets with
`|A ∩ B| ≠ 2` for `A ≠ B` admits a coloring of `⋃₀ ℱ` with at most `κ` colors avoiding
monochromatic members of `ℱ`. -/
theorem jsp_000490_no_uniform_cardinal_bound :
    ¬ ∃ κ : Cardinal.{u},
        ∀ (X : Type u) (ℱ : Set (Set X)),
          (∀ A ∈ ℱ, Cardinal.mk A = Cardinal.aleph0) →
          (∀ A ∈ ℱ, ∀ B ∈ ℱ, A ≠ B → Cardinal.mk (A ∩ B : Set X) ≠ 2) →
          ∃ (C : Type u) (f : (⋃₀ ℱ : Set X) → C),
            Cardinal.mk C ≤ κ ∧
            ∀ (A : Set X) (hA : A ∈ ℱ),
              ¬ ∃ c : C, ∀ (x : X) (hx : x ∈ A),
                f ⟨x, Set.mem_sUnion_of_mem hx hA⟩ = c := by
  rintro ⟨κ, hκ⟩
  let K : Type u := κ.out
  have hK : Cardinal.mk K = κ := Cardinal.mk_out κ
  obtain ⟨X, ℱ, huniv, hcount, hinter, hmono⟩ := jsp_000490_for_every_color_type K
  obtain ⟨C, f, hC_le, hno_mono⟩ := hκ X ℱ hcount hinter
  rw [← hK] at hC_le
  obtain ⟨emb⟩ := (Cardinal.le_def C K).mp hC_le
  let g : X → K := fun x => emb (f ⟨x, by rw [huniv]; trivial⟩)
  obtain ⟨A, hA, k, hk⟩ := hmono g
  have hA_nonempty : A.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have h0 := hcount A hA
    simp [hemp] at h0
    exact Cardinal.aleph0_ne_zero h0.symm
  obtain ⟨x₀, hx₀⟩ := hA_nonempty
  let c₀ : C := f ⟨x₀, Set.mem_sUnion_of_mem hx₀ hA⟩
  apply hno_mono A hA
  refine ⟨c₀, ?_⟩
  intro x hx
  have h1 : emb (f ⟨x, Set.mem_sUnion_of_mem hx hA⟩) = k := hk x hx
  have h2 : emb c₀ = k := hk x₀ hx₀
  exact emb.injective (h1.trans h2.symm)

end MainTheorems

end JSP_000490

#check JSP_000490.erdos_rado_countable
#check JSP_000490.jsp_000490_for_every_color_type
#check JSP_000490.jsp_000490_no_uniform_cardinal_bound

#print axioms JSP_000490.erdos_rado_countable
#print axioms JSP_000490.jsp_000490_for_every_color_type
#print axioms JSP_000490.jsp_000490_no_uniform_cardinal_bound
