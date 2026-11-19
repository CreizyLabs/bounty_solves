import Mathlib

/-!
# JSP-000690 (Erdős–Lovász 1974): 3-Uniform, 3-Chromatic-Critical Hypergraph of Minimum Degree 7

- **Catalog ID:** JSP-000690 (`catalog-0601-0700.md`)
- **Problem:** Erdős–Lovász (1974): *"Is there a three-uniform, three-chromatic-critical hypergraph
  with minimum degree at least seven?"*
- **Answer:** **Yes** — there exists an explicit **7-regular**, **21-edge**, **3-uniform**
  hypergraph `H` on `9` vertices (`Fin 9`) with chromatic number `χ(H) = 3` that is both
  **edge-critical** (every proper subhypergraph `H.erase e` is 2-colorable) and
  **vertex-critical** (deleting any vertex makes the remaining hypergraph 2-colorable).

## Proof Method
1. Define the 21-edge 3-uniform hypergraph `erdosLovasz9 : Finset (Finset (Fin 9))` from its
   explicit list of 21 ordered triples `erdosLovasz9Triples`.
2. Verify `IsUniform 3 erdosLovasz9`, `erdosLovasz9.card = 21`, and 7-regularity
   `∀ v : Fin 9, vertexDegree erdosLovasz9 v = 7` (hence `HasMinDegreeAtLeast 7`).
3. Exhibit an explicit proper 3-coloring `threeColoring9 : Fin 9 → Fin 3` (`{0,1,2} ↦ 0,
   {3,4,5} ↦ 1, {6,7,8} ↦ 2`) proving `IsKColorable 3 erdosLovasz9`.
4. Encode arbitrary 2-colorings `c : Fin 9 → Fin 2` losslessly into 9-bit masks `maskOf c < 512`
   with `maskBit (maskOf c) v = (c v).1`, and verify via a depth-9 binary-tree check `checkPow2 0 9`
   in the Lean kernel (`decide`, no `native_decide`) that every `m < 512` makes at least one triple
   in `erdosLovasz9Triples` monochromatic, establishing `¬ IsKColorable 2 erdosLovasz9`.
5. Exhibit an explicit witness 2-coloring mask for each of the 21 edges and verify in the Lean
   kernel (`List.all` + `decide`, no `native_decide`) that removing any edge `e ∈ erdosLovasz9`
   makes `erdosLovasz9.erase e` 2-colorable (edge-criticality), which immediately also yields
   vertex-criticality since every vertex has degree `7 ≥ 1`.

## Formal Guarantees
- Unconditional, zero `sorry`, zero `admit`, zero custom axioms, zero `native_decide`,
  zero approximations.
-/

namespace JSP_000690

open Finset

/-! ## Section 1: Hypergraph Definitions -/

/-- A hypergraph `H` on vertex type `V` is `k`-uniform if every hyperedge has size `k`. -/
def IsUniform {V : Type*} (k : ℕ) (H : Finset (Finset V)) : Prop :=
  ∀ e ∈ H, e.card = k

/-- The degree of a vertex `v` in a hypergraph `H` is the number of hyperedges containing `v`. -/
def vertexDegree {V : Type*} [DecidableEq V] (H : Finset (Finset V)) (v : V) : ℕ :=
  (H.filter fun e => v ∈ e).card

/-- Every vertex of `H` has degree at least `d`. -/
def HasMinDegreeAtLeast {V : Type*} [DecidableEq V] (d : ℕ) (H : Finset (Finset V)) : Prop :=
  ∀ v : V, d ≤ vertexDegree H v

/-- A weak (standard) proper hypergraph coloring: no hyperedge is monochromatic. -/
def IsProperHypergraphColoring {V α : Type*} (H : Finset (Finset V)) (c : V → α) : Prop :=
  ∀ e ∈ H, ∃ u ∈ e, ∃ v ∈ e, c u ≠ c v

/-- A hypergraph `H` is `k`-colorable if it admits a proper hypergraph coloring with `k` colors. -/
def IsKColorable {V : Type*} (k : ℕ) (H : Finset (Finset V)) : Prop :=
  ∃ c : V → Fin k, IsProperHypergraphColoring H c

/-- A hypergraph `H` is 3-chromatic edge-critical if it is 3-colorable, not 2-colorable, and
deleting any single edge leaves a 2-colorable hypergraph. -/
def IsThreeChromaticEdgeCritical {V : Type*} [DecidableEq V] (H : Finset (Finset V)) : Prop :=
  IsKColorable 3 H ∧ ¬ IsKColorable 2 H ∧ ∀ e ∈ H, IsKColorable 2 (H.erase e)

/-- A hypergraph `H` is 3-chromatic vertex-critical if it is 3-colorable, not 2-colorable, and
deleting any vertex (all incident edges) leaves a 2-colorable hypergraph. -/
def IsThreeChromaticVertexCritical {V : Type*} [DecidableEq V] (H : Finset (Finset V)) : Prop :=
  IsKColorable 3 H ∧ ¬ IsKColorable 2 H ∧ ∀ v : V, IsKColorable 2 (H.filter fun e => v ∉ e)

/-- Combined 3-chromatic-criticality (both edge-critical and vertex-critical). -/
def IsThreeChromaticCritical {V : Type*} [DecidableEq V] (H : Finset (Finset V)) : Prop :=
  IsThreeChromaticEdgeCritical H ∧ IsThreeChromaticVertexCritical H

lemma isKColorable_mono {V : Type*} {k : ℕ} {H₁ H₂ : Finset (Finset V)}
    (hsub : H₁ ⊆ H₂) (hcol : IsKColorable k H₂) : IsKColorable k H₁ := by
  obtain ⟨c, hc⟩ := hcol
  exact ⟨c, fun e he => hc e (hsub he)⟩

lemma isThreeChromaticVertexCritical_of_edgeCritical {V : Type*} [DecidableEq V]
    {H : Finset (Finset V)} (hEdge : IsThreeChromaticEdgeCritical H)
    (hdeg : HasMinDegreeAtLeast 1 H) :
    IsThreeChromaticVertexCritical H := by
  refine ⟨hEdge.1, hEdge.2.1, fun v => ?_⟩
  have hpos : 0 < (H.filter fun e => v ∈ e).card := hdeg v
  obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
  have heH : e ∈ H := (Finset.mem_filter.mp he).1
  have hve : v ∈ e := (Finset.mem_filter.mp he).2
  have hsub : (H.filter fun f => v ∉ f) ⊆ H.erase e := by
    intro f hf
    have hfH : f ∈ H := (Finset.mem_filter.mp hf).1
    have hvf : v ∉ f := (Finset.mem_filter.mp hf).2
    refine Finset.mem_erase.mpr ⟨?_, hfH⟩
    rintro rfl
    exact hvf hve
  exact isKColorable_mono hsub (hEdge.2.2 e heH)

/-! ## Section 2: Explicit 7-Regular 21-Edge 3-Uniform Hypergraph on 9 Vertices -/

/-- Ordered triple representation of the 21 hyperedges on `Fin 9`. -/
def erdosLovasz9Triples : List (Fin 9 × Fin 9 × Fin 9) :=
  [ (0, 1, 6), (0, 2, 4), (0, 4, 5), (0, 4, 6), (0, 4, 7), (0, 5, 6), (0, 5, 7),
    (1, 2, 8), (1, 3, 5), (1, 3, 6), (1, 3, 8), (1, 5, 6), (1, 6, 8),
    (2, 3, 7), (2, 3, 8), (2, 4, 7), (2, 4, 8), (2, 7, 8),
    (3, 5, 6), (3, 7, 8), (4, 5, 7) ]

/-- Convert an ordered triple to its 3-element `Finset (Fin 9)`. -/
def tripleToEdge (t : Fin 9 × Fin 9 × Fin 9) : Finset (Fin 9) :=
  {t.1, t.2.1, t.2.2}

/-- The 21-edge 3-uniform hypergraph `erdosLovasz9` on `Fin 9`. -/
def erdosLovasz9 : Finset (Finset (Fin 9)) :=
  (erdosLovasz9Triples.map tripleToEdge).toFinset

lemma mem_erdosLovasz9_iff (e : Finset (Fin 9)) :
    e ∈ erdosLovasz9 ↔ ∃ t ∈ erdosLovasz9Triples, tripleToEdge t = e := by
  simp [erdosLovasz9]

lemma tripleToEdge_mem_erdosLovasz9 {t : Fin 9 × Fin 9 × Fin 9} (ht : t ∈ erdosLovasz9Triples) :
    tripleToEdge t ∈ erdosLovasz9 :=
  (mem_erdosLovasz9_iff _).mpr ⟨t, ht, rfl⟩

lemma erdosLovasz9Triples_distinct :
    erdosLovasz9Triples.all (fun t => t.1 != t.2.1 && t.1 != t.2.2 && t.2.1 != t.2.2) = true := by
  decide

lemma erdosLovasz9_isUniform3 : IsUniform 3 erdosLovasz9 := by
  intro e he
  obtain ⟨t, ht, rfl⟩ := (mem_erdosLovasz9_iff e).mp he
  have hdist := List.all_eq_true.mp erdosLovasz9Triples_distinct t ht
  simp only [Bool.and_eq_true, bne_iff_ne] at hdist
  obtain ⟨⟨h12, h13⟩, h23⟩ := hdist
  unfold tripleToEdge
  rw [Finset.card_insert_of_notMem, Finset.card_pair h23]
  simp [h12, h13]

lemma erdosLovasz9_card_eq_21 : erdosLovasz9.card = 21 := by
  decide

lemma erdosLovasz9_seven_regular : ∀ v : Fin 9, vertexDegree erdosLovasz9 v = 7 := by
  decide

lemma erdosLovasz9_minDegree_ge_7 : HasMinDegreeAtLeast 7 erdosLovasz9 := fun v =>
  le_of_eq (erdosLovasz9_seven_regular v).symm

/-! ## Section 3: 3-Colorability -/

/-- Explicit proper 3-coloring: `{0,1,2} ↦ 0`, `{3,4,5} ↦ 1`, `{6,7,8} ↦ 2`. -/
def threeColoring9 (v : Fin 9) : Fin 3 :=
  ⟨v.1 / 3, by have := v.2; omega⟩

lemma threeColoring9_all :
    erdosLovasz9Triples.all
      (fun t => (t.1.1 / 3 != t.2.1.1 / 3) || (t.1.1 / 3 != t.2.2.1 / 3)) = true := by
  decide

theorem erdosLovasz9_isThreeColorable : IsKColorable 3 erdosLovasz9 := by
  refine ⟨threeColoring9, fun e he => ?_⟩
  obtain ⟨t, ht, rfl⟩ := (mem_erdosLovasz9_iff e).mp he
  have hok := List.all_eq_true.mp threeColoring9_all t ht
  simp only [Bool.or_eq_true, bne_iff_ne] at hok
  rcases hok with h12 | h13
  · refine ⟨t.1, by simp [tripleToEdge], t.2.1, by simp [tripleToEdge], ?_⟩
    intro heq
    exact h12 (congrArg Fin.val heq)
  · refine ⟨t.1, by simp [tripleToEdge], t.2.2, by simp [tripleToEdge], ?_⟩
    intro heq
    exact h13 (congrArg Fin.val heq)

/-! ## Section 4: Non-2-Colorability via Depth-9 Binary-Tree Mask Verification -/

/-- Extract bit `v` of a natural number mask `m`. -/
def maskBit (m : ℕ) (v : Fin 9) : ℕ :=
  (m / 2 ^ v.1) % 2

/-- Decode a natural number mask `m` into a 2-coloring `Fin 9 → Fin 2`. -/
def maskColor (m : ℕ) (v : Fin 9) : Fin 2 :=
  ⟨maskBit m v, Nat.mod_lt _ (by decide)⟩

/-- Encode any 2-coloring `c : Fin 9 → Fin 2` as a 9-bit natural number `< 512`. -/
def maskOf (c : Fin 9 → Fin 2) : ℕ :=
  (c 0).1 + 2 * (c 1).1 + 4 * (c 2).1 + 8 * (c 3).1 + 16 * (c 4).1 +
  32 * (c 5).1 + 64 * (c 6).1 + 128 * (c 7).1 + 256 * (c 8).1

lemma maskOf_lt (c : Fin 9 → Fin 2) : maskOf c < 512 := by
  have := (c 0).2; have := (c 1).2; have := (c 2).2
  have := (c 3).2; have := (c 4).2; have := (c 5).2
  have := (c 6).2; have := (c 7).2; have := (c 8).2
  unfold maskOf
  omega

lemma maskBit_maskOf (c : Fin 9 → Fin 2) (v : Fin 9) :
    maskBit (maskOf c) v = (c v).1 := by
  have h0 := (c 0).2; have h1 := (c 1).2; have h2 := (c 2).2
  have h3 := (c 3).2; have h4 := (c 4).2; have h5 := (c 5).2
  have h6 := (c 6).2; have h7 := (c 7).2; have h8 := (c 8).2
  fin_cases v <;> dsimp [maskBit, maskOf] <;> omega

/-- Boolean predicate: mask `m` makes at least one triple in `erdosLovasz9Triples` monochromatic. -/
def hasMonoTriple (m : ℕ) : Bool :=
  erdosLovasz9Triples.any fun t =>
    (maskBit m t.1 == maskBit m t.2.1) && (maskBit m t.1 == maskBit m t.2.2)

/-- Balanced binary-tree verification of `hasMonoTriple` over `[base, base + 2^k)` (depth `k`). -/
def checkPow2 (base : ℕ) : ℕ → Bool
  | 0 => hasMonoTriple base
  | k + 1 => checkPow2 base k && checkPow2 (base + 2 ^ k) k

lemma checkPow2_sound (base k m : ℕ) (hlo : base ≤ m) (hhi : m < base + 2 ^ k)
    (hok : checkPow2 base k = true) : hasMonoTriple m = true := by
  induction k generalizing base with
  | zero =>
    have hm : m = base := by omega
    subst hm
    exact hok
  | succ k ih =>
    simp only [checkPow2, Bool.and_eq_true] at hok
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by omega
    by_cases hmid : m < base + 2 ^ k
    · exact ih base hlo hmid hok.1
    · exact ih (base + 2 ^ k) (by omega) (by omega) hok.2

lemma checkPow2_zero_9 : checkPow2 0 9 = true := by
  decide

theorem erdosLovasz9_not_twoColorable : ¬ IsKColorable 2 erdosLovasz9 := by
  rintro ⟨c, hc⟩
  have hmono : hasMonoTriple (maskOf c) = true :=
    checkPow2_sound 0 9 (maskOf c) (Nat.zero_le _) (by simpa using maskOf_lt c) checkPow2_zero_9
  unfold hasMonoTriple at hmono
  rw [List.any_eq_true] at hmono
  obtain ⟨t, ht, hEq⟩ := hmono
  simp only [Bool.and_eq_true, beq_iff_eq, maskBit_maskOf] at hEq
  have h12 : c t.1 = c t.2.1 := Fin.ext hEq.1
  have h13 : c t.1 = c t.2.2 := Fin.ext hEq.2
  obtain ⟨u, hu, v, hv, huv⟩ := hc (tripleToEdge t) (tripleToEdge_mem_erdosLovasz9 ht)
  simp only [tripleToEdge, Finset.mem_insert, Finset.mem_singleton] at hu hv
  have hu_eq : c u = c t.1 := by
    rcases hu with rfl | rfl | rfl
    · rfl
    · exact h12.symm
    · exact h13.symm
  have hv_eq : c v = c t.1 := by
    rcases hv with rfl | rfl | rfl
    · rfl
    · exact h12.symm
    · exact h13.symm
  exact huv (hu_eq.trans hv_eq.symm)

/-! ## Section 5: Edge-Criticality and Vertex-Criticality -/

/-- Explicit witness 2-coloring mask for each of the 21 hyperedges, showing that deleting
that single hyperedge makes the remaining 20 hyperedges 2-colorable. -/
def erdosLovasz9Witnesses : List ((Fin 9 × Fin 9 × Fin 9) × ℕ) :=
  [ ((0, 1, 6), 199), ((0, 2, 4), 31),  ((0, 4, 5), 198), ((0, 4, 6), 166),
    ((0, 4, 7), 155), ((0, 5, 6), 154), ((0, 5, 7), 92),  ((1, 2, 8), 216),
    ((1, 3, 5), 47),  ((1, 3, 6), 218), ((1, 3, 8), 228), ((1, 5, 6), 230),
    ((1, 6, 8), 45),  ((2, 3, 7), 143), ((2, 3, 8), 210), ((2, 4, 7), 214),
    ((2, 4, 8), 139), ((2, 7, 8), 27),  ((3, 5, 6), 124), ((3, 7, 8), 39),
    ((4, 5, 7), 15) ]

lemma witnesses_cover_all :
    erdosLovasz9Triples.all (fun t => erdosLovasz9Witnesses.any (fun p => p.1 == t)) = true := by
  decide

lemma witnesses_valid_all :
    erdosLovasz9Witnesses.all (fun p =>
      erdosLovasz9Triples.all fun t =>
        (t == p.1) || (maskBit p.2 t.1 != maskBit p.2 t.2.1) ||
          (maskBit p.2 t.1 != maskBit p.2 t.2.2)) = true := by
  decide

theorem erdosLovasz9_edgeCritical :
    ∀ e ∈ erdosLovasz9, IsKColorable 2 (erdosLovasz9.erase e) := by
  intro e he
  obtain ⟨t₀, ht₀, rfl⟩ := (mem_erdosLovasz9_iff e).mp he
  have hcov := List.all_eq_true.mp witnesses_cover_all t₀ ht₀
  rw [List.any_eq_true] at hcov
  obtain ⟨p, hp, hpeq⟩ := hcov
  simp only [beq_iff_eq] at hpeq
  refine ⟨maskColor p.2, fun f hf => ?_⟩
  have hne : f ≠ tripleToEdge t₀ := (Finset.mem_erase.mp hf).1
  have hfH : f ∈ erdosLovasz9 := (Finset.mem_erase.mp hf).2
  obtain ⟨t, ht, rfl⟩ := (mem_erdosLovasz9_iff f).mp hfH
  have ht_ne : t ≠ p.1 := by
    intro h
    apply hne
    rw [h, hpeq]
  have hval := List.all_eq_true.mp (List.all_eq_true.mp witnesses_valid_all p hp) t ht
  simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne] at hval
  rcases hval with (hteq | h12) | h13
  · exact absurd hteq ht_ne
  · refine ⟨t.1, by simp [tripleToEdge], t.2.1, by simp [tripleToEdge], ?_⟩
    intro heq
    exact h12 (congrArg Fin.val heq)
  · refine ⟨t.1, by simp [tripleToEdge], t.2.2, by simp [tripleToEdge], ?_⟩
    intro heq
    exact h13 (congrArg Fin.val heq)

theorem erdosLovasz9_isThreeChromaticEdgeCritical :
    IsThreeChromaticEdgeCritical erdosLovasz9 :=
  ⟨erdosLovasz9_isThreeColorable, erdosLovasz9_not_twoColorable, erdosLovasz9_edgeCritical⟩

theorem erdosLovasz9_isThreeChromaticVertexCritical :
    IsThreeChromaticVertexCritical erdosLovasz9 :=
  isThreeChromaticVertexCritical_of_edgeCritical erdosLovasz9_isThreeChromaticEdgeCritical
    (fun v => le_trans (by decide : 1 ≤ 7) (erdosLovasz9_minDegree_ge_7 v))

theorem erdosLovasz9_isThreeChromaticCritical :
    IsThreeChromaticCritical erdosLovasz9 :=
  ⟨erdosLovasz9_isThreeChromaticEdgeCritical, erdosLovasz9_isThreeChromaticVertexCritical⟩

/-! ## Section 6: Main Theorems (JSP-000690) -/

/-- **Main Theorem (JSP-000690 / Erdős–Lovász 1974, concrete witness on `Fin 9`):**
There exists a 3-uniform, 3-chromatic-critical (both edge-critical and vertex-critical)
hypergraph on 9 vertices whose minimum degree is at least 7 (in fact, 7-regular with 21 edges). -/
theorem jsp_000690_erdos_lovasz_fin9 :
    ∃ H : Finset (Finset (Fin 9)),
      IsUniform 3 H ∧
      HasMinDegreeAtLeast 7 H ∧
      IsThreeChromaticCritical H :=
  ⟨erdosLovasz9, erdosLovasz9_isUniform3, erdosLovasz9_minDegree_ge_7,
    erdosLovasz9_isThreeChromaticCritical⟩

/-- **Main Theorem (JSP-000690 / Erdős–Lovász 1974, existential form over finite vertex types):**
There exists a finite nonempty vertex set `V` and a 3-uniform hypergraph `H` on `V` with
minimum degree at least 7 that is 3-chromatic-critical (both edge-critical and vertex-critical). -/
theorem jsp_000690_erdos_lovasz_solved :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (H : Finset (Finset V)),
      Nonempty V ∧
      IsUniform 3 H ∧
      HasMinDegreeAtLeast 7 H ∧
      IsThreeChromaticCritical H :=
  ⟨Fin 9, inferInstance, inferInstance, erdosLovasz9, ⟨0⟩,
    erdosLovasz9_isUniform3, erdosLovasz9_minDegree_ge_7,
    erdosLovasz9_isThreeChromaticCritical⟩

end JSP_000690

#check JSP_000690.erdosLovasz9_isUniform3
#check JSP_000690.erdosLovasz9_seven_regular
#check JSP_000690.erdosLovasz9_isThreeChromaticCritical
#check JSP_000690.jsp_000690_erdos_lovasz_fin9
#check JSP_000690.jsp_000690_erdos_lovasz_solved

#print axioms JSP_000690.erdosLovasz9_isUniform3
#print axioms JSP_000690.erdosLovasz9_seven_regular
#print axioms JSP_000690.erdosLovasz9_isThreeChromaticCritical
#print axioms JSP_000690.jsp_000690_erdos_lovasz_fin9
#print axioms JSP_000690.jsp_000690_erdos_lovasz_solved
