import Mathlib

/-!
# JSP-000698 (Erdős Problem #842): Unconditional Proof of the Fleischner–Stiebitz Theorem

- **Catalog ID:** JSP-000698 (`catalog-0601-0700.md`)
- **Erdős Problem:** #842 (Cycle-Plus-Triangles Conjecture; posed by Du, Hsu, Hwang and
  strengthened by Paul Erdős; proved by H. Fleischner and M. Stiebitz, Discrete Math. 1992)
- **Question:** Is every graph formed by vertex-disjoint triangles and a spanning Hamilton
  cycle three-colorable?
- **Answer:** Yes — in fact every such graph is **3-choosable** (list-colorable from arbitrary
  lists of size at least `3`), and therefore 3-colorable (`χ(G) ≤ 3`).

## Proof Method
1. **Alon–Tarsi Theorem via Combinatorial Nullstellensatz (`Mathlib.Combinatorics.Nullstellensatz`):**
   For any finite directed multigraph `(V, A, src, dst)`, expanding the graph polynomial
   `P(x) = ∏ a : A, (X (src a) - X (dst a))` in `MvPolynomial V ℤ` yields that the coefficient
   of `∏ v, X v ^ outdeg(v)` equals `∑_{S Eulerian} (-1) ^ |S| = EE(D) - EO(D)`. When this
   signed Eulerian count is nonzero, `MvPolynomial.combinatorial_nullstellensatz_exists_eval_nonzero`
   yields a proper list coloring from any lists `L v` of size `> outdeg(v)`.
2. **Canonical 2-Regular Orientation & Complementation Involution:**
   Orient the spanning Hamilton cycle cyclically and each triangle cyclically. Every vertex
   has `outdeg = indeg = 2` and `|A| = 6n` is even. Complementation `S ↦ Sᶜ` is a
   fixed-point-free parity-preserving involution on both even and odd Eulerian subdigraphs,
   so `EE(D)` and `EO(D)` are both even; hence `EE(D) + EO(D) ≡ 2 (mod 4)` forces
   `EE(D) ≠ EO(D)`.
3. **Triangle Factorization & Subset Expansion:**
   Fixing the cycle arc subset `A ⊆ C`, valid extensions into the disjoint triangles factor as
   `∏_t triMatchCount(A, t)` where pointwise
   `triMatchCount(u - v) = 1_{∀ j, bal(t, j) = 0} + 1_{∑_j bal(t, j) = 0}`.
   Expanding over all `S ⊆ Fin n` yields `totalEulerian(D) = ∑_{S : Finset (Fin n)} N(S)`.
   For `S = ∅`, only `A = ∅` and `A = univ` satisfy zero balance at every cycle vertex, so
   `N(∅) = 2`.
4. **Chevalley–Warning Theorem (`Mathlib.FieldTheory.ChevalleyWarning`) for `S ≠ ∅`:**
   For every nonempty `S ⊆ Fin n`, complementation `A ↦ Aᶜ` gives `N(S) = 2 * N₀(S)` where
   `N₀(S)` fixes `0 ∉ A` (`3n - 1` free variables over `ZMod 2`). Encoding `∑_j in_j = ∑_j out_j`
   by a linear equation `P_t` (degree `1`) and quadratic carry equation `Q_t` (degree `2`)
   over `ZMod 2`, both `P_{t₀}` and `Q_{t₀}` for a chosen `t₀ ∈ S` are redundant by global
   balance conservation modulo `2` and `4`. The remaining equations have total degree
   `≤ 3(n - |S|) + 3(|S| - 1) = 3n - 3 < 3n - 1`. By `char_dvd_card_solutions_of_sum_lt` over
   `ZMod 2`, `2 ∣ N₀(S)`, hence `4 ∣ N(S)` for every nonempty `S`. Thus `totalEulerian(D) ≡ 2 (mod 4)`.

## Formal Guarantees
- Unconditional, zero `sorry`, zero `admit`, zero custom axioms
  (`[propext, Classical.choice, Quot.sound]`), zero approximations.
-/

namespace JSP_000698

open Finset MvPolynomial

/-! ## Section 1: Alon–Tarsi Theorem for Finite Directed Multigraphs -/

section AlonTarsi

variable {V A : Type*} [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]

/-- Outdegree multi-index of a finite directed multigraph `(src, dst)`. -/
noncomputable def outdegFinsupp (src : A → V) : V →₀ ℕ :=
  ∑ a : A, Finsupp.single (src a) 1

omit [Fintype V] [DecidableEq A] in
lemma outdegFinsupp_apply (src : A → V) (v : V) :
    outdegFinsupp src v = (Finset.univ.filter fun a : A => src a = v).card := by
  classical
  simp only [outdegFinsupp, Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.card_filter]

/-- Monomial exponent vector contributed by arc subset `S` in the expansion of `arcPoly`. -/
noncomputable def monomOf (src dst : A → V) (S : Finset A) : V →₀ ℕ :=
  (∑ a ∈ S, Finsupp.single (dst a) 1) + (∑ a ∈ Finset.univ \ S, Finsupp.single (src a) 1)

omit [Fintype V] in
lemma monomOf_apply (src dst : A → V) (S : Finset A) (v : V) :
    monomOf src dst S v =
      (S.filter fun a => dst a = v).card + ((Finset.univ \ S).filter fun a => src a = v).card := by
  classical
  simp only [monomOf, Finsupp.add_apply, Finsupp.finsetSum_apply, Finsupp.single_apply,
    Finset.card_filter]

/-- A subdigraph `S ⊆ A` is Eulerian if every vertex has equal indegree and outdegree in `S`. -/
def IsEulerian (src dst : A → V) (S : Finset A) : Prop :=
  ∀ v : V, (S.filter fun a => src a = v).card = (S.filter fun a => dst a = v).card

instance instDecidablePredIsEulerian (src dst : A → V) :
    DecidablePred (IsEulerian src dst) := fun _ =>
  Fintype.decidableForallFintype

omit [Fintype V] in
lemma monomOf_eq_outdeg_iff (src dst : A → V) (S : Finset A) :
    monomOf src dst S = outdegFinsupp src ↔ IsEulerian src dst S := by
  rw [Finsupp.ext_iff]
  constructor
  · intro h v
    have hv := h v
    rw [monomOf_apply, outdegFinsupp_apply] at hv
    have hsplit : (Finset.univ.filter fun a : A => src a = v).card =
        (S.filter fun a => src a = v).card +
        ((Finset.univ \ S).filter fun a => src a = v).card := by
      have hunion : S ∪ (Finset.univ \ S) = Finset.univ :=
        Finset.union_sdiff_of_subset (subset_univ S)
      have hdisj : Disjoint (S.filter fun a => src a = v)
          ((Finset.univ \ S).filter fun a => src a = v) :=
        Finset.disjoint_filter_filter disjoint_sdiff_self_right
      rw [← Finset.card_union_of_disjoint hdisj, ← Finset.filter_union, hunion]
    omega
  · intro h v
    rw [monomOf_apply, outdegFinsupp_apply]
    have hsplit : (Finset.univ.filter fun a : A => src a = v).card =
        (S.filter fun a => src a = v).card +
        ((Finset.univ \ S).filter fun a => src a = v).card := by
      have hunion : S ∪ (Finset.univ \ S) = Finset.univ :=
        Finset.union_sdiff_of_subset (subset_univ S)
      have hdisj : Disjoint (S.filter fun a => src a = v)
          ((Finset.univ \ S).filter fun a => src a = v) :=
        Finset.disjoint_filter_filter disjoint_sdiff_self_right
      rw [← Finset.card_union_of_disjoint hdisj, ← Finset.filter_union, hunion]
    have hv := h v
    omega

omit [Fintype V] [DecidableEq V] in
lemma finsupp_sum_single_one_degree {ι : Type*} (s : Finset ι) (f : ι → V) :
    Finsupp.degree (∑ a ∈ s, Finsupp.single (f a) 1) = s.card := by
  rw [map_sum]
  simp [Finsupp.degree_single]

omit [Fintype V] [DecidableEq V] in
lemma monomOf_degree (src dst : A → V) (S : Finset A) :
    Finsupp.degree (monomOf src dst S) = Fintype.card A := by
  unfold monomOf
  rw [map_add, finsupp_sum_single_one_degree, finsupp_sum_single_one_degree,
    Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ]
  have hle : S.card ≤ Fintype.card A := Finset.card_le_univ S
  omega

omit [Fintype V] [DecidableEq V] [DecidableEq A] in
lemma outdegFinsupp_degree (src : A → V) :
    Finsupp.degree (outdegFinsupp src) = Fintype.card A := by
  unfold outdegFinsupp
  rw [finsupp_sum_single_one_degree, Finset.card_univ]

/-- The graph polynomial `∏ a, (X (src a) - X (dst a))` over `ℤ`. -/
noncomputable def arcPoly (src dst : A → V) : MvPolynomial V ℤ :=
  ∏ a : A, (MvPolynomial.X (src a) - MvPolynomial.X (dst a))

omit [Fintype V] [DecidableEq V] in
lemma prod_X_eq_monomial {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → V) :
    (∏ a ∈ s, (MvPolynomial.X (f a) : MvPolynomial V ℤ)) =
      MvPolynomial.monomial (∑ a ∈ s, Finsupp.single (f a) 1) 1 := by
  induction s using Finset.induction_on with
  | empty =>
    simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih]
    rw [MvPolynomial.X, MvPolynomial.monomial_mul_monomial, one_mul]

omit [Fintype V] [DecidableEq V] in
lemma arcPoly_expand (src dst : A → V) :
    arcPoly src dst =
      ∑ S ∈ (Finset.univ : Finset A).powerset,
        MvPolynomial.monomial (monomOf src dst S) ((-1 : ℤ) ^ S.card) := by
  unfold arcPoly
  have hsub : ∀ a : A, (MvPolynomial.X (src a) - MvPolynomial.X (dst a) : MvPolynomial V ℤ) =
      (- MvPolynomial.X (dst a)) + MvPolynomial.X (src a) := fun a => sub_eq_neg_add _ _
  simp_rw [hsub]
  rw [Finset.prod_add]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.prod_neg, prod_X_eq_monomial, prod_X_eq_monomial]
  have hneg : ((-1 : MvPolynomial V ℤ) ^ S.card) = MvPolynomial.C ((-1 : ℤ) ^ S.card) := by
    simp
  rw [hneg, mul_assoc, MvPolynomial.monomial_mul_monomial, one_mul, MvPolynomial.C_mul_monomial,
    mul_one]
  rfl

/-- Signed Eulerian count `EE(D) - EO(D)`. -/
def signedEulerianCount (src dst : A → V) : ℤ :=
  ∑ S ∈ (Finset.univ : Finset (Finset A)).filter (IsEulerian src dst), (-1 : ℤ) ^ S.card

lemma arcPoly_coeff_outdeg (src dst : A → V) :
    (arcPoly src dst).coeff (outdegFinsupp src) = signedEulerianCount src dst := by
  rw [arcPoly_expand, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial, signedEulerianCount]
  have hpow : (Finset.univ : Finset A).powerset = (Finset.univ : Finset (Finset A)) := by
    ext S; simp
  rw [hpow, Finset.sum_filter]
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases h : IsEulerian src dst S
  · have hm : monomOf src dst S = outdegFinsupp src := (monomOf_eq_outdeg_iff src dst S).mpr h
    simp [h, hm]
  · have hm : monomOf src dst S ≠ outdegFinsupp src := fun heq =>
      h ((monomOf_eq_outdeg_iff src dst S).mp heq)
    simp [h, hm]

omit [Fintype V] [DecidableEq V] in
lemma arcPoly_totalDegree_le (src dst : A → V) :
    (arcPoly src dst).totalDegree ≤ Fintype.card A := by
  rw [arcPoly_expand]
  refine le_trans (MvPolynomial.totalDegree_finsetSum _ _) ?_
  rw [Finset.sup_le_iff]
  intro S _
  refine le_trans (MvPolynomial.totalDegree_monomial_le _ _) ?_
  simpa [Finsupp.sum, Finsupp.degree_apply] using le_of_eq (monomOf_degree src dst S)

/-- Alon–Tarsi list-coloring theorem over `ℤ` for finite directed multigraphs. -/
theorem alon_tarsi_int (src dst : A → V)
    (hEul : signedEulerianCount src dst ≠ 0)
    (L : V → Finset ℤ)
    (hL : ∀ v : V, (Finset.univ.filter fun a : A => src a = v).card < (L v).card) :
    ∃ c : V → ℤ, (∀ v : V, c v ∈ L v) ∧ ∀ a : A, c (src a) ≠ c (dst a) := by
  have hcoeff : (arcPoly src dst).coeff (outdegFinsupp src) ≠ 0 := by
    rw [arcPoly_coeff_outdeg]
    exact hEul
  have hdeg_le : (arcPoly src dst).totalDegree ≤ Finsupp.degree (outdegFinsupp src) := by
    rw [outdegFinsupp_degree]
    exact arcPoly_totalDegree_le src dst
  have hdeg_ge : Finsupp.degree (outdegFinsupp src) ≤ (arcPoly src dst).totalDegree := by
    rw [Finsupp.degree_apply]
    exact MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hcoeff)
  have hdeg_eq : (arcPoly src dst).totalDegree = Finsupp.degree (outdegFinsupp src) :=
    le_antisymm hdeg_le hdeg_ge
  have htL : ∀ v : V, outdegFinsupp src v < (L v).card := by
    intro v
    rw [outdegFinsupp_apply]
    exact hL v
  obtain ⟨c, hcL, hceval⟩ :=
    MvPolynomial.combinatorial_nullstellensatz_exists_eval_nonzero
      (arcPoly src dst) (outdegFinsupp src) hcoeff hdeg_eq L htL
  refine ⟨c, hcL, ?_⟩
  intro a hEq
  apply hceval
  unfold arcPoly
  rw [map_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ a)
  simp [hEq]

/-- Alon–Tarsi list-coloring theorem for arbitrary color types `α`. -/
theorem alon_tarsi_list_coloring {α : Type*} [DecidableEq α] (src dst : A → V)
    (hEul : signedEulerianCount src dst ≠ 0)
    (L : V → Finset α)
    (hL : ∀ v : V, (Finset.univ.filter fun a : A => src a = v).card < (L v).card) :
    ∃ c : V → α, (∀ v : V, c v ∈ L v) ∧ ∀ a : A, c (src a) ≠ c (dst a) := by
  let U : Finset α := Finset.univ.biUnion L
  let e : U ≃ Fin (Fintype.card U) := Fintype.equivFin U
  let encode : U → ℤ := fun x => ((e x).1 : ℤ)
  have henc_inj : Function.Injective encode := by
    intro x y hxy
    have hnat : (e x).1 = (e y).1 := Int.ofNat.inj hxy
    exact e.injective (Fin.ext hnat)
  let L' : V → Finset ℤ := fun v =>
    (L v).attach.image fun x => encode ⟨x.1, Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ v, x.2⟩⟩
  have hL'_card : ∀ v : V, (L' v).card = (L v).card := by
    intro v
    dsimp [L']
    rw [Finset.card_image_of_injective]
    · exact Finset.card_attach
    · intro x y hxy
      have hsub : (⟨x.1, Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ v, x.2⟩⟩ : U) =
          ⟨y.1, Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ v, y.2⟩⟩ := henc_inj hxy
      exact Subtype.ext (congrArg (fun z : U => z.1) hsub)
  have hL' : ∀ v : V, (Finset.univ.filter fun a : A => src a = v).card < (L' v).card := by
    intro v
    rw [hL'_card]
    exact hL v
  obtain ⟨c', hc'L', hc'adj⟩ := alon_tarsi_int src dst hEul L' hL'
  have hex : ∀ v : V, ∃ x : α, x ∈ L v ∧
      ∃ hxU : x ∈ U, encode ⟨x, hxU⟩ = c' v := by
    intro v
    have hv := hc'L' v
    dsimp [L'] at hv
    rw [Finset.mem_image] at hv
    obtain ⟨⟨x, hxL⟩, _, hxeq⟩ := hv
    exact ⟨x, hxL, Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ v, hxL⟩, hxeq⟩
  let c : V → α := fun v => (hex v).choose
  refine ⟨c, fun v => (hex v).choose_spec.1, ?_⟩
  intro a hEq
  obtain ⟨_, hx1, h1⟩ := (hex (src a)).choose_spec
  obtain ⟨_, hx2, h2⟩ := (hex (dst a)).choose_spec
  apply hc'adj a
  rw [← h1, ← h2]
  have hsub : (⟨c (src a), hx1⟩ : U) = ⟨c (dst a), hx2⟩ := Subtype.ext hEq
  exact congrArg encode hsub

end AlonTarsi

/-! ## Section 2: Cycle-Plus-Triangles Orientation and Parity Reduction -/

section CyclePlusTrianglesOrientation

/-- Next index in a directed 3-cycle `0 → 1 → 2 → 0`. -/
def triNext : Fin 3 → Fin 3
  | ⟨0, _⟩ => ⟨1, by omega⟩
  | ⟨1, _⟩ => ⟨2, by omega⟩
  | ⟨2, _⟩ => ⟨0, by omega⟩

/-- Previous index in a directed 3-cycle `0 → 1 → 2 → 0`. -/
def triPrev : Fin 3 → Fin 3
  | ⟨0, _⟩ => ⟨2, by omega⟩
  | ⟨1, _⟩ => ⟨0, by omega⟩
  | ⟨2, _⟩ => ⟨1, by omega⟩

lemma triNext_triPrev (j : Fin 3) : triNext (triPrev j) = j := by fin_cases j <;> rfl
lemma triPrev_triNext (j : Fin 3) : triPrev (triNext j) = j := by fin_cases j <;> rfl

/-- Next vertex on the directed `3n`-cycle. -/
def cycNext {n : ℕ} (hn : 0 < n) (i : Fin (3 * n)) : Fin (3 * n) :=
  ⟨(i.1 + 1) % (3 * n), Nat.mod_lt _ (by omega)⟩

/-- Previous vertex on the directed `3n`-cycle. -/
def cycPrev {n : ℕ} (hn : 0 < n) (i : Fin (3 * n)) : Fin (3 * n) :=
  ⟨(i.1 + (3 * n - 1)) % (3 * n), Nat.mod_lt _ (by omega)⟩

lemma cycNext_cycPrev {n : ℕ} (hn : 0 < n) (i : Fin (3 * n)) :
    cycNext hn (cycPrev hn i) = i := by
  ext
  simp only [cycNext, cycPrev]
  have hi : i.1 < 3 * n := i.2
  rw [Nat.mod_add_mod]
  have h : i.1 + (3 * n - 1) + 1 = i.1 + 3 * n := by omega
  rw [h, Nat.add_mod_right, Nat.mod_eq_of_lt hi]

lemma cycPrev_cycNext {n : ℕ} (hn : 0 < n) (i : Fin (3 * n)) :
    cycPrev hn (cycNext hn i) = i := by
  ext
  simp only [cycNext, cycPrev]
  have hi : i.1 < 3 * n := i.2
  rw [Nat.mod_add_mod]
  have h : i.1 + 1 + (3 * n - 1) = i.1 + 3 * n := by omega
  rw [h, Nat.add_mod_right, Nat.mod_eq_of_lt hi]

/-- Equivalence `cycPrev hn` on `Fin (3 * n)`. -/
def cycPrevEquiv {n : ℕ} (hn : 0 < n) : Fin (3 * n) ≃ Fin (3 * n) where
  toFun := cycPrev hn
  invFun := cycNext hn
  left_inv := cycNext_cycPrev hn
  right_inv := cycPrev_cycNext hn

/-- Arc index type of the oriented cycle-plus-triangles multigraph:
`3n` cycle arcs plus `3n` triangle arcs (`6n` total). -/
abbrev CPTArc (n : ℕ) := Fin (3 * n) ⊕ (Fin n × Fin 3)

/-- Source vertex of each arc in the oriented cycle-plus-triangles multigraph. -/
def cptSrc {n : ℕ} (π : Fin n × Fin 3 ≃ Fin (3 * n)) : CPTArc n → Fin (3 * n)
  | Sum.inl i => i
  | Sum.inr p => π p

/-- Target vertex of each arc in the oriented cycle-plus-triangles multigraph. -/
def cptDst {n : ℕ} (hn : 0 < n) (π : Fin n × Fin 3 ≃ Fin (3 * n)) : CPTArc n → Fin (3 * n)
  | Sum.inl i => cycNext hn i
  | Sum.inr (t, j) => π (t, triNext j)

lemma cptSrc_filter_eq {n : ℕ} (π : Fin n × Fin 3 ≃ Fin (3 * n)) (v : Fin (3 * n)) :
    (Finset.univ.filter fun a : CPTArc n => cptSrc π a = v) =
      ({Sum.inl v, Sum.inr (π.symm v)} : Finset (CPTArc n)) := by
  ext a
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  cases a with
  | inl i =>
    simp [cptSrc]
  | inr p =>
    simp only [cptSrc, reduceCtorEq, Sum.inr.injEq, false_or]
    exact ⟨fun h => (π.symm_apply_eq.mpr h.symm).symm, fun h => by rw [h, π.apply_symm_apply]⟩

lemma cptDst_filter_eq {n : ℕ} (hn : 0 < n) (π : Fin n × Fin 3 ≃ Fin (3 * n)) (v : Fin (3 * n)) :
    (Finset.univ.filter fun a : CPTArc n => cptDst hn π a = v) =
      ({Sum.inl (cycPrev hn v), Sum.inr ((π.symm v).1, triPrev (π.symm v).2)} : Finset (CPTArc n)) := by
  ext a
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  cases a with
  | inl i =>
    simp only [cptDst, Sum.inl.injEq, reduceCtorEq, or_false]
    constructor
    · intro h
      rw [← h, cycPrev_cycNext]
    · intro h
      rw [h, cycNext_cycPrev]
  | inr q =>
    rcases q with ⟨t, j⟩
    simp only [cptDst, reduceCtorEq, Sum.inr.injEq, false_or, Prod.mk.injEq]
    constructor
    · intro h
      have hq : (t, triNext j) = π.symm v := π.injective (by rw [h, π.apply_symm_apply])
      have ht : t = (π.symm v).1 := congrArg Prod.fst hq
      have hj : triNext j = (π.symm v).2 := congrArg Prod.snd hq
      exact ⟨ht, by rw [← hj, triPrev_triNext]⟩
    · rintro ⟨rfl, rfl⟩
      rw [triNext_triPrev, Prod.mk.eta, π.apply_symm_apply]

lemma cptSrc_filter_eq_pair {n : ℕ} (π : Fin n × Fin 3 ≃ Fin (3 * n)) (t : Fin n) (j : Fin 3) :
    (Finset.univ.filter fun a : CPTArc n => cptSrc π a = π (t, j)) =
      ({Sum.inl (π (t, j)), Sum.inr (t, j)} : Finset (CPTArc n)) := by
  rw [cptSrc_filter_eq, π.symm_apply_apply]

lemma cptDst_filter_eq_pair {n : ℕ} (hn : 0 < n) (π : Fin n × Fin 3 ≃ Fin (3 * n))
    (t : Fin n) (j : Fin 3) :
    (Finset.univ.filter fun a : CPTArc n => cptDst hn π a = π (t, j)) =
      ({Sum.inl (cycPrev hn (π (t, j))), Sum.inr (t, triPrev j)} : Finset (CPTArc n)) := by
  rw [cptDst_filter_eq, π.symm_apply_apply]

lemma cpt_outdeg {n : ℕ} (π : Fin n × Fin 3 ≃ Fin (3 * n)) (v : Fin (3 * n)) :
    (Finset.univ.filter fun a : CPTArc n => cptSrc π a = v).card = 2 := by
  rw [cptSrc_filter_eq, Finset.card_pair]
  simp

lemma cpt_indeg {n : ℕ} (hn : 0 < n) (π : Fin n × Fin 3 ≃ Fin (3 * n)) (v : Fin (3 * n)) :
    (Finset.univ.filter fun a : CPTArc n => cptDst hn π a = v).card = 2 := by
  rw [cptDst_filter_eq, Finset.card_pair]
  simp

/-- In the 2-regular orientation, the complement of an Eulerian subdigraph is Eulerian. -/
lemma cpt_isEulerian_compl {n : ℕ} (hn : 0 < n) (π : Fin n × Fin 3 ≃ Fin (3 * n))
    (S : Finset (CPTArc n)) :
    IsEulerian (cptSrc π) (cptDst hn π) Sᶜ ↔ IsEulerian (cptSrc π) (cptDst hn π) S := by
  have hpart : ∀ (f : CPTArc n → Fin (3 * n)) (v : Fin (3 * n)),
      (S.filter fun a => f a = v).card + (Sᶜ.filter fun a => f a = v).card =
      (Finset.univ.filter fun a => f a = v).card := by
    intro f v
    have hdisj : Disjoint (S.filter fun a => f a = v) (Sᶜ.filter fun a => f a = v) :=
      Finset.disjoint_filter_filter disjoint_compl_right
    rw [← Finset.card_union_of_disjoint hdisj, ← Finset.filter_union, Finset.union_compl]
  constructor
  · intro hc v
    have hs := hpart (cptSrc π) v
    have hd := hpart (cptDst hn π) v
    rw [cpt_outdeg] at hs
    rw [cpt_indeg] at hd
    have hv := hc v
    omega
  · intro hS v
    have hs := hpart (cptSrc π) v
    have hd := hpart (cptDst hn π) v
    rw [cpt_outdeg] at hs
    rw [cpt_indeg] at hd
    have hv := hS v
    omega

/-- Any finite set carrying a fixed-point-free involution has even cardinality. -/
lemma even_card_of_invol {α : Type*} [DecidableEq α] (s : Finset α) (f : α → α)
    (hf_mem : ∀ x ∈ s, f x ∈ s) (hf_inv : ∀ x ∈ s, f (f x) = x) (hf_ne : ∀ x ∈ s, f x ≠ x) :
    2 ∣ s.card := by
  classical
  induction hcard : s.card using Nat.strong_induction_on generalizing s with
  | h k ih =>
    by_cases hs : s = ∅
    · subst hs; simp at hcard; subst hcard; exact dvd_zero 2
    · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hs
      have hfx : f x ∈ s := hf_mem x hx
      have hne : f x ≠ x := hf_ne x hx
      let t := (s.erase x).erase (f x)
      have ht_card : t.card + 2 = s.card := by
        have hfx_in : f x ∈ s.erase x := Finset.mem_erase.mpr ⟨hne, hfx⟩
        have h1 : t.card + 1 = (s.erase x).card := Finset.card_erase_add_one hfx_in
        have h2 : (s.erase x).card + 1 = s.card := Finset.card_erase_add_one hx
        omega
      have ht_lt : t.card < k := by omega
      have ht_even : 2 ∣ t.card := by
        apply ih t.card ht_lt t
        · intro y hy
          have hy_s : y ∈ s := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy)
          have hy_ne_x : y ≠ x := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hy)).1
          have hy_ne_fx : y ≠ f x := (Finset.mem_erase.mp hy).1
          apply Finset.mem_erase.mpr
          refine ⟨?_, Finset.mem_erase.mpr ⟨?_, hf_mem y hy_s⟩⟩
          · intro hfy_eq
            have := congrArg f hfy_eq
            rw [hf_inv y hy_s, hf_inv x hx] at this
            exact hy_ne_x this
          · intro hfy_eq
            have := congrArg f hfy_eq
            rw [hf_inv y hy_s] at this
            exact hy_ne_fx this
        · intro y hy
          exact hf_inv y (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy))
        · intro y hy
          exact hf_ne y (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy))
        · rfl
      omega

/-- If the total number of Eulerian subdigraphs of `D(π)` is `≡ 2 (mod 4)`, then
`signedEulerianCount ≠ 0`. -/
lemma signedEulerianCount_ne_zero_of_total_mod4 {n : ℕ} (hn : 0 < n)
    (π : Fin n × Fin 3 ≃ Fin (3 * n))
    (hmod4 : ((Finset.univ : Finset (Finset (CPTArc n))).filter
      (IsEulerian (cptSrc π) (cptDst hn π))).card % 4 = 2) :
    signedEulerianCount (cptSrc π) (cptDst hn π) ≠ 0 := by
  let E := (Finset.univ : Finset (Finset (CPTArc n))).filter (IsEulerian (cptSrc π) (cptDst hn π))
  change E.card % 4 = 2 at hmod4
  let EE := E.filter fun S => Even S.card
  let EO := E.filter fun S => ¬ Even S.card
  have hcard_total : Fintype.card (CPTArc n) = 6 * n := by
    simp [CPTArc]
    omega
  have hcompl_card : ∀ S : Finset (CPTArc n), Sᶜ.card + S.card = 6 * n := by
    intro S
    rw [Finset.card_compl, hcard_total]
    have hle : S.card ≤ 6 * n := by
      rw [← hcard_total]
      exact Finset.card_le_univ S
    omega
  have hcompl_even : ∀ S : Finset (CPTArc n), Even Sᶜ.card ↔ Even S.card := by
    intro S
    have hc := hcompl_card S
    rw [Nat.even_iff, Nat.even_iff]
    omega
  have hcompl_ne : ∀ S : Finset (CPTArc n), Sᶜ ≠ S := by
    intro S hEq
    have hmem : Sum.inl (⟨0, by omega⟩ : Fin (3 * n)) ∈ S ↔
        Sum.inl (⟨0, by omega⟩ : Fin (3 * n)) ∉ S := by
      conv_lhs => rw [← hEq]
      simp
    tauto
  have hEE_even : 2 ∣ EE.card := by
    apply even_card_of_invol EE (fun S => Sᶜ)
    · intro S hS
      simp only [EE, E, Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
      exact ⟨(cpt_isEulerian_compl hn π S).mpr hS.1, (hcompl_even S).mpr hS.2⟩
    · intro S _
      exact compl_compl S
    · intro S _
      exact hcompl_ne S
  have hEO_even : 2 ∣ EO.card := by
    apply even_card_of_invol EO (fun S => Sᶜ)
    · intro S hS
      simp only [EO, E, Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
      exact ⟨(cpt_isEulerian_compl hn π S).mpr hS.1, fun h => hS.2 ((hcompl_even S).mp h)⟩
    · intro S _
      exact compl_compl S
    · intro S _
      exact hcompl_ne S
  have hsum_card : EE.card + EO.card = E.card :=
    Finset.card_filter_add_card_filter_not (s := E) (fun S => Even S.card)
  have hne_card : EE.card ≠ EO.card := by
    intro hEq
    obtain ⟨k, hk⟩ := hEE_even
    omega
  have hsigned : signedEulerianCount (cptSrc π) (cptDst hn π) =
      (EE.card : ℤ) - (EO.card : ℤ) := by
    unfold signedEulerianCount
    change (∑ S ∈ E, (-1 : ℤ) ^ S.card) = (EE.card : ℤ) - (EO.card : ℤ)
    rw [← Finset.sum_filter_add_sum_filter_not E (fun S => Even S.card)]
    have h1 : (∑ S ∈ EE, (-1 : ℤ) ^ S.card) = (EE.card : ℤ) := by
      have : ∀ S ∈ EE, (-1 : ℤ) ^ S.card = 1 := fun S hS =>
        Even.neg_one_pow (Finset.mem_filter.mp hS).2
      rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, mul_one]
    have h2 : (∑ S ∈ EO, (-1 : ℤ) ^ S.card) = -(EO.card : ℤ) := by
      have : ∀ S ∈ EO, (-1 : ℤ) ^ S.card = -1 := fun S hS => by
        have hodd : Odd S.card := Nat.not_even_iff_odd.mp (Finset.mem_filter.mp hS).2
        exact Odd.neg_one_pow hodd
      rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, mul_neg_one]
    change (∑ S ∈ EE, (-1 : ℤ) ^ S.card) + (∑ S ∈ EO, (-1 : ℤ) ^ S.card) = _
    rw [h1, h2, sub_eq_add_neg]
  rw [hsigned]
  omega

end CyclePlusTrianglesOrientation

/-! ## Section 3: Triangle Factorization and Subset Expansion -/

section TriangleFactorization

/-- Cycle balance `indeg_A(v) - outdeg_A(v) ∈ {-1, 0, 1}` at vertex `v` for a cycle arc subset `A`. -/
def cycBal {n : ℕ} (hn : 0 < n) (A : Finset (Fin (3 * n))) (v : Fin (3 * n)) : ℤ :=
  (if cycPrev hn v ∈ A then (1 : ℤ) else 0) - (if v ∈ A then 1 else 0)

/-- Triangle balance `outdeg_B(j) - indeg_B(j)` at local vertex `j : Fin 3` for a triangle subset `B`. -/
def triOutMinusIn (B : Finset (Fin 3)) (j : Fin 3) : ℤ :=
  (if j ∈ B then (1 : ℤ) else 0) - (if triPrev j ∈ B then 1 else 0)

/-- Number of subsets `B ⊆ Fin 3` matching a prescribed balance triple `d : Fin 3 → ℤ`. -/
def triMatchCount (d : Fin 3 → ℤ) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin 3))).filter fun B => ∀ j : Fin 3, triOutMinusIn B j = d j).card

lemma cycBal_range {n : ℕ} (hn : 0 < n) (A : Finset (Fin (3 * n))) (v : Fin (3 * n)) :
    cycBal hn A v = -1 ∨ cycBal hn A v = 0 ∨ cycBal hn A v = 1 := by
  unfold cycBal
  by_cases h1 : cycPrev hn v ∈ A <;> by_cases h2 : v ∈ A <;> simp [h1, h2]

lemma cycBal_compl {n : ℕ} (hn : 0 < n) (A : Finset (Fin (3 * n))) (v : Fin (3 * n)) :
    cycBal hn Aᶜ v = - cycBal hn A v := by
  unfold cycBal
  by_cases h1 : cycPrev hn v ∈ A <;> by_cases h2 : v ∈ A <;> simp [h1, h2]

/-- Exact pointwise decomposition of `triMatchCount` on `{-1, 0, 1}^3`:
`triMatchCount d = 1_{∀ j, d j = 0} + 1_{∑ j, d j = 0}`. -/
lemma triMatchCount_eq_ind_add (d : Fin 3 → ℤ)
    (hd : ∀ j : Fin 3, d j = -1 ∨ d j = 0 ∨ d j = 1) :
    triMatchCount d =
      (if ∀ j : Fin 3, d j = 0 then 1 else 0) +
      (if (∑ j : Fin 3, d j) = 0 then 1 else 0) := by
  have h0 := hd 0
  have h1 := hd 1
  have h2 := hd 2
  have hfun : ∀ a b c : ℤ, d 0 = a → d 1 = b → d 2 = c →
      d = fun j : Fin 3 => match j with | ⟨0, _⟩ => a | ⟨1, _⟩ => b | ⟨2, _⟩ => c := by
    intro a b c ha hb hc
    funext j
    fin_cases j <;> assumption
  rcases h0 with h0 | h0 | h0 <;>
  rcases h1 with h1 | h1 | h1 <;>
  rcases h2 with h2 | h2 | h2 <;>
  rw [hfun _ _ _ h0 h1 h2] <;> decide

/-- Combine a cycle arc subset `A` and per-triangle arc subsets `T` into a subset of `CPTArc n`. -/
def cptOfPair {n : ℕ} (A : Finset (Fin (3 * n))) (T : Fin n → Finset (Fin 3)) :
    Finset (CPTArc n) :=
  A.map ⟨Sum.inl, Sum.inl_injective⟩ ∪
  (Finset.univ.sigma T).map
    ⟨fun p => Sum.inr (p.1, p.2), fun p q h => by
      rcases p with ⟨t1, j1⟩; rcases q with ⟨t2, j2⟩
      cases Sum.inr.inj h; rfl⟩

@[simp]
lemma mem_cptOfPair_inl {n : ℕ} (A : Finset (Fin (3 * n))) (T : Fin n → Finset (Fin 3))
    (i : Fin (3 * n)) :
    Sum.inl i ∈ cptOfPair A T ↔ i ∈ A := by
  simp [cptOfPair]

@[simp]
lemma mem_cptOfPair_inr {n : ℕ} (A : Finset (Fin (3 * n))) (T : Fin n → Finset (Fin 3))
    (t : Fin n) (j : Fin 3) :
    Sum.inr (t, j) ∈ cptOfPair A T ↔ j ∈ T t := by
  simp only [cptOfPair, Finset.mem_union, Finset.mem_map, Finset.mem_sigma, Finset.mem_univ,
    true_and, Function.Embedding.coeFn_mk]
  constructor
  · rintro (⟨_, _, h⟩ | ⟨⟨a, b⟩, hb, h⟩)
    · cases h
    · cases h
      exact hb
  · intro h
    exact Or.inr ⟨⟨t, j⟩, h, rfl⟩

lemma cptOfPair_src_card {n : ℕ} (π : Fin n × Fin 3 ≃ Fin (3 * n))
    (A : Finset (Fin (3 * n))) (T : Fin n → Finset (Fin 3)) (t : Fin n) (j : Fin 3) :
    ((cptOfPair A T).filter fun a => cptSrc π a = π (t, j)).card =
      (if π (t, j) ∈ A then 1 else 0) + (if j ∈ T t then 1 else 0) := by
  have hsub : ((cptOfPair A T).filter fun a => cptSrc π a = π (t, j)) =
      ((Finset.univ.filter fun a => cptSrc π a = π (t, j)).filter fun a => a ∈ cptOfPair A T) := by
    ext a; simp [and_comm]
  rw [hsub, cptSrc_filter_eq_pair]
  by_cases hA : π (t, j) ∈ A <;> by_cases hT : j ∈ T t <;>
    simp [Finset.filter_insert, Finset.filter_singleton, hA, hT]

lemma cptOfPair_dst_card {n : ℕ} (hn : 0 < n) (π : Fin n × Fin 3 ≃ Fin (3 * n))
    (A : Finset (Fin (3 * n))) (T : Fin n → Finset (Fin 3)) (t : Fin n) (j : Fin 3) :
    ((cptOfPair A T).filter fun a => cptDst hn π a = π (t, j)).card =
      (if cycPrev hn (π (t, j)) ∈ A then 1 else 0) + (if triPrev j ∈ T t then 1 else 0) := by
  have hsub : ((cptOfPair A T).filter fun a => cptDst hn π a = π (t, j)) =
      ((Finset.univ.filter fun a => cptDst hn π a = π (t, j)).filter fun a => a ∈ cptOfPair A T) := by
    ext a; simp [and_comm]
  rw [hsub, cptDst_filter_eq_pair]
  by_cases hA : cycPrev hn (π (t, j)) ∈ A <;> by_cases hT : triPrev j ∈ T t <;>
    simp [Finset.filter_insert, Finset.filter_singleton, hA, hT]

lemma isEulerian_cptOfPair_iff {n : ℕ} (hn : 0 < n) (π : Fin n × Fin 3 ≃ Fin (3 * n))
    (A : Finset (Fin (3 * n))) (T : Fin n → Finset (Fin 3)) :
    IsEulerian (cptSrc π) (cptDst hn π) (cptOfPair A T) ↔
      ∀ t : Fin n, ∀ j : Fin 3, triOutMinusIn (T t) j = cycBal hn A (π (t, j)) := by
  unfold IsEulerian
  constructor
  · intro h t j
    have hv := h (π (t, j))
    rw [cptOfPair_src_card, cptOfPair_dst_card] at hv
    unfold triOutMinusIn cycBal
    by_cases h1 : π (t, j) ∈ A <;> by_cases h2 : cycPrev hn (π (t, j)) ∈ A <;>
      by_cases h3 : j ∈ T t <;> by_cases h4 : triPrev j ∈ T t <;>
      simp only [h1, h2, h3, h4, ↓reduceIte] at hv ⊢ <;> omega
  · intro h v
    have htj := h (π.symm v).1 (π.symm v).2
    have hv_eq : π ((π.symm v).1, (π.symm v).2) = v := by
      rw [Prod.mk.eta, π.apply_symm_apply]
    rw [← hv_eq]
    rw [cptOfPair_src_card, cptOfPair_dst_card]
    unfold triOutMinusIn cycBal at htj
    by_cases h1 : π ((π.symm v).1, (π.symm v).2) ∈ A <;>
      by_cases h2 : cycPrev hn (π ((π.symm v).1, (π.symm v).2)) ∈ A <;>
      by_cases h3 : (π.symm v).2 ∈ T (π.symm v).1 <;>
      by_cases h4 : triPrev (π.symm v).2 ∈ T (π.symm v).1 <;>
      simp only [h1, h2, h3, h4, ↓reduceIte] at htj ⊢ <;> omega

/-- Factorization of total Eulerian subdigraph count over cycle subsets `A` and triangles `t`. -/
theorem totalEulerian_eq_sum_prod {n : ℕ} (hn : 0 < n) (π : Fin n × Fin 3 ≃ Fin (3 * n)) :
    ((Finset.univ : Finset (Finset (CPTArc n))).filter
      (IsEulerian (cptSrc π) (cptDst hn π))).card =
    ∑ A : Finset (Fin (3 * n)),
      ∏ t : Fin n, triMatchCount (fun j : Fin 3 => cycBal hn A (π (t, j))) := by
  classical
  let toPair : Finset (CPTArc n) →
      (A : Finset (Fin (3 * n))) × (Fin n → Finset (Fin 3)) := fun S =>
    ⟨Finset.univ.filter (fun i => Sum.inl i ∈ S),
     fun t => Finset.univ.filter (fun j => Sum.inr (t, j) ∈ S)⟩
  let ofPair : ((A : Finset (Fin (3 * n))) × (Fin n → Finset (Fin 3))) →
      Finset (CPTArc n) := fun p => cptOfPair p.1 p.2
  have hleft : ∀ S, ofPair (toPair S) = S := by
    intro S; ext a; cases a with
    | inl i => simp [ofPair, toPair]
    | inr p => rcases p with ⟨t, j⟩; simp [ofPair, toPair]
  have hright : ∀ p, toPair (ofPair p) = p := by
    rintro ⟨A, T⟩
    ext1
    · ext i; simp [ofPair, toPair]
    · apply heq_of_eq
      funext t; ext j; simp [ofPair, toPair]
  let validT (A : Finset (Fin (3 * n))) : Finset (Fin n → Finset (Fin 3)) :=
    Finset.univ.filter fun T => ∀ t : Fin n, ∀ j : Fin 3,
      triOutMinusIn (T t) j = cycBal hn A (π (t, j))
  have hsigma : ((Finset.univ : Finset (Finset (CPTArc n))).filter
      (IsEulerian (cptSrc π) (cptDst hn π))).card =
      ((Finset.univ : Finset (Finset (Fin (3 * n)))).sigma validT).card := by
    refine Finset.card_bij (fun S _ => toPair S) ?_ ?_ ?_
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
      simp only [Finset.mem_sigma, Finset.mem_univ, true_and, validT, Finset.mem_filter]
      have hS' : IsEulerian (cptSrc π) (cptDst hn π) (cptOfPair (toPair S).1 (toPair S).2) := by
        simpa [ofPair] using (by rwa [hleft S] : IsEulerian (cptSrc π) (cptDst hn π) (ofPair (toPair S)))
      exact (isEulerian_cptOfPair_iff hn π (toPair S).1 (toPair S).2).mp hS'
    · intro S₁ _ S₂ _ h
      have := congrArg ofPair h
      rwa [hleft S₁, hleft S₂] at this
    · intro p hp
      simp only [Finset.mem_sigma, Finset.mem_univ, true_and, validT, Finset.mem_filter] at hp
      refine ⟨ofPair p, ?_, hright p⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (isEulerian_cptOfPair_iff hn π p.1 p.2).mpr hp
  rw [hsigma, Finset.card_sigma]
  refine Finset.sum_congr rfl fun A _ => ?_
  have hpi : validT A = Fintype.piFinset fun t : Fin n =>
      (Finset.univ : Finset (Finset (Fin 3))).filter fun B =>
        ∀ j : Fin 3, triOutMinusIn B j = cycBal hn A (π (t, j)) := by
    ext T
    simp [validT, Fintype.mem_piFinset]
  rw [hpi, Fintype.card_piFinset]
  rfl

/-- Cycle subsets `A` satisfying the contracted-triangle balance conditions indexed by `S`. -/
def subsetBalSet {n : ℕ} (hn : 0 < n) (π : Fin n × Fin 3 ≃ Fin (3 * n)) (S : Finset (Fin n)) :
    Finset (Finset (Fin (3 * n))) :=
  Finset.univ.filter fun A =>
    (∀ t ∈ S, (∑ j : Fin 3, cycBal hn A (π (t, j))) = 0) ∧
    (∀ t ∉ S, ∀ j : Fin 3, cycBal hn A (π (t, j)) = 0)

/-- Exact expansion of total Eulerian subdigraph count over subsets `S ⊆ Fin n`. -/
theorem totalEulerian_eq_sum_subsetBal {n : ℕ} (hn : 0 < n) (π : Fin n × Fin 3 ≃ Fin (3 * n)) :
    ((Finset.univ : Finset (Finset (CPTArc n))).filter
      (IsEulerian (cptSrc π) (cptDst hn π))).card =
    ∑ S : Finset (Fin n), (subsetBalSet hn π S).card := by
  rw [totalEulerian_eq_sum_prod hn π]
  have hprod : ∀ A : Finset (Fin (3 * n)),
      (∏ t : Fin n, triMatchCount (fun j : Fin 3 => cycBal hn A (π (t, j)))) =
      ∑ S : Finset (Fin n),
        if (∀ t ∈ S, (∑ j : Fin 3, cycBal hn A (π (t, j))) = 0) ∧
           (∀ t ∉ S, ∀ j : Fin 3, cycBal hn A (π (t, j)) = 0)
        then 1 else 0 := by
    intro A
    have hpt : ∀ t : Fin n,
        triMatchCount (fun j : Fin 3 => cycBal hn A (π (t, j))) =
        (if (∑ j : Fin 3, cycBal hn A (π (t, j))) = 0 then 1 else 0) +
        (if ∀ j : Fin 3, cycBal hn A (π (t, j)) = 0 then 1 else 0) := fun t => by
      rw [triMatchCount_eq_ind_add _ (fun j => cycBal_range hn A (π (t, j))), add_comm]
    simp_rw [hpt]
    rw [Finset.prod_add]
    have hpow : (Finset.univ : Finset (Fin n)).powerset = Finset.univ := by
      ext S; simp
    rw [hpow]
    refine Finset.sum_congr rfl fun S _ => ?_
    by_cases hcond : (∀ t ∈ S, (∑ j : Fin 3, cycBal hn A (π (t, j))) = 0) ∧
        (∀ t ∉ S, ∀ j : Fin 3, cycBal hn A (π (t, j)) = 0)
    · rw [ite_eq_left_iff.mpr fun h => absurd hcond h]
      have h1 : (∏ t ∈ S, if (∑ j : Fin 3, cycBal hn A (π (t, j))) = 0 then 1 else 0) = 1 :=
        Finset.prod_eq_one fun t ht => by simp only [hcond.1 t ht, ↓reduceIte]
      have h2 : (∏ t ∈ Finset.univ \ S, if ∀ j : Fin 3, cycBal hn A (π (t, j)) = 0 then 1 else 0) = 1 :=
        Finset.prod_eq_one fun t ht => by
          simp only [hcond.2 t (Finset.mem_sdiff.mp ht).2, implies_true, ↓reduceIte]
      rw [h1, h2, mul_one]
    · rw [ite_eq_right_iff.mpr fun h => absurd h hcond]
      by_cases h1 : ∀ t ∈ S, (∑ j : Fin 3, cycBal hn A (π (t, j))) = 0
      · have h2 : ¬ ∀ t ∉ S, ∀ j : Fin 3, cycBal hn A (π (t, j)) = 0 := fun h => hcond ⟨h1, h⟩
        push Not at h2
        obtain ⟨t, htS, j, hj⟩ := h2
        have ht_mem : t ∈ Finset.univ \ S := Finset.mem_sdiff.mpr ⟨Finset.mem_univ t, htS⟩
        have hz : (∏ x ∈ Finset.univ \ S, if ∀ j : Fin 3, cycBal hn A (π (x, j)) = 0 then 1 else 0) = 0 := by
          apply Finset.prod_eq_zero ht_mem
          have hnot : ¬ ∀ j : Fin 3, cycBal hn A (π (t, j)) = 0 := fun hall => hj (hall j)
          simp only [hnot, ↓reduceIte]
        rw [hz, mul_zero]
      · push Not at h1
        obtain ⟨t, htS, htne⟩ := h1
        have hz : (∏ x ∈ S, if (∑ j : Fin 3, cycBal hn A (π (x, j))) = 0 then 1 else 0) = 0 := by
          apply Finset.prod_eq_zero htS
          simp only [htne, ↓reduceIte]
        rw [hz, zero_mul]
  simp_rw [hprod]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => ?_
  simp only [subsetBalSet, Finset.card_filter]

/-- For `S = ∅`, only `A = ∅` and `A = univ` have zero balance at every cycle vertex. -/
theorem card_subsetBalSet_empty {n : ℕ} (hn : 0 < n) (π : Fin n × Fin 3 ≃ Fin (3 * n)) :
    (subsetBalSet hn π ∅).card = 2 := by
  have hset : subsetBalSet hn π ∅ = ({∅, Finset.univ} : Finset (Finset (Fin (3 * n)))) := by
    ext A
    simp only [subsetBalSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
      false_implies, not_false_eq_true, true_implies, implies_true, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hall
      have hbal0 : ∀ v : Fin (3 * n), cycBal hn A v = 0 := by
        intro v
        have h := hall (π.symm v).1 (π.symm v).2
        rwa [Prod.mk.eta, π.apply_symm_apply] at h
      have hstep : ∀ (k : ℕ) (hk : k < 3 * n),
          ((⟨k, hk⟩ : Fin (3 * n)) ∈ A) ↔ ((⟨0, by omega⟩ : Fin (3 * n)) ∈ A) := by
        intro k hk
        induction k with
        | zero => rfl
        | succ k ih =>
          have hk' : k < 3 * n := by omega
          have hprev : cycPrev hn ⟨k + 1, hk⟩ = ⟨k, hk'⟩ := by
            ext; simp only [cycPrev]
            have h1 : k + 1 + (3 * n - 1) = k + 3 * n := by omega
            rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hk']
          have hb := hbal0 ⟨k + 1, hk⟩
          unfold cycBal at hb
          rw [hprev] at hb
          have heq : ((⟨k + 1, hk⟩ : Fin (3 * n)) ∈ A) ↔ ((⟨k, hk'⟩ : Fin (3 * n)) ∈ A) := by
            by_cases h1 : (⟨k, hk'⟩ : Fin (3 * n)) ∈ A <;>
              by_cases h2 : (⟨k + 1, hk⟩ : Fin (3 * n)) ∈ A <;> simp_all
          exact heq.trans (ih hk')
      by_cases h0 : (⟨0, by omega⟩ : Fin (3 * n)) ∈ A
      · right
        ext ⟨k, hk⟩
        simp [(hstep k hk).mpr h0]
      · left
        ext ⟨k, hk⟩
        simp only [Finset.notMem_empty, iff_false]
        exact fun h => h0 ((hstep k hk).mp h)
    · rintro (rfl | rfl) t j <;> simp [cycBal]
  rw [hset, Finset.card_pair]
  intro hEq
  have hmem : (⟨0, by omega⟩ : Fin (3 * n)) ∈ (∅ : Finset (Fin (3 * n))) := by
    rw [hEq]; exact Finset.mem_univ _
  exact Finset.notMem_empty _ hmem

end TriangleFactorization

/-! ## Section 4: Chevalley–Warning Divisibility by 4 for Nonempty `S` -/

section ChevalleyWarningMod4

/-- Over `ZMod 2`, two 3-bit triples have equal integer Hamming weight iff their sum and
second elementary symmetric polynomial coincide in `ZMod 2`. -/
lemma zmod2_sum3_eq_iff (a0 a1 a2 b0 b1 b2 : ZMod 2) :
    (a0.val : ℤ) + a1.val + a2.val = (b0.val : ℤ) + b1.val + b2.val ↔
      (a0 + a1 + a2 + b0 + b1 + b2 = 0) ∧
      (a0 * a1 + a1 * a2 + a2 * a0 + (b0 * b1 + b1 * b2 + b2 * b0) = 0) := by
  fin_cases a0 <;> fin_cases a1 <;> fin_cases a2 <;>
    fin_cases b0 <;> fin_cases b1 <;> fin_cases b2 <;> decide

/-- Free variable type for Chevalley–Warning: all vertices except `0` (`3n - 1` variables). -/
abbrev CWVar {n : ℕ} (hn : 0 < n) := { v : Fin (3 * n) // v ≠ ⟨0, by omega⟩ }

/-- Variable polynomial assigned to cycle vertex `v`, with `0 ↦ 0` and `v ≠ 0 ↦ X ⟨v, h⟩`. -/
noncomputable def cwVarOf {n : ℕ} (hn : 0 < n) (v : Fin (3 * n)) : MvPolynomial (CWVar hn) (ZMod 2) :=
  if h : v = ⟨0, by omega⟩ then 0 else MvPolynomial.X ⟨v, h⟩

/-- Extension of an assignment `x : CWVar hn → ZMod 2` to all `Fin (3 * n)` with `0 ↦ 0`. -/
def cwExt0 {n : ℕ} (hn : 0 < n) (x : CWVar hn → ZMod 2) (v : Fin (3 * n)) : ZMod 2 :=
  if h : v = ⟨0, by omega⟩ then 0 else x ⟨v, h⟩

lemma cwVarOf_totalDegree_le {n : ℕ} (hn : 0 < n) (v : Fin (3 * n)) :
    (cwVarOf hn v).totalDegree ≤ 1 := by
  unfold cwVarOf
  split_ifs
  · simp
  · simp [MvPolynomial.totalDegree_X]

lemma cwVarOf_eval {n : ℕ} (hn : 0 < n) (x : CWVar hn → ZMod 2) (v : Fin (3 * n)) :
    MvPolynomial.eval x (cwVarOf hn v) = cwExt0 hn x v := by
  unfold cwVarOf cwExt0
  split_ifs <;> simp

/-- Second elementary symmetric polynomial `ab + bc + ca` over `ZMod 2`. -/
noncomputable def cwE2 {n : ℕ} (hn : 0 < n) (a b c : MvPolynomial (CWVar hn) (ZMod 2)) :
    MvPolynomial (CWVar hn) (ZMod 2) :=
  a * b + b * c + c * a

/-- Linear parity polynomial `P_t` for triangle `t`. -/
noncomputable def cwPPoly {n : ℕ} (hn : 0 < n) (π : Fin n × Fin 3 ≃ Fin (3 * n)) (t : Fin n) :
    MvPolynomial (CWVar hn) (ZMod 2) :=
  ∑ j : Fin 3, (cwVarOf hn (cycPrev hn (π (t, j))) + cwVarOf hn (π (t, j)))

/-- Quadratic carry polynomial `Q_t` for triangle `t`. -/
noncomputable def cwQPoly {n : ℕ} (hn : 0 < n) (π : Fin n × Fin 3 ≃ Fin (3 * n)) (t : Fin n) :
    MvPolynomial (CWVar hn) (ZMod 2) :=
  cwE2 hn (cwVarOf hn (cycPrev hn (π (t, 0)))) (cwVarOf hn (cycPrev hn (π (t, 1))))
    (cwVarOf hn (cycPrev hn (π (t, 2)))) +
  cwE2 hn (cwVarOf hn (π (t, 0))) (cwVarOf hn (π (t, 1))) (cwVarOf hn (π (t, 2)))

/-- Polynomial system indexed by `(Fin n × Fin 3) ⊕ (Fin n ⊕ Fin n)`. -/
noncomputable def cwEqPoly {n : ℕ} (hn : 0 < n) (π : Fin n × Fin 3 ≃ Fin (3 * n)) :
    ((Fin n × Fin 3) ⊕ (Fin n ⊕ Fin n)) → MvPolynomial (CWVar hn) (ZMod 2)
  | Sum.inl (t, j) => cwVarOf hn (cycPrev hn (π (t, j))) + cwVarOf hn (π (t, j))
  | Sum.inr (Sum.inl t) => cwPPoly hn π t
  | Sum.inr (Sum.inr t) => cwQPoly hn π t

/-- Embedding of external vertex equations into the combined index type. -/
def cwEmbInl (n : ℕ) : (Fin n × Fin 3) ↪ ((Fin n × Fin 3) ⊕ (Fin n ⊕ Fin n)) :=
  ⟨Sum.inl, Sum.inl_injective⟩

/-- Embedding of linear parity equations `P_t` into the combined index type. -/
def cwEmbP (n : ℕ) : Fin n ↪ ((Fin n × Fin 3) ⊕ (Fin n ⊕ Fin n)) :=
  ⟨fun t => Sum.inr (Sum.inl t), fun _ _ h => Sum.inl.inj (Sum.inr.inj h)⟩

/-- Embedding of quadratic carry equations `Q_t` into the combined index type. -/
def cwEmbQ (n : ℕ) : Fin n ↪ ((Fin n × Fin 3) ⊕ (Fin n ⊕ Fin n)) :=
  ⟨fun t => Sum.inr (Sum.inr t), fun _ _ h => Sum.inr.inj (Sum.inr.inj h)⟩

@[simp] lemma cwEmbInl_apply (n : ℕ) (p : Fin n × Fin 3) : cwEmbInl n p = Sum.inl p := rfl
@[simp] lemma cwEmbP_apply (n : ℕ) (t : Fin n) : cwEmbP n t = Sum.inr (Sum.inl t) := rfl
@[simp] lemma cwEmbQ_apply (n : ℕ) (t : Fin n) : cwEmbQ n t = Sum.inr (Sum.inr t) := rfl

/-- Active equation index set for nonempty `S` with redundant triangle `t₀ ∈ S` dropped. -/
def cwEqSet {n : ℕ} (S : Finset (Fin n)) (t₀ : Fin n) :
    Finset ((Fin n × Fin 3) ⊕ (Fin n ⊕ Fin n)) :=
  ((Sᶜ ×ˢ (Finset.univ : Finset (Fin 3))).map (cwEmbInl n) ∪
   (S.erase t₀).map (cwEmbP n)) ∪
  (S.erase t₀).map (cwEmbQ n)

lemma mem_cwEqSet_inl {n : ℕ} {S : Finset (Fin n)} {t₀ : Fin n} {p : Fin n × Fin 3} :
    Sum.inl p ∈ cwEqSet S t₀ ↔ p.1 ∉ S := by
  simp [cwEqSet]

lemma mem_cwEqSet_inr_inl {n : ℕ} {S : Finset (Fin n)} {t₀ t : Fin n} :
    Sum.inr (Sum.inl t) ∈ cwEqSet S t₀ ↔ t ∈ S.erase t₀ := by
  simp [cwEqSet]

lemma mem_cwEqSet_inr_inr {n : ℕ} {S : Finset (Fin n)} {t₀ t : Fin n} :
    Sum.inr (Sum.inr t) ∈ cwEqSet S t₀ ↔ t ∈ S.erase t₀ := by
  simp [cwEqSet]

lemma cw_deg_sum_lt {n : ℕ} (hn : 0 < n) (π : Fin n × Fin 3 ≃ Fin (3 * n))
    {S : Finset (Fin n)} {t₀ : Fin n} (ht₀ : t₀ ∈ S) :
    (∑ e ∈ cwEqSet S t₀, (cwEqPoly hn π e).totalDegree) < Fintype.card (CWVar hn) := by
  have hdeg_add : ∀ u v : Fin (3 * n), (cwVarOf hn u + cwVarOf hn v).totalDegree ≤ 1 := fun u v =>
    le_trans (MvPolynomial.totalDegree_add _ _)
      (max_le (cwVarOf_totalDegree_le hn u) (cwVarOf_totalDegree_le hn v))
  have hdeg_P : ∀ t : Fin n, (cwPPoly hn π t).totalDegree ≤ 1 := by
    intro t
    unfold cwPPoly
    refine le_trans (MvPolynomial.totalDegree_finsetSum _ _) ?_
    rw [Finset.sup_le_iff]
    intro j _
    exact hdeg_add _ _
  have hdeg_mul : ∀ u v : Fin (3 * n), (cwVarOf hn u * cwVarOf hn v).totalDegree ≤ 2 := fun u v =>
    le_trans (MvPolynomial.totalDegree_mul _ _)
      (add_le_add (cwVarOf_totalDegree_le hn u) (cwVarOf_totalDegree_le hn v))
  have hdeg_e2 : ∀ u v w : Fin (3 * n),
      (cwE2 hn (cwVarOf hn u) (cwVarOf hn v) (cwVarOf hn w)).totalDegree ≤ 2 := by
    intro u v w
    unfold cwE2
    refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le ?_ (hdeg_mul w u))
    exact le_trans (MvPolynomial.totalDegree_add _ _) (max_le (hdeg_mul u v) (hdeg_mul v w))
  have hdeg_Q : ∀ t : Fin n, (cwQPoly hn π t).totalDegree ≤ 2 := fun t =>
    le_trans (MvPolynomial.totalDegree_add _ _) (max_le (hdeg_e2 _ _ _) (hdeg_e2 _ _ _))
  have hdisj1 : Disjoint
      ((Sᶜ ×ˢ (Finset.univ : Finset (Fin 3))).map (cwEmbInl n))
      ((S.erase t₀).map (cwEmbP n)) := by
    rw [Finset.disjoint_left]
    intro e he1 he2
    simp only [Finset.mem_map, cwEmbInl_apply, cwEmbP_apply] at he1 he2
    obtain ⟨_, _, rfl⟩ := he1
    obtain ⟨_, _, h⟩ := he2
    cases h
  have hdisj2 : Disjoint
      ((Sᶜ ×ˢ (Finset.univ : Finset (Fin 3))).map (cwEmbInl n) ∪
       (S.erase t₀).map (cwEmbP n))
      ((S.erase t₀).map (cwEmbQ n)) := by
    rw [Finset.disjoint_left]
    intro e he1 he2
    simp only [Finset.mem_union, Finset.mem_map, cwEmbInl_apply, cwEmbP_apply,
      cwEmbQ_apply] at he1 he2
    obtain ⟨_, _, h2⟩ := he2
    rcases he1 with ⟨_, _, h1⟩ | ⟨_, _, h1⟩
    · cases h1.trans h2.symm
    · cases h1.trans h2.symm
  have hsum_split : (∑ e ∈ cwEqSet S t₀, (cwEqPoly hn π e).totalDegree) =
      (∑ p ∈ Sᶜ ×ˢ (Finset.univ : Finset (Fin 3)), (cwEqPoly hn π (Sum.inl p)).totalDegree) +
      (∑ t ∈ S.erase t₀, (cwPPoly hn π t).totalDegree) +
      (∑ t ∈ S.erase t₀, (cwQPoly hn π t).totalDegree) := by
    unfold cwEqSet
    rw [Finset.sum_union hdisj2, Finset.sum_union hdisj1,
      Finset.sum_map, Finset.sum_map, Finset.sum_map]
    rfl
  have hb1 : (∑ p ∈ Sᶜ ×ˢ (Finset.univ : Finset (Fin 3)),
      (cwEqPoly hn π (Sum.inl p)).totalDegree) ≤ 3 * (n - S.card) := by
    calc
      (∑ p ∈ Sᶜ ×ˢ (Finset.univ : Finset (Fin 3)), (cwEqPoly hn π (Sum.inl p)).totalDegree)
          ≤ ∑ _p ∈ Sᶜ ×ˢ (Finset.univ : Finset (Fin 3)), 1 := by
            apply Finset.sum_le_sum
            rintro ⟨t, j⟩ _; exact hdeg_add _ _
      _ = (Sᶜ ×ˢ (Finset.univ : Finset (Fin 3))).card := by simp
      _ = 3 * (n - S.card) := by
            rw [Finset.card_product, Finset.card_compl, Finset.card_fin, Fintype.card_fin, mul_comm]
  have hb2 : (∑ t ∈ S.erase t₀, (cwPPoly hn π t).totalDegree) ≤ S.card - 1 := by
    calc
      (∑ t ∈ S.erase t₀, (cwPPoly hn π t).totalDegree) ≤ ∑ _t ∈ S.erase t₀, 1 :=
        Finset.sum_le_sum fun t _ => hdeg_P t
      _ = (S.erase t₀).card := by simp
      _ = S.card - 1 := Finset.card_erase_of_mem ht₀
  have hb3 : (∑ t ∈ S.erase t₀, (cwQPoly hn π t).totalDegree) ≤ 2 * (S.card - 1) := by
    calc
      (∑ t ∈ S.erase t₀, (cwQPoly hn π t).totalDegree) ≤ ∑ _t ∈ S.erase t₀, 2 :=
        Finset.sum_le_sum fun t _ => hdeg_Q t
      _ = (S.erase t₀).card * 2 := by simp
      _ = 2 * (S.card - 1) := by rw [Finset.card_erase_of_mem ht₀, mul_comm]
  have hcard_σ : Fintype.card (CWVar hn) = 3 * n - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique]
  have hS_pos : 1 ≤ S.card := Finset.card_pos.mpr ⟨t₀, ht₀⟩
  have hS_le : S.card ≤ n := by
    have := Finset.card_le_univ S
    rwa [Fintype.card_fin] at this
  rw [hsum_split, hcard_σ]
  omega

lemma cw_eval_P {n : ℕ} (hn : 0 < n) (π : Fin n × Fin 3 ≃ Fin (3 * n))
    (x : CWVar hn → ZMod 2) (t : Fin n) :
    MvPolynomial.eval x (cwPPoly hn π t) =
      cwExt0 hn x (cycPrev hn (π (t, 0))) + cwExt0 hn x (cycPrev hn (π (t, 1))) +
      cwExt0 hn x (cycPrev hn (π (t, 2))) + cwExt0 hn x (π (t, 0)) +
      cwExt0 hn x (π (t, 1)) + cwExt0 hn x (π (t, 2)) := by
  unfold cwPPoly
  rw [map_sum, Fin.sum_univ_three]
  simp only [map_add, cwVarOf_eval]
  ring

lemma cw_eval_Q {n : ℕ} (hn : 0 < n) (π : Fin n × Fin 3 ≃ Fin (3 * n))
    (x : CWVar hn → ZMod 2) (t : Fin n) :
    MvPolynomial.eval x (cwQPoly hn π t) =
      (cwExt0 hn x (cycPrev hn (π (t, 0))) * cwExt0 hn x (cycPrev hn (π (t, 1))) +
       cwExt0 hn x (cycPrev hn (π (t, 1))) * cwExt0 hn x (cycPrev hn (π (t, 2))) +
       cwExt0 hn x (cycPrev hn (π (t, 2))) * cwExt0 hn x (cycPrev hn (π (t, 0)))) +
      (cwExt0 hn x (π (t, 0)) * cwExt0 hn x (π (t, 1)) +
       cwExt0 hn x (π (t, 1)) * cwExt0 hn x (π (t, 2)) +
       cwExt0 hn x (π (t, 2)) * cwExt0 hn x (π (t, 0))) := by
  unfold cwQPoly cwE2
  simp only [map_add, map_mul, cwVarOf_eval]

lemma zmod2_ite_eq_val (z : ZMod 2) : (if z = 1 then (1 : ℤ) else 0) = (z.val : ℤ) := by
  fin_cases z <;> decide

lemma zmod2_eq_zero_of_ne_one (z : ZMod 2) (h : z ≠ 1) : (0 : ZMod 2) = z := by
  fin_cases z
  · rfl
  · exact absurd rfl h

lemma zmod2_add_self (z : ZMod 2) : z + z = 0 := by
  fin_cases z <;> decide

lemma zmod2_val_sub_eq_zero_iff (a b : ZMod 2) :
    (a.val : ℤ) - (b.val : ℤ) = 0 ↔ a + b = 0 := by
  fin_cases a <;> fin_cases b <;> decide

lemma sum_cycPrev {n : ℕ} {M : Type*} [AddCommMonoid M] (hn : 0 < n) (f : Fin (3 * n) → M) :
    (∑ v : Fin (3 * n), f (cycPrev hn v)) = ∑ v : Fin (3 * n), f v :=
  Equiv.sum_comp (cycPrevEquiv hn) f

lemma cw_card_half0_eq_solutions {n : ℕ} (hn : 0 < n) (π : Fin n × Fin 3 ≃ Fin (3 * n))
    {S : Finset (Fin n)} {t₀ : Fin n} (ht₀ : t₀ ∈ S) :
    ((subsetBalSet hn π S).filter fun A => (⟨0, by omega⟩ : Fin (3 * n)) ∉ A).card =
      Nat.card { x : CWVar hn → ZMod 2 // ∀ e ∈ cwEqSet S t₀, MvPolynomial.eval x (cwEqPoly hn π e) = 0 } := by
  let zeroV : Fin (3 * n) := ⟨0, by omega⟩
  let Half0 := (subsetBalSet hn π S).filter fun A => zeroV ∉ A
  change Half0.card = _
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  let toVec (A : Finset (Fin (3 * n))) : CWVar hn → ZMod 2 := fun v => if v.1 ∈ A then 1 else 0
  let ofVec (x : CWVar hn → ZMod 2) : Finset (Fin (3 * n)) := Finset.univ.filter fun v => cwExt0 hn x v = 1
  have hval_ext0 : ∀ (x : CWVar hn → ZMod 2) (v : Fin (3 * n)),
      (if v ∈ ofVec x then (1 : ℤ) else 0) = ((cwExt0 hn x v).val : ℤ) := by
    intro x v
    simp only [ofVec, Finset.mem_filter, Finset.mem_univ, true_and]
    exact zmod2_ite_eq_val (cwExt0 hn x v)
  have hcycBal_ofVec : ∀ (x : CWVar hn → ZMod 2) (v : Fin (3 * n)),
      cycBal hn (ofVec x) v = ((cwExt0 hn x (cycPrev hn v)).val : ℤ) - ((cwExt0 hn x v).val : ℤ) := by
    intro x v
    unfold cycBal
    rw [hval_ext0, hval_ext0]
  have hsum_bal_ofVec : ∀ (x : CWVar hn → ZMod 2) (t : Fin n),
      (∑ j : Fin 3, cycBal hn (ofVec x) (π (t, j))) =
        (((cwExt0 hn x (cycPrev hn (π (t, 0)))).val : ℤ) + (cwExt0 hn x (cycPrev hn (π (t, 1)))).val +
          (cwExt0 hn x (cycPrev hn (π (t, 2)))).val) -
        (((cwExt0 hn x (π (t, 0))).val : ℤ) + (cwExt0 hn x (π (t, 1))).val +
          (cwExt0 hn x (π (t, 2))).val) := by
    intro x t
    rw [Fin.sum_univ_three]
    simp only [hcycBal_ofVec]
    ring
  have hleft_inv : ∀ A ∈ Half0, ofVec (toVec A) = A := by
    intro A hA
    have h0A : zeroV ∉ A := (Finset.mem_filter.mp hA).2
    ext v
    simp only [ofVec, Finset.mem_filter, Finset.mem_univ, true_and, cwExt0, toVec]
    by_cases hv : v = zeroV
    · subst hv; simp [zeroV, h0A]
    · simp only [zeroV] at hv
      simp only [hv, ↓reduceDIte]
      by_cases hvA : v ∈ A <;> simp [hvA]
  have hright_inv : ∀ x : CWVar hn → ZMod 2, toVec (ofVec x) = x := by
    intro x
    funext ⟨v, hv⟩
    have hmem : v ∈ ofVec x ↔ x ⟨v, hv⟩ = 1 := by
      dsimp only [ofVec]
      rw [Finset.mem_filter]
      simp only [Finset.mem_univ, true_and, cwExt0, hv, ↓reduceDIte]
    dsimp only [toVec]
    by_cases hx1 : x ⟨v, hv⟩ = 1
    · rw [ite_eq_left_iff.mpr fun h => absurd (hmem.mpr hx1) h, hx1]
    · rw [ite_eq_right_iff.mpr fun h => absurd (hmem.mp h) hx1]
      exact zmod2_eq_zero_of_ne_one (x ⟨v, hv⟩) hx1
  refine Finset.card_bij (fun A _ => toVec A) ?_ ?_ ?_
  · intro A hA
    have hA_eq := hleft_inv A hA
    have hA_sub := (Finset.mem_filter.mp hA).1
    simp only [subsetBalSet, Finset.mem_filter, Finset.mem_univ, true_and] at hA_sub
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro e he
    cases e with
    | inl p =>
      rcases p with ⟨t, j⟩
      have htS : t ∉ S := mem_cwEqSet_inl.mp he
      have hb := hA_sub.2 t htS j
      rw [← hA_eq, hcycBal_ofVec] at hb
      unfold cwEqPoly
      rw [map_add, cwVarOf_eval, cwVarOf_eval]
      exact (zmod2_val_sub_eq_zero_iff _ _).mp hb
    | inr q =>
      cases q with
      | inl t =>
        have htS : t ∈ S := Finset.mem_of_mem_erase (mem_cwEqSet_inr_inl.mp he)
        have hs := hA_sub.1 t htS
        rw [← hA_eq, hsum_bal_ofVec, sub_eq_zero] at hs
        unfold cwEqPoly
        rw [cw_eval_P]
        exact ((zmod2_sum3_eq_iff _ _ _ _ _ _).mp hs).1
      | inr t =>
        have htS : t ∈ S := Finset.mem_of_mem_erase (mem_cwEqSet_inr_inr.mp he)
        have hs := hA_sub.1 t htS
        rw [← hA_eq, hsum_bal_ofVec, sub_eq_zero] at hs
        unfold cwEqPoly
        rw [cw_eval_Q]
        exact ((zmod2_sum3_eq_iff _ _ _ _ _ _).mp hs).2
  · intro A₁ hA₁ A₂ hA₂ hEq
    have := congrArg ofVec hEq
    rwa [hleft_inv A₁ hA₁, hleft_inv A₂ hA₂] at this
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    refine ⟨ofVec x, ?_, hright_inv x⟩
    have h0_not : zeroV ∉ ofVec x := by
      simp [ofVec, cwExt0, zeroV]
    have hout : ∀ t ∉ S, ∀ j : Fin 3, cycBal hn (ofVec x) (π (t, j)) = 0 := by
      intro t htS j
      have heq := hx (Sum.inl (t, j)) (mem_cwEqSet_inl.mpr htS)
      unfold cwEqPoly at heq
      rw [map_add, cwVarOf_eval, cwVarOf_eval] at heq
      rw [hcycBal_ofVec]
      exact (zmod2_val_sub_eq_zero_iff _ _).mpr heq
    have hP_erase : ∀ t ∈ S.erase t₀, MvPolynomial.eval x (cwPPoly hn π t) = 0 := fun t ht =>
      hx (Sum.inr (Sum.inl t)) (mem_cwEqSet_inr_inl.mpr ht)
    have hQ_erase : ∀ t ∈ S.erase t₀, MvPolynomial.eval x (cwQPoly hn π t) = 0 := fun t ht =>
      hx (Sum.inr (Sum.inr t)) (mem_cwEqSet_inr_inr.mpr ht)
    -- Redundancy of `P_{t₀}` via global `ZMod 2` balance conservation.
    have hP_all : ∀ t : Fin n, MvPolynomial.eval x (cwPPoly hn π t) = 0 := by
      have hP_out : ∀ t ∉ S, MvPolynomial.eval x (cwPPoly hn π t) = 0 := by
        intro t htS
        unfold cwPPoly
        rw [map_sum]
        apply Finset.sum_eq_zero
        intro j _
        exact hx (Sum.inl (t, j)) (mem_cwEqSet_inl.mpr htS)
      have hsum_all_P : (∑ t : Fin n, MvPolynomial.eval x (cwPPoly hn π t)) = 0 := by
        have h1 : (∑ t : Fin n, MvPolynomial.eval x (cwPPoly hn π t)) =
            ∑ p : Fin n × Fin 3, (cwExt0 hn x (cycPrev hn (π p)) + cwExt0 hn x (π p)) := by
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun t _ => ?_
          unfold cwPPoly
          rw [map_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_add, cwVarOf_eval, cwVarOf_eval]
        rw [h1, Equiv.sum_comp π (fun v => cwExt0 hn x (cycPrev hn v) + cwExt0 hn x v),
          Finset.sum_add_distrib, sum_cycPrev hn (fun v => cwExt0 hn x v)]
        exact zmod2_add_self _
      have hP_t0 : MvPolynomial.eval x (cwPPoly hn π t₀) = 0 := by
        have hdecomp : (∑ t : Fin n, MvPolynomial.eval x (cwPPoly hn π t)) =
            MvPolynomial.eval x (cwPPoly hn π t₀) +
            (∑ t ∈ Finset.univ.erase t₀, MvPolynomial.eval x (cwPPoly hn π t)) :=
          (Finset.add_sum_erase _ _ (Finset.mem_univ t₀)).symm
        have hrest0 : (∑ t ∈ Finset.univ.erase t₀, MvPolynomial.eval x (cwPPoly hn π t)) = 0 := by
          apply Finset.sum_eq_zero
          intro t ht
          by_cases htS : t ∈ S
          · exact hP_erase t (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp ht).1, htS⟩)
          · exact hP_out t htS
        rw [hdecomp, hrest0, add_zero] at hsum_all_P
        exact hsum_all_P
      intro t
      by_cases hteq : t = t₀
      · subst hteq; exact hP_t0
      · by_cases htS : t ∈ S
        · exact hP_erase t (Finset.mem_erase.mpr ⟨hteq, htS⟩)
        · exact hP_out t htS
    -- Redundancy of `Q_{t₀}` via global integer balance conservation.
    have hQ_t0 : MvPolynomial.eval x (cwQPoly hn π t₀) = 0 := by
      have hglobal_int : (∑ t : Fin n, ∑ j : Fin 3, cycBal hn (ofVec x) (π (t, j))) = 0 := by
        rw [← Fintype.sum_prod_type', Equiv.sum_comp π (fun v => cycBal hn (ofVec x) v)]
        simp only [hcycBal_ofVec, Finset.sum_sub_distrib]
        rw [sum_cycPrev hn (fun v => ((cwExt0 hn x v).val : ℤ)), sub_self]
      have hsum_t_zero : ∀ t ≠ t₀, (∑ j : Fin 3, cycBal hn (ofVec x) (π (t, j))) = 0 := by
        intro t hne
        by_cases htS : t ∈ S
        · rw [hsum_bal_ofVec, sub_eq_zero]
          have hp := hP_all t
          have hq := hQ_erase t (Finset.mem_erase.mpr ⟨hne, htS⟩)
          rw [cw_eval_P] at hp
          rw [cw_eval_Q] at hq
          exact (zmod2_sum3_eq_iff _ _ _ _ _ _).mpr ⟨hp, hq⟩
        · exact Finset.sum_eq_zero fun j _ => hout t htS j
      have hbal_t0 : (∑ j : Fin 3, cycBal hn (ofVec x) (π (t₀, j))) = 0 := by
        have hdecomp : (∑ t : Fin n, ∑ j : Fin 3, cycBal hn (ofVec x) (π (t, j))) =
            (∑ j : Fin 3, cycBal hn (ofVec x) (π (t₀, j))) +
            ∑ t ∈ Finset.univ.erase t₀, ∑ j : Fin 3, cycBal hn (ofVec x) (π (t, j)) :=
          (Finset.add_sum_erase _ _ (Finset.mem_univ t₀)).symm
        have hrest0 : (∑ t ∈ Finset.univ.erase t₀, ∑ j : Fin 3, cycBal hn (ofVec x) (π (t, j))) = 0 :=
          Finset.sum_eq_zero fun t ht => hsum_t_zero t (Finset.mem_erase.mp ht).1
        rw [hdecomp, hrest0, add_zero] at hglobal_int
        exact hglobal_int
      rw [hsum_bal_ofVec, sub_eq_zero] at hbal_t0
      rw [cw_eval_Q]
      exact ((zmod2_sum3_eq_iff _ _ _ _ _ _).mp hbal_t0).2
    simp only [Half0, subsetBalSet, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨⟨?_, hout⟩, h0_not⟩
    intro t htS
    rw [hsum_bal_ofVec, sub_eq_zero]
    have hp := hP_all t
    have hq : MvPolynomial.eval x (cwQPoly hn π t) = 0 := by
      by_cases hteq : t = t₀
      · subst hteq; exact hQ_t0
      · exact hQ_erase t (Finset.mem_erase.mpr ⟨hteq, htS⟩)
    rw [cw_eval_P] at hp
    rw [cw_eval_Q] at hq
    exact (zmod2_sum3_eq_iff _ _ _ _ _ _).mpr ⟨hp, hq⟩

lemma dvd_natCard_of_dvd_fintypeCard {α : Type*} {inst : Fintype α} {d : ℕ}
    (h : d ∣ @Fintype.card α inst) : d ∣ Nat.card α := by
  rwa [@Nat.card_eq_fintype_card α inst]

/-- For any nonempty `S ⊆ Fin n`, `4 ∣ (subsetBalSet hn π S).card` via complementation
plus the Chevalley–Warning theorem over `ZMod 2`. -/
theorem four_dvd_card_subsetBalSet_nonempty {n : ℕ} (hn : 0 < n)
    (π : Fin n × Fin 3 ≃ Fin (3 * n)) {S : Finset (Fin n)} (hS : S.Nonempty) :
    4 ∣ (subsetBalSet hn π S).card := by
  let zeroV : Fin (3 * n) := ⟨0, by omega⟩
  let Half0 := (subsetBalSet hn π S).filter fun A => zeroV ∉ A
  have hcompl_mem : ∀ A, A ∈ subsetBalSet hn π S → Aᶜ ∈ subsetBalSet hn π S := by
    intro A hA
    simp only [subsetBalSet, Finset.mem_filter, Finset.mem_univ, true_and] at hA ⊢
    refine ⟨fun t ht => ?_, fun t ht j => ?_⟩
    · simp_rw [cycBal_compl, Finset.sum_neg_distrib, hA.1 t ht, neg_zero]
    · rw [cycBal_compl, hA.2 t ht j, neg_zero]
  have hcard_double : (subsetBalSet hn π S).card = 2 * Half0.card := by
    have hsplit := (Finset.card_filter_add_card_filter_not
      (s := subsetBalSet hn π S) (fun A => zeroV ∉ A)).symm
    have hbij : ((subsetBalSet hn π S).filter fun A => ¬ zeroV ∉ A).card = Half0.card := by
      refine Finset.card_bij (fun A _ => Aᶜ) ?_ ?_ ?_
      · intro A hA
        simp only [Finset.mem_filter, not_not, Half0, Finset.mem_compl] at hA ⊢
        exact ⟨hcompl_mem A hA.1, hA.2⟩
      · intro A₁ _ A₂ _ h; exact compl_injective h
      · intro A hA
        refine ⟨Aᶜ, ?_, compl_compl A⟩
        simp only [Finset.mem_filter, not_not, Half0, Finset.mem_compl] at hA ⊢
        exact ⟨hcompl_mem A hA.1, hA.2⟩
    rw [hsplit, hbij, two_mul]
  obtain ⟨t₀, ht₀⟩ := hS
  have hcw := dvd_natCard_of_dvd_fintypeCard
    (char_dvd_card_solutions_of_sum_lt (K := ZMod 2) 2 (cw_deg_sum_lt hn π ht₀))
  have h2 : 2 ∣ Half0.card := by
    rw [cw_card_half0_eq_solutions hn π ht₀]
    exact hcw
  rw [hcard_double]
  obtain ⟨k, hk⟩ := h2
  exact ⟨k, by omega⟩

/-- **Fleischner–Stiebitz Parity Theorem (1992):** For every `n ≥ 1` and every partition `π`
of `Fin (3 * n)` into `n` disjoint triangles, the total number of Eulerian subdigraphs of the
canonically oriented cycle-plus-triangles multigraph satisfies `totalEulerian ≡ 2 (mod 4)`. -/
theorem totalEulerian_mod4_eq_two {n : ℕ} (hn : 0 < n) (π : Fin n × Fin 3 ≃ Fin (3 * n)) :
    ((Finset.univ : Finset (Finset (CPTArc n))).filter
      (IsEulerian (cptSrc π) (cptDst hn π))).card % 4 = 2 := by
  rw [totalEulerian_eq_sum_subsetBal hn π]
  have hdecomp : (∑ S : Finset (Fin n), (subsetBalSet hn π S).card) =
      (subsetBalSet hn π ∅).card +
      ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).erase ∅, (subsetBalSet hn π S).card :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ ∅)).symm
  have hdvd4 : 4 ∣ ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).erase ∅,
      (subsetBalSet hn π S).card := by
    apply Finset.dvd_sum
    intro S hS
    have hne : S ≠ ∅ := (Finset.mem_erase.mp hS).1
    exact four_dvd_card_subsetBalSet_nonempty hn π (Finset.nonempty_iff_ne_empty.mpr hne)
  rw [hdecomp, card_subsetBalSet_empty hn π]
  obtain ⟨k, hk⟩ := hdvd4
  omega

/-- The signed Eulerian count `EE(D) - EO(D)` is nonzero for every cycle-plus-triangles graph. -/
theorem cpt_signedEulerianCount_ne_zero {n : ℕ} (hn : 0 < n) (π : Fin n × Fin 3 ≃ Fin (3 * n)) :
    signedEulerianCount (cptSrc π) (cptDst hn π) ≠ 0 :=
  signedEulerianCount_ne_zero_of_total_mod4 hn π (totalEulerian_mod4_eq_two hn π)

end ChevalleyWarningMod4

/-! ## Section 5: Main Theorems — 3-Choosability and 3-Colorability (JSP-000698) -/

section MainTheorems

/-- A graph `G` on a vertex set `V` is a **cycle-plus-triangles graph** of order `3n` if its
vertex set admits a spanning Hamilton cycle (`cyc : Fin (3 * n) ≃ V`) and a partition into `n`
pairwise vertex-disjoint triangles (`tri : Fin n × Fin 3 ≃ V`) whose union forms `G`
(whether or not any triangle edge coincides with a cycle edge). -/
def IsCyclePlusTriangles {V : Type*} (n : ℕ) (G : SimpleGraph V) : Prop :=
  ∃ (cyc : Fin (3 * n) ≃ V) (tri : Fin n × Fin 3 ≃ V),
    ∀ u v : V, G.Adj u v →
      (((cyc.symm u).1 + 1) % (3 * n) = (cyc.symm v).1 ∨
       ((cyc.symm v).1 + 1) % (3 * n) = (cyc.symm u).1 ∨
       (tri.symm u).1 = (tri.symm v).1)

/-- Exact equality characterization of a cycle-plus-triangles graph formed by the union of a
spanning Hamilton cycle and `n` pairwise vertex-disjoint triangles. -/
def IsExactCyclePlusTriangles {V : Type*} (n : ℕ) (G : SimpleGraph V) : Prop :=
  ∃ (cyc : Fin (3 * n) ≃ V) (tri : Fin n × Fin 3 ≃ V),
    ∀ u v : V, G.Adj u v ↔
      (u ≠ v ∧
        (((cyc.symm u).1 + 1) % (3 * n) = (cyc.symm v).1 ∨
         ((cyc.symm v).1 + 1) % (3 * n) = (cyc.symm u).1 ∨
         (tri.symm u).1 = (tri.symm v).1))

lemma isCyclePlusTriangles_of_exact {V : Type*} {n : ℕ} {G : SimpleGraph V}
    (h : IsExactCyclePlusTriangles n G) : IsCyclePlusTriangles n G := by
  obtain ⟨cyc, tri, hadj⟩ := h
  exact ⟨cyc, tri, fun u v huv => ((hadj u v).mp huv).2⟩

lemma fin3_triNext_cases (j₁ j₂ : Fin 3) (h : j₁ ≠ j₂) :
    triNext j₁ = j₂ ∨ triNext j₂ = j₁ := by
  fin_cases j₁ <;> fin_cases j₂ <;> simp_all [triNext]

/-- **Fleischner–Stiebitz Theorem (3-choosability, JSP-000698 / Erdős #842):**
Every graph formed by a spanning Hamilton cycle and `n` pairwise vertex-disjoint triangles
(and every subgraph thereof) is **3-choosable**: for any color type `α` and any assignment of
lists `L : V → Finset α` of size at least `3`, there exists a proper list coloring
`c : V → α` with `∀ v, c v ∈ L v` and `∀ u v, G.Adj u v → c u ≠ c v`. -/
theorem jsp_000698_fleischner_stiebitz_3_choosable
    {V α : Type*} [DecidableEq α] {n : ℕ} {G : SimpleGraph V}
    (hG : IsCyclePlusTriangles n G)
    (L : V → Finset α) (hL : ∀ v : V, 3 ≤ (L v).card) :
    ∃ c : V → α, (∀ v : V, c v ∈ L v) ∧ ∀ u v : V, G.Adj u v → c u ≠ c v := by
  obtain ⟨cyc, tri, hadj⟩ := hG
  by_cases hn0 : n = 0
  · subst hn0
    refine ⟨fun v => Fin.elim0 (cyc.symm v), ?_, ?_⟩
    · intro v; exact Fin.elim0 (cyc.symm v)
    · intro u; exact Fin.elim0 (cyc.symm u)
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    let π : Fin n × Fin 3 ≃ Fin (3 * n) := tri.trans cyc.symm
    let L' : Fin (3 * n) → Finset α := fun i => L (cyc i)
    have hL' : ∀ i : Fin (3 * n),
        (Finset.univ.filter fun a : CPTArc n => cptSrc π a = i).card < (L' i).card := by
      intro i
      rw [cpt_outdeg π i]
      have hi := hL (cyc i)
      dsimp [L']
      omega
    obtain ⟨c', hc'L', hc'arc⟩ :=
      alon_tarsi_list_coloring (cptSrc π) (cptDst hn π)
        (cpt_signedEulerianCount_ne_zero hn π) L' hL'
    refine ⟨fun v => c' (cyc.symm v), ?_, ?_⟩
    · intro v
      have h := hc'L' (cyc.symm v)
      simpa [L'] using h
    · intro u v huv
      have hne : u ≠ v := G.ne_of_adj huv
      rcases hadj u v huv with h1 | h2 | h3
      · have hd : cycNext hn (cyc.symm u) = cyc.symm v := Fin.ext h1
        have hdiff := hc'arc (Sum.inl (cyc.symm u))
        simpa [cptSrc, cptDst, hd] using hdiff
      · have hd : cycNext hn (cyc.symm v) = cyc.symm u := Fin.ext h2
        have hdiff := hc'arc (Sum.inl (cyc.symm v))
        simpa [cptSrc, cptDst, hd] using Ne.symm hdiff
      · let t := (tri.symm u).1
        let j₁ := (tri.symm u).2
        let j₂ := (tri.symm v).2
        have ht_v : (tri.symm v).1 = t := h3.symm
        have hu_eq : π (t, j₁) = cyc.symm u := by
          dsimp [π, t, j₁]; simp
        have hv_eq : π (t, j₂) = cyc.symm v := by
          dsimp [π, j₂]; rw [← ht_v]; simp
        have hj_ne : j₁ ≠ j₂ := by
          intro hj
          apply hne
          apply tri.symm.injective
          exact Prod.ext h3 hj
        have hcases : triNext j₁ = j₂ ∨ triNext j₂ = j₁ :=
          fin3_triNext_cases j₁ j₂ hj_ne
        rcases hcases with hnext | hprev
        · have hdiff := hc'arc (Sum.inr (t, j₁))
          dsimp [cptSrc, cptDst] at hdiff
          rwa [hu_eq, hnext, hv_eq] at hdiff
        · have hdiff := hc'arc (Sum.inr (t, j₂))
          dsimp [cptSrc, cptDst] at hdiff
          rw [hv_eq, hprev, hu_eq] at hdiff
          exact Ne.symm hdiff

/-- **Main Theorem (JSP-000698 / Erdős Problem #842 — Fleischner–Stiebitz 1992):**
Every graph formed by vertex-disjoint triangles and a spanning Hamilton cycle admits a
proper 3-coloring `G.Coloring (Fin 3)`. -/
theorem jsp_000698_fleischner_stiebitz_3_colorable
    {V : Type*} {n : ℕ} {G : SimpleGraph V}
    (hG : IsCyclePlusTriangles n G) :
    Nonempty (G.Coloring (Fin 3)) := by
  obtain ⟨c, _, hproper⟩ :=
    jsp_000698_fleischner_stiebitz_3_choosable hG
      (fun _ => (Finset.univ : Finset (Fin 3)))
      (fun _ => by decide)
  exact ⟨SimpleGraph.Coloring.mk c (fun {u v} huv => hproper u v huv)⟩

/-- Exact-union corollary for `IsExactCyclePlusTriangles`. -/
theorem jsp_000698_exact_3_colorable
    {V : Type*} {n : ℕ} {G : SimpleGraph V}
    (hG : IsExactCyclePlusTriangles n G) :
    Nonempty (G.Coloring (Fin 3)) :=
  jsp_000698_fleischner_stiebitz_3_colorable (isCyclePlusTriangles_of_exact hG)

/-- Chromatic number upper bound `G.chromaticNumber ≤ 3` for every cycle-plus-triangles graph. -/
theorem jsp_000698_chromaticNumber_le_three
    {V : Type*} {n : ℕ} {G : SimpleGraph V}
    (hG : IsCyclePlusTriangles n G) :
    G.chromaticNumber ≤ 3 :=
  SimpleGraph.chromaticNumber_le_iff_colorable.mpr (jsp_000698_fleischner_stiebitz_3_colorable hG)

end MainTheorems

end JSP_000698

#check JSP_000698.alon_tarsi_list_coloring
#check JSP_000698.totalEulerian_mod4_eq_two
#check JSP_000698.jsp_000698_fleischner_stiebitz_3_choosable
#check JSP_000698.jsp_000698_fleischner_stiebitz_3_colorable
#check JSP_000698.jsp_000698_exact_3_colorable
#check JSP_000698.jsp_000698_chromaticNumber_le_three

#print axioms JSP_000698.alon_tarsi_list_coloring
#print axioms JSP_000698.totalEulerian_mod4_eq_two
#print axioms JSP_000698.jsp_000698_fleischner_stiebitz_3_choosable
#print axioms JSP_000698.jsp_000698_fleischner_stiebitz_3_colorable
#print axioms JSP_000698.jsp_000698_exact_3_colorable
#print axioms JSP_000698.jsp_000698_chromaticNumber_le_three
