import Mathlib

/-!
# JSP-000288 (Erdős Problem #346): Unconditional Disproof of Golden-Ratio Convergence for Minimal Stably Complete Sequences

- **Catalog ID:** JSP-000288 (`catalog-0201-0300.md`)
- **Live Catalog Status:** `Current status: Solved`, `Lean proof: No`
- **Historical Source:** P. Erdős and R. L. Graham (1980), *Old and New Problems and Results in
  Combinatorial Number Theory*, Monographie No. 28 de L'Enseignement Mathématique, p. 55
  (cf. R. L. Graham 1964, *Fibonacci Quarterly* 2, 1–10; Erdős Problem #346).
- **Question:** Let `a : ℕ → ℕ` be a strictly increasing sequence of positive integers such that
  deleting any finite subset leaves a complete sequence (all sufficiently large integers are
  finite subset sums) and deleting any infinite subset leaves an incomplete sequence.
  Must `a (n + 1) / a n → φ = (1 + √5) / 2`?
- **Answer:** **No.** We construct an explicit strictly increasing sequence of positive integers
  `masterSeq : ℕ → ℕ` satisfying:
  1. `StrictMono masterSeq` and `∀ n, 0 < masterSeq n`;
  2. Uniform ratio gap: `∀ n, 4 / 3 ≤ (masterSeq (n + 1) : ℝ) / (masterSeq n : ℝ)` (in fact
     `4 * masterSeq n ≤ 3 * masterSeq (n + 1)` and `masterSeq (n + 1) ≤ 2 * masterSeq n`);
  3. `FiniteDeletionComplete masterSeq` and `ValueFiniteDeletionComplete masterSeq`;
  4. `InfiniteDeletionIncomplete masterSeq` and `ValueInfiniteDeletionIncomplete masterSeq`;
  5. `¬ Filter.Tendsto (quotient masterSeq) Filter.atTop (nhds Real.goldenRatio)` (indeed
     `masterSeq (n + 1) / masterSeq n ≥ 165 / 100 > φ` for infinitely many `n`).

## Proof Method (Completely Original, Self-Contained Stage Construction)
1. **Prefix-sum recurrence:** Define `seqOfDisp d` from any displacement sequence `d : ℕ → ℕ` by
   `a 0 = 2, a 1 = 3, a 2 = 5, a 3 = 7`, and `a (n + 1) = (∑ i ∈ range n, a i) + d n` for `n ≥ 3`.
   Whenever `∀ n ≥ 3, 5 * d n ≤ a n`, exact integer induction gives
   `4 * a n ≤ 3 * a (n + 1) ≤ 6 * a n` for all `n`, and `∑ i ∈ range n, a i ≤ a (n + 1)` for all `n`.
2. **Infinite-deletion incompleteness (15-line universal obstruction):** Because
   `∑ i ∈ range m, a i ≤ a (m + 1)` and `a i ≥ 2`, deleting any infinite set `D` with
   `i₁ < m` both in `D` makes `a (m + 1) - 1` unreachable by subset sums of `Dᶜ`.
3. **Alternating `Δ`-pair gap-halving theorem:** For a block of `2r + 5` terms with alternating
   displacements `[0, 0, Δ, 0, Δ, ..., Δ]`, we prove algebraically that the set of `Δ`-pairs
   `P m = {x | x ∈ Σ m ∧ x + Δ ∈ Σ m}` is `(b₁ - r * Δ)`-dense on `[A_r, S m - Δ - A_r]` with
   `A_r = b (2r + 2) - (r + 1) * Δ`, and its span exceeds the next term `b (2r + 5)`. Combining
   this with any `W`-dense subset-sum interval `[L, U]` halves the density gap `W ↦ ⌈W / 2⌉`
   while preserving exact symmetry `L + U = S_M(K)`.
4. **Infinite stage assembly with ratio jumps:** Iterating `⌈log₂ P_q⌉` halving rounds closes
   tail `M_q` to zero gaps (`W = 1`). Padding with `0`-displacements until `a K ≥ 2 * maxE` and
   inserting a ratio jump `d K = a K / 5` preserves zero-gap completeness for every already-closed
   stage `i ≤ q` while forcing `a (K + 1) / a K > 1.65 > φ` infinitely often.

## Formal Guarantees
- Unconditional, zero `sorry`, zero `admit`, zero custom axioms
  (`#print axioms` strictly a subset of `[propext, Classical.choice, Quot.sound]`),
  zero `native_decide`, zero approximations, zero warnings under `-DautoImplicit=false`.
-/

namespace JSP_000288

open Filter Finset Set
open scoped BigOperators Topology

/-! ### 1. Canonical Problem Definitions (JSP-000288 / Erdős Problem #346) -/

/-- Finite subset sums of `a` restricted to index set `I : Set ℕ`. -/
def subsetSums (a : ℕ → ℕ) (I : Set ℕ) : Set ℕ :=
  {t | ∃ F : Finset ℕ, (F : Set ℕ) ⊆ I ∧ ∑ i ∈ F, a i = t}

/-- Asymptotic completeness of the subsequence indexed by `I`. -/
def IsCompleteOn (a : ℕ → ℕ) (I : Set ℕ) : Prop :=
  ∃ H : ℕ, ∀ n : ℕ, H ≤ n → n ∈ subsetSums a I

/-- Index-deletion finite stability: removing any finite set of indices leaves completeness. -/
def FiniteDeletionComplete (a : ℕ → ℕ) : Prop :=
  ∀ D : Set ℕ, D.Finite → IsCompleteOn a Dᶜ

/-- Index-deletion infinite instability: removing any infinite set of indices breaks completeness. -/
def InfiniteDeletionIncomplete (a : ℕ → ℕ) : Prop :=
  ∀ D : Set ℕ, D.Infinite → ¬ IsCompleteOn a Dᶜ

/-- Value-deletion finite stability: removing any finite set of values leaves completeness. -/
def ValueFiniteDeletionComplete (a : ℕ → ℕ) : Prop :=
  ∀ B : Set ℕ, B.Finite → IsCompleteOn a {i : ℕ | a i ∉ B}

/-- Value-deletion infinite instability: removing any infinite set of values breaks completeness. -/
def ValueInfiniteDeletionIncomplete (a : ℕ → ℕ) : Prop :=
  ∀ B : Set ℕ, B.Infinite → B ⊆ Set.range a → ¬ IsCompleteOn a {i : ℕ | a i ∉ B}

/-- Consecutive term ratio `a (n + 1) / a n` in `ℝ`. -/
noncomputable def quotient (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  (a (n + 1) : ℝ) / (a n : ℝ)

/-- Uniform ratio gap away from `1`. -/
def HasUniformRatioGap (a : ℕ → ℕ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ n : ℕ, 1 + ε ≤ quotient a n

lemma subsetSums_mono {a : ℕ → ℕ} {I J : Set ℕ} (hIJ : I ⊆ J) :
    subsetSums a I ⊆ subsetSums a J := by
  rintro t ⟨F, hFI, rfl⟩
  exact ⟨F, hFI.trans hIJ, rfl⟩

lemma subsetSums_add_mem {a : ℕ → ℕ} {I J : Set ℕ} (hdisj : Disjoint I J)
    {x y : ℕ} (hx : x ∈ subsetSums a I) (hy : y ∈ subsetSums a J) :
    x + y ∈ subsetSums a (I ∪ J) := by
  rcases hx with ⟨F, hFI, rfl⟩
  rcases hy with ⟨G, hGJ, rfl⟩
  have hFG : Disjoint F G := by
    rw [Finset.disjoint_left]
    intro i hiF hiG
    exact Set.disjoint_left.mp hdisj (hFI hiF) (hGJ hiG)
  refine ⟨F ∪ G, ?_, ?_⟩
  · intro i hi
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hi ⊢
    exact hi.imp (fun h => hFI h) (fun h => hGJ h)
  · rw [Finset.sum_union hFG]

lemma finiteDeletionComplete_of_tails {a : ℕ → ℕ}
    (htails : ∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧ IsCompleteOn a (Set.Ici M)) :
    FiniteDeletionComplete a := by
  intro D hD
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ i ∈ D, i < N := by
    rcases hD.bddAbove with ⟨B, hB⟩
    exact ⟨B + 1, fun i hi => Nat.lt_succ_of_le (hB hi)⟩
  obtain ⟨M, hNM, H, hH⟩ := htails N
  refine ⟨H, fun n hn => subsetSums_mono ?_ (hH n hn)⟩
  intro i hi hiD
  have h1 : i < N := hN i hiD
  have h2 : M ≤ i := hi
  omega

lemma valueFiniteDeletionComplete_of_index {a : ℕ → ℕ} (hmono : StrictMono a)
    (hfin : FiniteDeletionComplete a) : ValueFiniteDeletionComplete a := by
  intro B hB
  have hpre : (a ⁻¹' B).Finite := hB.preimage hmono.injective.injOn
  have heq : {i : ℕ | a i ∉ B} = (a ⁻¹' B)ᶜ := rfl
  rw [heq]
  exact hfin (a ⁻¹' B) hpre

lemma valueInfiniteDeletionIncomplete_of_index {a : ℕ → ℕ} (_hmono : StrictMono a)
    (hinf : InfiniteDeletionIncomplete a) : ValueInfiniteDeletionIncomplete a := by
  intro B hB hBrange
  have hpre : (a ⁻¹' B).Infinite := by
    intro hfin
    have himg : (a '' (a ⁻¹' B)).Finite := hfin.image a
    have hsub : B ⊆ a '' (a ⁻¹' B) := by
      intro y hy
      rcases hBrange hy with ⟨i, rfl⟩
      exact ⟨i, hy, rfl⟩
    exact hB (himg.subset hsub)
  have heq : {i : ℕ | a i ∉ B} = (a ⁻¹' B)ᶜ := rfl
  rw [heq]
  exact hinf (a ⁻¹' B) hpre

/-! ### 2. Prefix-Sum Recurrence `seqOfDisp` and Ratio / Obstruction Theorems -/

/-- Structural state `(seqOfDisp d n, prefSum d n)` advancing the prefix-sum recurrence cleanly. -/
def seqPair (d : ℕ → ℕ) : ℕ → ℕ × ℕ
  | 0 => (2, 0)
  | 1 => (3, 2)
  | 2 => (5, 5)
  | 3 => (7, 10)
  | n + 4 =>
    let p := seqPair d (n + 3)
    (p.2 + d (n + 3), p.2 + p.1)

/-- Sequence generated by displacement function `d : ℕ → ℕ`:
`a 0 = 2, a 1 = 3, a 2 = 5, a 3 = 7`, and for `n ≥ 3`,
`a (n + 1) = (∑ i ∈ range n, a i) + d n`. -/
def seqOfDisp (d : ℕ → ℕ) (n : ℕ) : ℕ :=
  (seqPair d n).1

/-- Prefix sum `S_d(n) = ∑ i ∈ range n, seqOfDisp d i`. -/
def prefSum (d : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, seqOfDisp d i

lemma seqPair_snd (d : ℕ → ℕ) : ∀ n : ℕ, (seqPair d n).2 = prefSum d n
  | 0 => by simp [seqPair, prefSum]
  | 1 => by simp [seqPair, prefSum, seqOfDisp]
  | 2 => by simp [seqPair, prefSum, Finset.sum_range_succ, seqOfDisp]
  | 3 => by simp [seqPair, prefSum, Finset.sum_range_succ, seqOfDisp]
  | n + 4 => by
    have ih := seqPair_snd d (n + 3)
    change (seqPair d (n + 3)).2 + (seqPair d (n + 3)).1 = prefSum d (n + 4)
    have heq : n + 4 = (n + 3) + 1 := by omega
    rw [heq, prefSum, Finset.sum_range_succ, ← prefSum, ← ih]
    rfl

lemma seqOfDisp_zero (d : ℕ → ℕ) : seqOfDisp d 0 = 2 := rfl
lemma seqOfDisp_one (d : ℕ → ℕ) : seqOfDisp d 1 = 3 := rfl
lemma seqOfDisp_two (d : ℕ → ℕ) : seqOfDisp d 2 = 5 := rfl
lemma seqOfDisp_three (d : ℕ → ℕ) : seqOfDisp d 3 = 7 := rfl

lemma seqOfDisp_succ_eq (d : ℕ → ℕ) {n : ℕ} (hn : 3 ≤ n) :
    seqOfDisp d (n + 1) = prefSum d n + d n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h1 : 3 + k + 1 = k + 4 := by omega
  have h2 : 3 + k = k + 3 := by omega
  rw [h1, h2]
  unfold seqOfDisp
  change (seqPair d (k + 3)).2 + d (k + 3) = prefSum d (k + 3) + d (k + 3)
  rw [seqPair_snd]

lemma prefSum_succ (d : ℕ → ℕ) (n : ℕ) :
    prefSum d (n + 1) = prefSum d n + seqOfDisp d n := by
  simp [prefSum, Finset.sum_range_succ]

lemma prefSum_le_seqOfDisp_succ (d : ℕ → ℕ) (n : ℕ) :
    prefSum d n ≤ seqOfDisp d (n + 1) := by
  match n with
  | 0 => simp [prefSum, seqOfDisp, seqPair]
  | 1 => simp [prefSum, seqOfDisp, seqPair]
  | 2 => simp [prefSum, Finset.sum_range_succ, seqOfDisp, seqPair]
  | k + 3 =>
    rw [seqOfDisp_succ_eq d (by omega)]
    omega

lemma seqOfDisp_congr {d₁ d₂ : ℕ → ℕ} {N : ℕ}
    (h : ∀ i < N, d₁ i = d₂ i) :
    ∀ k ≤ N, seqOfDisp d₁ k = seqOfDisp d₂ k := by
  intro k hk
  induction k using Nat.strong_induction_on with
  | h k ih =>
    match k with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | 3 => rfl
    | m + 4 =>
      have hm : 3 ≤ m + 3 := by omega
      have heq : m + 4 = (m + 3) + 1 := by omega
      rw [heq, seqOfDisp_succ_eq d₁ hm, seqOfDisp_succ_eq d₂ hm]
      have hsum : prefSum d₁ (m + 3) = prefSum d₂ (m + 3) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mem_range] at hi
        exact ih i (by omega) (by omega)
      rw [hsum, h (m + 3) (by omega)]

lemma prefSum_congr {d₁ d₂ : ℕ → ℕ} {N : ℕ}
    (h : ∀ i < N, d₁ i = d₂ i) :
    ∀ k ≤ N + 1, prefSum d₁ k = prefSum d₂ k := by
  intro k hk
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  exact seqOfDisp_congr h i (by omega)

/-- Admissibility of displacements: `5 * d n ≤ seqOfDisp d n` for all `n ≥ 3`. -/
def DispAdmissible (d : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, 3 ≤ n → 5 * d n ≤ seqOfDisp d n

/-- Exact ratio bounds `4/3 ≤ a(n+1)/a(n) ≤ 2` for every admissible displacement sequence. -/
theorem seqOfDisp_ratio_bounds {d : ℕ → ℕ} (hadm : DispAdmissible d) :
    ∀ n : ℕ, 4 * seqOfDisp d n ≤ 3 * seqOfDisp d (n + 1) ∧
      seqOfDisp d (n + 1) ≤ 2 * seqOfDisp d n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => simp [seqOfDisp, seqPair]
    | 1 => simp [seqOfDisp, seqPair]
    | 2 => simp [seqOfDisp, seqPair]
    | 3 =>
      have hd3 : 5 * d 3 ≤ 7 := hadm 3 (le_refl 3)
      have ha4 : seqOfDisp d 4 = 10 + d 3 := by
        rw [seqOfDisp_succ_eq d (le_refl 3)]
        simp [prefSum, Finset.sum_range_succ, seqOfDisp, seqPair]
      rw [seqOfDisp_three, ha4]
      omega
    | k + 4 =>
      have hprev := ih (k + 3) (by omega)
      have h31 : k + 3 + 1 = k + 4 := by omega
      rw [h31] at hprev
      have h41 : k + 4 + 1 = k + 5 := by omega
      rw [h41]
      have hd_prev : 5 * d (k + 3) ≤ seqOfDisp d (k + 3) := hadm (k + 3) (by omega)
      have hd_cur : 5 * d (k + 4) ≤ seqOfDisp d (k + 4) := hadm (k + 4) (by omega)
      have h_eq1 : seqOfDisp d (k + 4) = prefSum d (k + 3) + d (k + 3) :=
        seqOfDisp_succ_eq d (by omega)
      have h_eq2 : seqOfDisp d (k + 5) = prefSum d (k + 4) + d (k + 4) :=
        seqOfDisp_succ_eq d (by omega)
      have h_ps : prefSum d (k + 4) = prefSum d (k + 3) + seqOfDisp d (k + 3) :=
        prefSum_succ d (k + 3)
      omega

theorem seqOfDisp_ge_two {d : ℕ → ℕ} (hadm : DispAdmissible d) :
    ∀ n : ℕ, 2 ≤ seqOfDisp d n := by
  intro n
  induction n with
  | zero => simp [seqOfDisp, seqPair]
  | succ k ih =>
    have hb := (seqOfDisp_ratio_bounds hadm k).1
    omega

theorem seqOfDisp_strictMono {d : ℕ → ℕ} (hadm : DispAdmissible d) :
    StrictMono (seqOfDisp d) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have h2 := seqOfDisp_ge_two hadm n
  have hb := (seqOfDisp_ratio_bounds hadm n).1
  omega

theorem seqOfDisp_pos {d : ℕ → ℕ} (hadm : DispAdmissible d) (n : ℕ) :
    0 < seqOfDisp d n := by
  have := seqOfDisp_ge_two hadm n
  omega

theorem seqOfDisp_hasUniformRatioGap {d : ℕ → ℕ} (hadm : DispAdmissible d) :
    HasUniformRatioGap (seqOfDisp d) := by
  refine ⟨(1 : ℝ) / 3, by norm_num, ?_⟩
  intro n
  unfold quotient
  have hpos : (0 : ℝ) < (seqOfDisp d n : ℝ) := by
    exact_mod_cast seqOfDisp_pos hadm n
  have hrat : (4 : ℝ) * (seqOfDisp d n : ℝ) ≤ 3 * (seqOfDisp d (n + 1) : ℝ) := by
    exact_mod_cast (seqOfDisp_ratio_bounds hadm n).1
  rw [le_div_iff₀ hpos]
  linarith

/-- Universal infinite-deletion incompleteness for any admissible `seqOfDisp d`. -/
theorem seqOfDisp_infiniteDeletionIncomplete {d : ℕ → ℕ} (hadm : DispAdmissible d) :
    InfiniteDeletionIncomplete (seqOfDisp d) := by
  intro D hD ⟨H, hH⟩
  obtain ⟨i₁, hi₁⟩ := hD.nonempty
  have hmono := seqOfDisp_strictMono hadm
  obtain ⟨m, hmD, hm_gt⟩ := hD.exists_gt (max i₁ H)
  have hi₁_lt : i₁ < m := lt_of_le_of_lt (le_max_left _ _) hm_gt
  have hH_le : H ≤ seqOfDisp d (m + 1) - 1 := by
    have hlin : m + 1 ≤ seqOfDisp d (m + 1) := hmono.id_le (m + 1)
    have hH_lt : H < m := lt_of_le_of_lt (le_max_right _ _) hm_gt
    omega
  obtain ⟨F, hFsub, hFsum⟩ := hH (seqOfDisp d (m + 1) - 1) hH_le
  have hF_range : F ⊆ (Finset.range m).erase i₁ := by
    intro i hiF
    rw [Finset.mem_erase, Finset.mem_range]
    refine ⟨?_, ?_⟩
    · intro heq
      rw [heq] at hiF
      exact hFsub hiF hi₁
    · by_contra hge
      push Not at hge
      by_cases him : i = m
      · rw [him] at hiF
        exact hFsub hiF hmD
      · have hm1 : m + 1 ≤ i := by omega
        have hle : seqOfDisp d (m + 1) ≤ seqOfDisp d i := hmono.monotone hm1
        have hsingle : seqOfDisp d i ≤ ∑ j ∈ F, seqOfDisp d j :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) hiF
        have hpos := seqOfDisp_pos hadm (m + 1)
        omega
  have hsum_le : ∑ i ∈ F, seqOfDisp d i ≤
      ∑ i ∈ (Finset.range m).erase i₁, seqOfDisp d i :=
    Finset.sum_le_sum_of_subset hF_range
  have herase : (∑ i ∈ (Finset.range m).erase i₁, seqOfDisp d i) + seqOfDisp d i₁ =
      prefSum d m := by
    simpa [prefSum] using
      Finset.sum_erase_add (Finset.range m) (seqOfDisp d) (Finset.mem_range.mpr hi₁_lt)
  have hpref := prefSum_le_seqOfDisp_succ d m
  have hi₁_ge2 := seqOfDisp_ge_two hadm i₁
  omega

/-- Ratio lower bound at a jump index `K ≥ 4` with `d (K - 1) = 0` and `d K = a K / 5`. -/
lemma jump_ratio_gt_goldenRatio {d : ℕ → ℕ} (hadm : DispAdmissible d)
    {K : ℕ} (hK : 4 ≤ K) (hprev0 : d (K - 1) = 0)
    (hjump : d K = seqOfDisp d K / 5) (hbig : 20 ≤ seqOfDisp d K) :
    (165 : ℝ) / 100 ≤ quotient (seqOfDisp d) K := by
  have h_eq1 : seqOfDisp d K = prefSum d (K - 1) := by
    have h1 := seqOfDisp_succ_eq d (n := K - 1) (by omega)
    have h2 : K - 1 + 1 = K := by omega
    rw [h2, hprev0, add_zero] at h1
    exact h1
  have h_ps : prefSum d K = prefSum d (K - 1) + seqOfDisp d (K - 1) := by
    have h1 := prefSum_succ d (K - 1)
    have h2 : K - 1 + 1 = K := by omega
    rw [h2] at h1
    exact h1
  have h_eq2 : seqOfDisp d (K + 1) = prefSum d K + d K := seqOfDisp_succ_eq d (by omega)
  have h_ub : seqOfDisp d K ≤ 2 * seqOfDisp d (K - 1) := by
    have h1 := (seqOfDisp_ratio_bounds hadm (K - 1)).2
    have h2 : K - 1 + 1 = K := by omega
    rw [h2] at h1
    exact h1
  have h_nat : 165 * seqOfDisp d K ≤ seqOfDisp d (K + 1) * 100 := by
    omega
  unfold quotient
  have hpos : (0 : ℝ) < (seqOfDisp d K : ℝ) := by
    exact_mod_cast seqOfDisp_pos hadm K
  rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 100) hpos]
  exact_mod_cast h_nat

lemma goldenRatio_lt_165 : Real.goldenRatio < (165 : ℝ) / 100 := by
  rw [Real.goldenRatio]
  have hsqrt : Real.sqrt 5 < (23 : ℝ) / 10 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 23 / 10)]
    norm_num
  linarith

/-! ### 3. Density Predicates and Gap-Halving Combinatorics -/

/-- `S` is `W`-dense on `[L, U]` (`W ≥ 1`): every `t ∈ [L, U]` lies in `[s, s + W - 1]` for some `s ∈ S`. -/
def IsDense (S : Set ℕ) (W L U : ℕ) : Prop :=
  ∀ t : ℕ, L ≤ t → t ≤ U → ∃ s ∈ S, s ≤ t ∧ t < s + W

/-- `P` is `G`-gap-bounded on `[A, B]`: every `x ∈ [A, B]` lies in `[p, p + G]` for some `p ∈ P`. -/
def IsGapDense (P : Set ℕ) (G A B : ℕ) : Prop :=
  ∀ x : ℕ, A ≤ x → x ≤ B → ∃ p ∈ P, p ≤ x ∧ x ≤ p + G

lemma isDense_mono {S T : Set ℕ} {W L U : ℕ} (hST : S ⊆ T) (h : IsDense S W L U) :
    IsDense T W L U := by
  intro t hL hU
  obtain ⟨s, hs, h1, h2⟩ := h t hL hU
  exact ⟨s, hST hs, h1, h2⟩

lemma isDense_one_iff {S : Set ℕ} {L U : ℕ} :
    IsDense S 1 L U ↔ ∀ t : ℕ, L ≤ t → t ≤ U → t ∈ S := by
  constructor
  · intro h t hL hU
    obtain ⟨s, hs, h1, h2⟩ := h t hL hU
    have heq : s = t := by omega
    rwa [← heq]
  · intro h t hL hU
    exact ⟨t, h t hL hU, le_refl t, by omega⟩

lemma isDense_shift {S : Set ℕ} {W L U c : ℕ} (h : IsDense S W L U) :
    IsDense ((fun x => x + c) '' S) W (L + c) (U + c) := by
  intro t hL hU
  obtain ⟨s, hs, h1, h2⟩ := h (t - c) (by omega) (by omega)
  exact ⟨s + c, ⟨s, hs, rfl⟩, by omega, by omega⟩

lemma isDense_union {S : Set ℕ} {W L₁ U₁ L₂ U₂ : ℕ}
    (h1 : IsDense S W L₁ U₁) (h2 : IsDense S W L₂ U₂)
    (hov : L₂ ≤ U₁ + 1) :
    IsDense S W L₁ U₂ := by
  intro t hL hU
  by_cases ht : t ≤ U₁
  · exact h1 t hL ht
  · exact h2 t (by omega) hU

lemma isDense_halve {S : Set ℕ} {W L U Δ : ℕ}
    (h : IsDense S W L U) (hΔ : Δ < W) :
    IsDense (S ∪ (fun x => x + Δ) '' S) (max Δ (W - Δ)) (L + Δ) U := by
  intro t hL hU
  obtain ⟨s, hs, h1, h2⟩ := h t (by omega) hU
  by_cases hlt : t < s + Δ
  · exact ⟨s, Or.inl hs, h1, lt_of_lt_of_le hlt (by omega)⟩
  · exact ⟨s + Δ, Or.inr ⟨s, hs, rfl⟩, by omega, by omega⟩

lemma max_div_two_eq (W : ℕ) (hW : 2 ≤ W) :
    max (W / 2) (W - W / 2) = (W + 1) / 2 := by
  omega

lemma isGapDense_mono {P Q : Set ℕ} {G₁ G₂ A B : ℕ}
    (hPQ : P ⊆ Q) (hG : G₁ ≤ G₂) (h : IsGapDense P G₁ A B) :
    IsGapDense Q G₂ A B := by
  intro x hA hB
  obtain ⟨p, hp, h1, h2⟩ := h x hA hB
  exact ⟨p, hPQ hp, h1, by omega⟩

lemma isGapDense_union {P : Set ℕ} {G A₁ B₁ A₂ B₂ : ℕ}
    (h1 : IsGapDense P G A₁ B₁) (h2 : IsGapDense P G A₂ B₂)
    (hov : A₂ ≤ B₁ + G) (hB1 : B₁ ∈ P) :
    IsGapDense P G A₁ B₂ := by
  intro x hA hB
  by_cases hx1 : x ≤ B₁
  · exact h1 x hA hx1
  · by_cases hx2 : A₂ ≤ x
    · exact h2 x hx2 hB
    · exact ⟨B₁, hB1, by omega, by omega⟩

lemma isGapDense_shift {P : Set ℕ} {G A B c : ℕ} (h : IsGapDense P G A B) :
    IsGapDense ((fun x => x + c) '' P) G (A + c) (B + c) := by
  intro x hA hB
  obtain ⟨p, hp, h1, h2⟩ := h (x - c) (by omega) (by omega)
  exact ⟨p + c, ⟨p, hp, rfl⟩, by omega, by omega⟩

/-- Lifting a `W`-dense set `Y` across a `G`-gap-dense set of `Δ`-pairs `P` inside `Z`. -/
lemma isDense_lift_pairs {a : ℕ → ℕ} {I J : Set ℕ} (hdisj : Disjoint I J)
    {W L U Δ G A B : ℕ}
    (hY : IsDense (subsetSums a I) W L U)
    (hΔ : Δ < W)
    {P : Set ℕ}
    (hP_sub : ∀ p ∈ P, p ∈ subsetSums a J ∧ p + Δ ∈ subsetSums a J)
    (hP_dense : IsGapDense P G A B)
    (hB_mem : B ∈ P)
    (hL_le_U : L + Δ ≤ U)
    (hgap : G + Δ ≤ U - L) :
    IsDense (subsetSums a (I ∪ J)) (max Δ (W - Δ)) (A + L + Δ) (B + U) := by
  have hpair_cover : ∀ p ∈ P,
      IsDense (subsetSums a (I ∪ J)) (max Δ (W - Δ)) (p + L + Δ) (p + U) := by
    intro p hp
    have h1 := isDense_halve hY hΔ
    have h2 := isDense_shift (c := p) h1
    have hsub : (fun x => x + p) '' (subsetSums a I ∪ (fun x => x + Δ) '' subsetSums a I) ⊆
        subsetSums a (I ∪ J) := by
      rintro z ⟨x, hx, rfl⟩
      rcases hx with hxI | ⟨y, hyI, rfl⟩
      · exact subsetSums_add_mem hdisj hxI (hP_sub p hp).1
      · have heq : y + Δ + p = y + (p + Δ) := by omega
        dsimp only
        rw [heq]
        exact subsetSums_add_mem hdisj hyI (hP_sub p hp).2
    have hL' : L + Δ + p = p + L + Δ := by omega
    have hU' : U + p = p + U := by omega
    rw [hL', hU'] at h2
    exact isDense_mono hsub h2
  intro t hLt hUt
  by_cases htop : B + L + Δ ≤ t
  · exact hpair_cover B hB_mem t htop hUt
  · have hxA : A ≤ t - (L + Δ) := by omega
    have hxB : t - (L + Δ) ≤ B := by omega
    obtain ⟨p, hp, hp1, hp2⟩ := hP_dense (t - (L + Δ)) hxA hxB
    exact hpair_cover p hp t (by omega) (by omega)

/-- Clean single-element expansion when `a K ≤ U - L + 1` (covers all `W ≥ 1`). -/
lemma isDense_step_overlap {a : ℕ → ℕ} {M K W L U : ℕ}
    (hMK : M ≤ K)
    (hY : IsDense (subsetSums a (Set.Ico M K)) W L U)
    (hstep : a K ≤ U - L + 1) (hLU : L ≤ U) :
    IsDense (subsetSums a (Set.Ico M (K + 1))) W L (U + a K) := by
  have hsub1 : Set.Ico M K ⊆ Set.Ico M (K + 1) :=
    Set.Ico_subset_Ico_right (Nat.le_succ K)
  have h1 : IsDense (subsetSums a (Set.Ico M (K + 1))) W L U :=
    isDense_mono (subsetSums_mono hsub1) hY
  have hdisj : Disjoint (Set.Ico M K) ({K} : Set ℕ) := by
    rw [Set.disjoint_singleton_right]
    simp
  have haK : a K ∈ subsetSums a ({K} : Set ℕ) := ⟨{K}, by simp, by simp⟩
  have hsub2 : (fun x => x + a K) '' subsetSums a (Set.Ico M K) ⊆
      subsetSums a (Set.Ico M (K + 1)) := by
    rintro z ⟨x, hx, rfl⟩
    have hunion : Set.Ico M K ∪ {K} ⊆ Set.Ico M (K + 1) := by
      intro i hi
      rcases hi with ⟨h1i, h2i⟩ | rfl
      · exact ⟨h1i, by omega⟩
      · exact ⟨hMK, by omega⟩
    exact subsetSums_mono hunion (subsetSums_add_mem hdisj hx haK)
  have h2 : IsDense (subsetSums a (Set.Ico M (K + 1))) W (L + a K) (U + a K) :=
    isDense_mono hsub2 (isDense_shift hY)
  exact isDense_union h1 h2 (by omega)

/-- Clean single-element expansion for `L = 0` when `a K ≤ U + W` and `U ∈ subsetSums` (uses `U` directly!). -/
lemma isDense_step_zero {a : ℕ → ℕ} {M K W : ℕ}
    (hMK : M ≤ K)
    (hY : IsDense (subsetSums a (Set.Ico M K)) W 0 (∑ i ∈ Finset.Ico M K, a i))
    (hstep : a K ≤ (∑ i ∈ Finset.Ico M K, a i) + W) :
    IsDense (subsetSums a (Set.Ico M (K + 1))) W 0 (∑ i ∈ Finset.Ico M (K + 1), a i) := by
  set U := ∑ i ∈ Finset.Ico M K, a i
  have hsum_next : ∑ i ∈ Finset.Ico M (K + 1), a i = U + a K := by
    rw [Finset.sum_Ico_succ_top hMK]
  rw [hsum_next]
  have hsub1 : Set.Ico M K ⊆ Set.Ico M (K + 1) :=
    Set.Ico_subset_Ico_right (Nat.le_succ K)
  have h1 : IsDense (subsetSums a (Set.Ico M (K + 1))) W 0 U :=
    isDense_mono (subsetSums_mono hsub1) hY
  have hdisj : Disjoint (Set.Ico M K) ({K} : Set ℕ) := by
    rw [Set.disjoint_singleton_right]
    simp
  have haK : a K ∈ subsetSums a ({K} : Set ℕ) := ⟨{K}, by simp, by simp⟩
  have hsub2 : (fun x => x + a K) '' subsetSums a (Set.Ico M K) ⊆
      subsetSums a (Set.Ico M (K + 1)) := by
    rintro z ⟨x, hx, rfl⟩
    have hunion : Set.Ico M K ∪ {K} ⊆ Set.Ico M (K + 1) := by
      intro i hi
      rcases hi with ⟨h1i, h2i⟩ | rfl
      · exact ⟨h1i, by omega⟩
      · exact ⟨hMK, by omega⟩
    exact subsetSums_mono hunion (subsetSums_add_mem hdisj hx haK)
  have h2 : IsDense (subsetSums a (Set.Ico M (K + 1))) W (a K) (U + a K) := by
    simpa using isDense_mono hsub2 (isDense_shift hY)
  have hU_mem : U ∈ subsetSums a (Set.Ico M (K + 1)) := by
    refine ⟨Finset.Ico M K, ?_, rfl⟩
    intro i hi
    simp only [Finset.mem_coe, Finset.mem_Ico] at hi
    exact ⟨hi.1, by omega⟩
  intro t _ hUt
  by_cases ht1 : t ≤ U
  · exact h1 t (Nat.zero_le _) ht1
  · by_cases ht2 : a K ≤ t
    · exact h2 t ht2 hUt
    · exact ⟨U, hU_mem, by omega, by omega⟩

/-! ### 4. Alternating `Δ`-Block Theorem (`P (2r + 5)` Density & Width) -/

section AltBlock

/-- Abstract alternating `Δ`-block sequence `b : ℕ → ℕ`:
`b 0 = b₀`, `b 1 = b₁`,
`b (2k) = b (2k - 1) + b (2k - 2) + Δ` (`k ≥ 1`),
`b (2k + 1) = b (2k) + b (2k - 1) - Δ` (`k ≥ 1`). -/
structure AltBlockSpec (b : ℕ → ℕ) (b₀ b₁ Δ : ℕ) : Prop where
  hb0 : b 0 = b₀
  hb1 : b 1 = b₁
  h_le : b₀ ≤ b₁
  h_ub : b₁ ≤ 2 * b₀
  hΔ_pos : 1 ≤ Δ
  hΔ_le : Δ ≤ b₀
  heven : ∀ k : ℕ, 1 ≤ k → b (2 * k) = b (2 * k - 1) + b (2 * k - 2) + Δ
  hodd : ∀ k : ℕ, 1 ≤ k → b (2 * k + 1) + Δ = b (2 * k) + b (2 * k - 1)

def blockSum (b : ℕ → ℕ) (m : ℕ) : ℕ :=
  ∑ i ∈ Finset.range m, b i

def blockSubSums (b : ℕ → ℕ) (m : ℕ) : Set ℕ :=
  subsetSums b (Set.Iio m)

def blockPairs (b : ℕ → ℕ) (Δ m : ℕ) : Set ℕ :=
  {x | x ∈ blockSubSums b m ∧ x + Δ ∈ blockSubSums b m}

lemma blockSum_succ (b : ℕ → ℕ) (m : ℕ) :
    blockSum b (m + 1) = blockSum b m + b m := by
  simp [blockSum, Finset.sum_range_succ]

lemma alt_ge_b0 {b : ℕ → ℕ} {b₀ b₁ Δ : ℕ} (h : AltBlockSpec b b₀ b₁ Δ) :
    ∀ n : ℕ, b₀ ≤ b n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => rw [h.hb0]
    | 1 => rw [h.hb1]; exact h.h_le
    | m + 2 =>
      rcases Nat.even_or_odd (m + 2) with ⟨k, hk⟩ | ⟨k, hk⟩
      · have hk1 : 1 ≤ k := by omega
        have heq : m + 2 = 2 * k := by omega
        rw [heq, h.heven k hk1]
        have h1 := ih (2 * k - 1) (by omega)
        omega
      · have hk1 : 1 ≤ k := by omega
        have heq : m + 2 = 2 * k + 1 := by omega
        rw [heq]
        have hodd := h.hodd k hk1
        have h1 := ih (2 * k) (by omega)
        have h2 := ih (2 * k - 1) (by omega)
        have hΔ := h.hΔ_le
        omega

lemma alt_mono {b : ℕ → ℕ} {b₀ b₁ Δ : ℕ} (h : AltBlockSpec b b₀ b₁ Δ) :
    ∀ n : ℕ, b n ≤ b (n + 1) := by
  intro n
  match n with
  | 0 => rw [h.hb0, h.hb1]; exact h.h_le
  | m + 1 =>
    rcases Nat.even_or_odd (m + 2) with ⟨k, hk⟩ | ⟨k, hk⟩
    · have hk1 : 1 ≤ k := by omega
      have h1 : m + 2 = 2 * k := by omega
      have h2 : m + 1 = 2 * k - 1 := by omega
      rw [h1, h2, h.heven k hk1]
      omega
    · have hk1 : 1 ≤ k := by omega
      have h1 : m + 2 = 2 * k + 1 := by omega
      have h2 : m + 1 = 2 * k := by omega
      rw [h1, h2]
      have hodd := h.hodd k hk1
      have hge := alt_ge_b0 h (2 * k - 1)
      have hΔ := h.hΔ_le
      omega

lemma alt_even_sum {b : ℕ → ℕ} {b₀ b₁ Δ : ℕ} (h : AltBlockSpec b b₀ b₁ Δ) :
    ∀ k : ℕ, 1 ≤ k →
      b (2 * k) = b₁ + blockSum b (2 * k - 1) + Δ ∧
      b (2 * k + 1) = b₁ + blockSum b (2 * k) := by
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk0 : k = 0
    · subst hk0
      have h2 : b 2 = b₁ + b₀ + Δ := by
        have := h.heven 1 (le_refl 1)
        simpa [h.hb0, h.hb1] using this
      have h3 : b 3 + Δ = b 2 + b₁ := by
        have := h.hodd 1 (le_refl 1)
        simpa [h.hb1] using this
      have hs1 : blockSum b 1 = b₀ := by simp [blockSum, h.hb0]
      have hs2 : blockSum b 2 = b₀ + b₁ := by
        simp [blockSum, Finset.sum_range_succ, h.hb0, h.hb1]
      change b 2 = b₁ + blockSum b 1 + Δ ∧ b 3 = b₁ + blockSum b 2
      omega
    · have hk1 : 1 ≤ k := by omega
      obtain ⟨ihe, iho⟩ := ih hk1
      have h2k2 : b (2 * (k + 1)) = b (2 * k + 1) + b (2 * k) + Δ := by
        have := h.heven (k + 1) (by omega)
        have ha : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
        have hb : 2 * (k + 1) - 2 = 2 * k := by omega
        rw [ha, hb] at this
        exact this
      have h2k3 : b (2 * (k + 1) + 1) + Δ = b (2 * (k + 1)) + b (2 * k + 1) := by
        have := h.hodd (k + 1) (by omega)
        have ha : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
        rw [ha] at this
        exact this
      have hs_odd : blockSum b (2 * (k + 1) - 1) = blockSum b (2 * k) + b (2 * k) := by
        have ha : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
        rw [ha, blockSum_succ]
      have hs_even : blockSum b (2 * (k + 1)) = blockSum b (2 * k + 1) + b (2 * k + 1) := by
        have ha : 2 * (k + 1) = 2 * k + 1 + 1 := by omega
        rw [ha, blockSum_succ]
      have hs_even' : blockSum b (2 * k + 1) = blockSum b (2 * k) + b (2 * k) :=
        blockSum_succ b (2 * k)
      omega

/-- Every prefix subset-sum set `blockSubSums b m` (`m ≥ 1`) is `b₀`-gap-dense on `[0, blockSum b m]`. -/
lemma blockSubSums_gapDense {b : ℕ → ℕ} {b₀ b₁ Δ : ℕ} (h : AltBlockSpec b b₀ b₁ Δ) :
    ∀ m : ℕ, 1 ≤ m → IsGapDense (blockSubSums b m) b₀ 0 (blockSum b m) := by
  intro m hm
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases hm0 : m = 0
    · subst hm0
      intro x _ hx
      have hs1 : blockSum b 1 = b₀ := by simp [blockSum, h.hb0]
      rw [hs1] at hx
      refine ⟨0, ⟨∅, by simp, by simp⟩, Nat.zero_le _, by omega⟩
    · by_cases hm1 : m = 1
      · subst hm1
        intro x _ hx
        have hs2 : blockSum b 2 = b₀ + b₁ := by
          simp [blockSum, Finset.sum_range_succ, h.hb0, h.hb1]
        rw [hs2] at hx
        have hmem0 : 0 ∈ blockSubSums b 2 := ⟨∅, by simp, by simp⟩
        have hmem_b0 : b₀ ∈ blockSubSums b 2 :=
          ⟨{0}, by intro i hi; simp at hi; subst hi; simp, by simp [h.hb0]⟩
        have hmem_b1 : b₁ ∈ blockSubSums b 2 :=
          ⟨{1}, by intro i hi; simp at hi; subst hi; simp, by simp [h.hb1]⟩
        have hmem_both : b₀ + b₁ ∈ blockSubSums b 2 := by
          refine ⟨{0, 1}, ?_, ?_⟩
          · intro i hi; simp at hi; rcases hi with rfl | rfl <;> simp
          · simp [h.hb0, h.hb1]
        have hub := h.h_ub
        have hle := h.h_le
        by_cases c1 : x ≤ b₀
        · exact ⟨0, hmem0, Nat.zero_le _, by omega⟩
        · by_cases c2 : x ≤ b₁
          · exact ⟨b₀, hmem_b0, by omega, by omega⟩
          · exact ⟨b₁, hmem_b1, by omega, by omega⟩
      · have hm2 : 2 ≤ m := by omega
        have hprev := ih (by omega)
        have hsub1 : blockSubSums b m ⊆ blockSubSums b (m + 1) :=
          subsetSums_mono (Set.Iio_subset_Iio (Nat.le_succ m))
        have h1 : IsGapDense (blockSubSums b (m + 1)) b₀ 0 (blockSum b m) :=
          isGapDense_mono hsub1 (le_refl _) hprev
        have hdisj : Disjoint (Set.Iio m) ({m} : Set ℕ) := by
          rw [Set.disjoint_singleton_right]
          simp
        have hbm : b m ∈ subsetSums b ({m} : Set ℕ) := ⟨{m}, by simp, by simp⟩
        have hsub2 : (fun x => x + b m) '' blockSubSums b m ⊆ blockSubSums b (m + 1) := by
          rintro z ⟨y, hy, rfl⟩
          have hun : Set.Iio m ∪ {m} ⊆ Set.Iio (m + 1) := by
            intro i hi
            rcases hi with hi | rfl
            · exact Nat.lt_succ_of_lt hi
            · exact Nat.lt_succ_self i
          exact subsetSums_mono hun (subsetSums_add_mem hdisj hy hbm)
        have h2 : IsGapDense (blockSubSums b (m + 1)) b₀ (b m) (blockSum b m + b m) := by
          simpa using isGapDense_mono hsub2 (le_refl _) (isGapDense_shift (c := b m) hprev)
        have hfull : blockSum b m ∈ blockSubSums b (m + 1) := by
          refine ⟨Finset.range m, ?_, rfl⟩
          intro i hi
          simp only [Finset.mem_coe, Finset.mem_range] at hi
          exact Nat.lt_succ_of_lt hi
        have hbm_le : b m ≤ blockSum b m + b₀ := by
          rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
          · have hk1 : 1 ≤ k := by omega
            have heq : m = 2 * k := by omega
            rw [heq]
            have hev := (alt_even_sum h k hk1).1
            have hsm : blockSum b (2 * k) = blockSum b (2 * k - 1) + b (2 * k - 1) := by
              have h1' : 2 * k = (2 * k - 1) + 1 := by omega
              conv_lhs => rw [h1', blockSum_succ]
            have hge := alt_ge_b0 h (2 * k - 1)
            have hub := h.h_ub
            have hΔ := h.hΔ_le
            -- Wait: if k = 1, b 2 = b₁ + b₀ + Δ and blockSum b 2 = b₀ + b₁, so b 2 = blockSum b 2 + Δ ≤ blockSum b 2 + b₀!
            -- If k ≥ 2, b (2k - 1) ≥ b 3 ≥ b₁, so blockSum b (2k) ≥ blockSum b (2k - 1) + b₁!
            by_cases hk2 : k = 1
            · subst hk2
              have h1' : blockSum b 2 = b₀ + b₁ := by
                simp [blockSum, Finset.sum_range_succ, h.hb0, h.hb1]
              have h2' : blockSum b 1 = b₀ := by simp [blockSum, h.hb0]
              simp only [mul_one, show 2 - 1 = 1 from rfl] at hev hsm hge ⊢
              omega
            · have hb1_le : b₁ ≤ b (2 * k - 1) := by
                have hmono : ∀ j : ℕ, 1 ≤ j → b₁ ≤ b j := by
                  intro j hj
                  induction j with
                  | zero => omega
                  | succ j ihj =>
                    by_cases hj0 : j = 0
                    · subst hj0; rw [h.hb1]
                    · exact le_trans (ihj (by omega)) (alt_mono h j)
                exact hmono (2 * k - 1) (by omega)
              omega
          · have hk1 : 1 ≤ k := by omega
            have heq : m = 2 * k + 1 := by omega
            rw [heq]
            have hodd := (alt_even_sum h k hk1).2
            have hsm : blockSum b (2 * k + 1) = blockSum b (2 * k) + b (2 * k) :=
              blockSum_succ b (2 * k)
            have hb1_le : b₁ ≤ b (2 * k) := by
              have hmono : ∀ j : ℕ, 1 ≤ j → b₁ ≤ b j := by
                intro j hj
                induction j with
                | zero => omega
                | succ j ihj =>
                  by_cases hj0 : j = 0
                  · subst hj0; rw [h.hb1]
                  · exact le_trans (ihj (by omega)) (alt_mono h j)
              exact hmono (2 * k) (by omega)
            omega
        rw [blockSum_succ]
        exact isGapDense_union h1 h2 hbm_le hfull

lemma blockSubSums_compl {b : ℕ → ℕ} {m x : ℕ}
    (hx : x ∈ blockSubSums b m) :
    x ≤ blockSum b m ∧ blockSum b m - x ∈ blockSubSums b m := by
  rcases hx with ⟨F, hF, rfl⟩
  have hFsub : F ⊆ Finset.range m := by
    intro i hi
    exact Finset.mem_range.mpr (hF hi)
  have hle : ∑ i ∈ F, b i ≤ blockSum b m :=
    Finset.sum_le_sum_of_subset hFsub
  refine ⟨hle, ?_⟩
  refine ⟨Finset.range m \ F, ?_, ?_⟩
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_range] at hi
    exact hi.1
  · have hadd := Finset.sum_sdiff hFsub (f := b)
    change (∑ i ∈ Finset.range m \ F, b i) + (∑ i ∈ F, b i) = blockSum b m at hadd
    omega

lemma blockPairs_symm {b : ℕ → ℕ} {Δ m x : ℕ}
    (hx : x ∈ blockPairs b Δ m) :
    x + Δ ≤ blockSum b m ∧ blockSum b m - Δ - x ∈ blockPairs b Δ m := by
  rcases hx with ⟨hx0, hx1⟩
  obtain ⟨hle0, hc0⟩ := blockSubSums_compl hx0
  obtain ⟨hle1, hc1⟩ := blockSubSums_compl hx1
  refine ⟨hle1, ?_, ?_⟩
  · have heq : blockSum b m - Δ - x = blockSum b m - (x + Δ) := by omega
    rw [heq]
    exact hc1
  · have heq : blockSum b m - Δ - x + Δ = blockSum b m - x := by omega
    rw [heq]
    exact hc0

lemma blockPairs_mono {b : ℕ → ℕ} {Δ m₁ m₂ : ℕ} (hm : m₁ ≤ m₂) :
    blockPairs b Δ m₁ ⊆ blockPairs b Δ m₂ := by
  intro x ⟨h1, h2⟩
  have hs := subsetSums_mono (a := b) (Set.Iio_subset_Iio hm)
  exact ⟨hs h1, hs h2⟩

lemma blockPairs_add_term {b : ℕ → ℕ} {Δ m : ℕ} :
    (fun x => x + b m) '' blockPairs b Δ m ⊆ blockPairs b Δ (m + 1) := by
  rintro z ⟨x, ⟨h1, h2⟩, rfl⟩
  have hdisj : Disjoint (Set.Iio m) ({m} : Set ℕ) := by
    rw [Set.disjoint_singleton_right]; simp
  have hbm : b m ∈ subsetSums b ({m} : Set ℕ) := ⟨{m}, by simp, by simp⟩
  have hun : Set.Iio m ∪ {m} ⊆ Set.Iio (m + 1) := by
    intro i hi
    rcases hi with hi | rfl
    · exact Nat.lt_succ_of_lt hi
    · exact Nat.lt_succ_self i
  refine ⟨subsetSums_mono hun (subsetSums_add_mem hdisj h1 hbm), ?_⟩
  have heq : x + b m + Δ = (x + Δ) + b m := by omega
  rw [heq]
  exact subsetSums_mono hun (subsetSums_add_mem hdisj h2 hbm)

/-- Telescoping even chain: for every `r : ℕ` and `j ≤ r + 1`,
`b (2r + 2) - j * Δ ∈ blockSubSums b (2r + 3)` and `j * Δ ≤ b (2r + 2)`. -/
lemma alt_telescope_even {b : ℕ → ℕ} {b₀ b₁ Δ : ℕ} (h : AltBlockSpec b b₀ b₁ Δ) :
    ∀ r : ℕ, ∀ j : ℕ, j ≤ r + 1 →
      j * Δ ≤ b (2 * r + 2) ∧ b (2 * r + 2) - j * Δ ∈ blockSubSums b (2 * r + 3) := by
  intro r
  induction r with
  | zero =>
    intro j hj
    have h2 : b 2 = b₁ + b₀ + Δ := by
      have := h.heven 1 (le_refl 1)
      simpa [h.hb0, h.hb1] using this
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · refine ⟨by omega, ?_⟩
      simp only [zero_mul, Nat.sub_zero]
      exact ⟨{2}, by intro i hi; simp at hi; subst hi; simp, by simp⟩
    · simp only [mul_zero, zero_add, one_mul]
      refine ⟨by omega, ?_⟩
      have heq : b 2 - Δ = b 0 + b 1 := by rw [h2, h.hb0, h.hb1]; omega
      rw [heq]
      refine ⟨{0, 1}, ?_, ?_⟩
      · intro i hi; simp at hi; rcases hi with rfl | rfl <;> simp
      · simp
  | succ r ih =>
    intro j hj
    have hstep : b (2 * (r + 1) + 2) = b (2 * r + 3) + b (2 * r + 2) + Δ := by
      have := h.heven (r + 2) (by omega)
      have h1 : 2 * (r + 2) = 2 * (r + 1) + 2 := by omega
      have h2 : 2 * (r + 2) - 1 = 2 * r + 3 := by omega
      have h3 : 2 * (r + 2) - 2 = 2 * r + 2 := by omega
      rw [h3, h2, h1] at this
      exact this
    by_cases hj0 : j = 0
    · subst hj0
      refine ⟨by omega, ?_⟩
      simp only [zero_mul, Nat.sub_zero]
      exact ⟨{2 * (r + 1) + 2}, by intro i hi; simp at hi; subst hi; simp, by simp⟩
    · obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
      obtain ⟨h1, hmem⟩ := ih j' (by omega)
      have hmul : j'.succ * Δ = j' * Δ + Δ := Nat.succ_mul j' Δ
      refine ⟨by omega, ?_⟩
      have heq : b (2 * (r + 1) + 2) - j'.succ * Δ =
          (b (2 * r + 2) - j' * Δ) + b (2 * r + 3) := by
        rw [hstep, hmul]
        omega
      rw [heq]
      have hdisj : Disjoint (Set.Iio (2 * r + 3)) ({2 * r + 3} : Set ℕ) := by
        rw [Set.disjoint_singleton_right]; simp
      have hterm : b (2 * r + 3) ∈ subsetSums b ({2 * r + 3} : Set ℕ) := ⟨{2 * r + 3}, by simp, by simp⟩
      have hun : Set.Iio (2 * r + 3) ∪ {2 * r + 3} ⊆ Set.Iio (2 * (r + 1) + 3) := by
        intro i hi
        rcases hi with hi | rfl
        · simp only [Set.mem_Iio] at hi ⊢; omega
        · simp only [Set.mem_Iio]; omega
      exact subsetSums_mono hun (subsetSums_add_mem hdisj hmem hterm)

lemma alt_telescope_pairs {b : ℕ → ℕ} {b₀ b₁ Δ : ℕ} (h : AltBlockSpec b b₀ b₁ Δ)
    (r j : ℕ) (hj1 : 1 ≤ j) (hjr : j ≤ r + 1) :
    b (2 * r + 2) - j * Δ ∈ blockPairs b Δ (2 * r + 3) := by
  obtain ⟨hle1, hm1⟩ := alt_telescope_even h r j hjr
  obtain ⟨hle2, hm2⟩ := alt_telescope_even h r (j - 1) (by omega)
  refine ⟨hm1, ?_⟩
  have heq : b (2 * r + 2) - j * Δ + Δ = b (2 * r + 2) - (j - 1) * Δ := by
    have hmul : j * Δ = (j - 1) * Δ + Δ := by
      cases j with
      | zero => omega
      | succ k => simp [Nat.add_mul]
    omega
  rw [heq]
  exact hm2

/-- Even shift lemma: `(b (2k + 2) - Δ) + x ∈ blockPairs b Δ (2k + 3)` for every `x ∈ blockSubSums b (2k)`. -/
lemma alt_shift_sigma_even {b : ℕ → ℕ} {b₀ b₁ Δ : ℕ} (h : AltBlockSpec b b₀ b₁ Δ)
    (k : ℕ) :
    (fun x => x + (b (2 * k + 2) - Δ)) '' blockSubSums b (2 * k) ⊆ blockPairs b Δ (2 * k + 3) := by
  have hstep : b (2 * k + 2) = b (2 * k + 1) + b (2 * k) + Δ := by
    have := h.heven (k + 1) (by omega)
    have h1 : 2 * (k + 1) = 2 * k + 2 := by omega
    have h2 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
    have h3 : 2 * (k + 1) - 2 = 2 * k := by omega
    rw [h3, h2, h1] at this
    exact this
  rintro z ⟨x, hx, rfl⟩
  have hdisj : Disjoint (Set.Iio (2 * k)) ({2 * k, 2 * k + 1, 2 * k + 2} : Set ℕ) := by
    rw [Set.disjoint_left]
    intro i hi hmem
    simp only [Set.mem_Iio] at hi
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    omega
  have hun : Set.Iio (2 * k) ∪ {2 * k, 2 * k + 1, 2 * k + 2} ⊆ Set.Iio (2 * k + 3) := by
    intro i hi
    simp only [Set.mem_union, Set.mem_Iio, Set.mem_insert_iff, Set.mem_singleton_iff] at hi ⊢
    omega
  have hmem1 : b (2 * k + 2) - Δ ∈ subsetSums b ({2 * k, 2 * k + 1, 2 * k + 2} : Set ℕ) := by
    refine ⟨{2 * k, 2 * k + 1}, ?_, ?_⟩
    · intro i hi
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hi
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      omega
    · have hne : 2 * k ≠ 2 * k + 1 := by omega
      rw [Finset.sum_pair hne]
      omega
  have hmem2 : b (2 * k + 2) ∈ subsetSums b ({2 * k, 2 * k + 1, 2 * k + 2} : Set ℕ) := by
    refine ⟨{2 * k + 2}, ?_, by simp⟩
    intro i hi
    simp only [Finset.mem_coe, Finset.mem_singleton] at hi
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  refine ⟨subsetSums_mono hun (subsetSums_add_mem hdisj hx hmem1), ?_⟩
  have heq : x + (b (2 * k + 2) - Δ) + Δ = x + b (2 * k + 2) := by omega
  rw [heq]
  exact subsetSums_mono hun (subsetSums_add_mem hdisj hx hmem2)

/-- Odd shift lemma: `b (2k + 3) + x ∈ blockPairs b Δ (2k + 4)` for every `x ∈ blockSubSums b (2k + 1)`. -/
lemma alt_shift_sigma_odd {b : ℕ → ℕ} {b₀ b₁ Δ : ℕ} (h : AltBlockSpec b b₀ b₁ Δ)
    (k : ℕ) :
    (fun x => x + b (2 * k + 3)) '' blockSubSums b (2 * k + 1) ⊆ blockPairs b Δ (2 * k + 4) := by
  have hstep : b (2 * k + 3) + Δ = b (2 * k + 2) + b (2 * k + 1) := by
    have := h.hodd (k + 1) (by omega)
    have h1 : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
    have h2 : 2 * (k + 1) = 2 * k + 2 := by omega
    have h3 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
    rw [h1, h3, h2] at this
    exact this
  rintro z ⟨x, hx, rfl⟩
  have hdisj : Disjoint (Set.Iio (2 * k + 1)) ({2 * k + 1, 2 * k + 2, 2 * k + 3} : Set ℕ) := by
    rw [Set.disjoint_left]
    intro i hi hmem
    simp only [Set.mem_Iio] at hi
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    omega
  have hun : Set.Iio (2 * k + 1) ∪ {2 * k + 1, 2 * k + 2, 2 * k + 3} ⊆ Set.Iio (2 * k + 4) := by
    intro i hi
    simp only [Set.mem_union, Set.mem_Iio, Set.mem_insert_iff, Set.mem_singleton_iff] at hi ⊢
    omega
  have hmem1 : b (2 * k + 3) ∈ subsetSums b ({2 * k + 1, 2 * k + 2, 2 * k + 3} : Set ℕ) := by
    refine ⟨{2 * k + 3}, ?_, by simp⟩
    intro i hi
    simp only [Finset.mem_coe, Finset.mem_singleton] at hi
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  have hmem2 : b (2 * k + 3) + Δ ∈ subsetSums b ({2 * k + 1, 2 * k + 2, 2 * k + 3} : Set ℕ) := by
    refine ⟨{2 * k + 1, 2 * k + 2}, ?_, ?_⟩
    · intro i hi
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hi
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      omega
    · have hne : 2 * k + 1 ≠ 2 * k + 2 := by omega
      rw [Finset.sum_pair hne]
      omega
  refine ⟨subsetSums_mono hun (subsetSums_add_mem hdisj hx hmem1), ?_⟩
  have heq : x + b (2 * k + 3) + Δ = x + (b (2 * k + 3) + Δ) := by omega
  rw [heq]
  exact subsetSums_mono hun (subsetSums_add_mem hdisj hx hmem2)

/-- Helper: a `Δ`-step chain `[base, base + n * Δ]` is `G`-gap-dense whenever `Δ ≤ G`. -/
lemma isGapDense_arith {P : Set ℕ} {base Δ G n : ℕ}
    (hΔpos : 1 ≤ Δ) (hΔG : Δ ≤ G)
    (hmem : ∀ j ≤ n, base + j * Δ ∈ P) :
    IsGapDense P G base (base + n * Δ) := by
  intro x hlo hhi
  set q := (x - base) / Δ
  have hq_le : q ≤ n := by
    have : (x - base) / Δ ≤ (n * Δ) / Δ := Nat.div_le_div_right (by omega)
    rwa [Nat.mul_div_cancel n (by omega)] at this
  refine ⟨base + q * Δ, hmem q hq_le, ?_, ?_⟩
  · have h1 : q * Δ ≤ x - base := Nat.div_mul_le_self (x - base) Δ
    omega
  · have hlt : x - base < q * Δ + Δ :=
      Nat.lt_div_mul_add (a := x - base) (b := Δ) (by omega)
    omega

/-- Base theorem at `m = 2r + 3`: `blockPairs b Δ (2r + 3)` is `(b₁ - r * Δ)`-gap-dense on
`[A_r, S (2r + 3) - Δ - A_r]` where `A_r = b (2r + 2) - (r + 1) * Δ`. -/
theorem blockPairs_dense_base {b : ℕ → ℕ} {b₀ b₁ Δ : ℕ} (h : AltBlockSpec b b₀ b₁ Δ)
    {r : ℕ} (hr : 1 ≤ r) (hG : b₀ + Δ ≤ b₁ - r * Δ) :
    let G := b₁ - r * Δ
    let A := b (2 * r + 2) - (r + 1) * Δ
    IsGapDense (blockPairs b Δ (2 * r + 3)) G A (blockSum b (2 * r + 3) - Δ - A) ∧
    A ∈ blockPairs b Δ (2 * r + 3) ∧
    blockSum b (2 * r + 3) - Δ - A ∈ blockPairs b Δ (2 * r + 3) := by
  intro G A
  have hA_mem : A ∈ blockPairs b Δ (2 * r + 3) :=
    alt_telescope_pairs h r (r + 1) (by omega) (le_refl _)
  obtain ⟨hA_le, hB_mem⟩ := blockPairs_symm hA_mem
  have hΔ_le_G : Δ ≤ G := by omega
  have hb0_le_G : b₀ ≤ G := by omega
  have h_even_r := alt_telescope_even h r (r + 1) (le_refl _)
  have h_b2r2 : b (2 * r + 2) = b₁ + blockSum b (2 * r + 1) + Δ := by
    have := (alt_even_sum h (r + 1) (by omega)).1
    have h1 : 2 * (r + 1) = 2 * r + 2 := by omega
    have h2 : 2 * (r + 1) - 1 = 2 * r + 1 := by omega
    rw [h2, h1] at this
    exact this
  have h_b2r3 : b (2 * r + 3) = b₁ + blockSum b (2 * r + 2) := by
    have := (alt_even_sum h (r + 1) (by omega)).2
    have h1 : 2 * (r + 1) + 1 = 2 * r + 3 := by omega
    have h2 : 2 * (r + 1) = 2 * r + 2 := by omega
    rw [h1, h2] at this
    exact this
  have h_b2r1 : b (2 * r + 1) = b₁ + blockSum b (2 * r) := (alt_even_sum h r hr).2
  have h_S2r3 : blockSum b (2 * r + 3) = blockSum b (2 * r + 2) + b (2 * r + 2) :=
    blockSum_succ b (2 * r + 2)
  -- Left arithmetic chain: `[A, b (2r + 2) - Δ]`
  have hleft : IsGapDense (blockPairs b Δ (2 * r + 3)) G A (b (2 * r + 2) - Δ) := by
    have hend : A + r * Δ = b (2 * r + 2) - Δ := by
      have : (r + 1) * Δ = r * Δ + Δ := by ring
      have := h_even_r.1
      omega
    rw [← hend]
    apply isGapDense_arith h.hΔ_pos hΔ_le_G
    intro j hj
    have heq : A + j * Δ = b (2 * r + 2) - (r + 1 - j) * Δ := by
      have h1 : (r + 1 - j) * Δ + j * Δ = (r + 1) * Δ := by
        rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
      have := h_even_r.1
      omega
    rw [heq]
    exact alt_telescope_pairs h r (r + 1 - j) (by omega) (by omega)
  -- Middle shifted `Σ (2r)`: `[b (2r + 2) - Δ, b (2r + 2) - Δ + S (2r)]`
  have hmid : IsGapDense (blockPairs b Δ (2 * r + 3)) G
      (b (2 * r + 2) - Δ) (b (2 * r + 2) - Δ + blockSum b (2 * r)) := by
    have hsig := blockSubSums_gapDense h (2 * r) (by omega)
    have hsh := isGapDense_shift (c := b (2 * r + 2) - Δ) hsig
    have h1 : 0 + (b (2 * r + 2) - Δ) = b (2 * r + 2) - Δ := by omega
    have h2 : blockSum b (2 * r) + (b (2 * r + 2) - Δ) = b (2 * r + 2) - Δ + blockSum b (2 * r) := by omega
    rw [h1, h2] at hsh
    exact isGapDense_mono (alt_shift_sigma_even h r) hb0_le_G hsh
  -- Right arithmetic chain (symmetric complement of left!): `[b (2r + 2) - Δ + S (2r), S (2r + 3) - Δ - A]`
  have hmid_hi_eq : b (2 * r + 2) - Δ + blockSum b (2 * r) = blockSum b (2 * r + 2) := by
    have hodd := h.hodd (r + 1) (by omega)
    have ha : 2 * (r + 1) + 1 = 2 * r + 3 := by omega
    have hb : 2 * (r + 1) = 2 * r + 2 := by omega
    have hc : 2 * (r + 1) - 1 = 2 * r + 1 := by omega
    rw [ha, hc, hb] at hodd
    have := h_even_r.1
    omega
  have hright : IsGapDense (blockPairs b Δ (2 * r + 3)) G
      (blockSum b (2 * r + 2)) (blockSum b (2 * r + 3) - Δ - A) := by
    have hend : blockSum b (2 * r + 2) + r * Δ = blockSum b (2 * r + 3) - Δ - A := by
      have : (r + 1) * Δ = r * Δ + Δ := by ring
      have := h_even_r.1
      omega
    rw [← hend]
    apply isGapDense_arith h.hΔ_pos hΔ_le_G
    intro j hj
    have htel := alt_telescope_pairs h r (j + 1) (by omega) (by omega)
    have hsym := (blockPairs_symm htel).2
    have heq : blockSum b (2 * r + 3) - Δ - (b (2 * r + 2) - (j + 1) * Δ) =
        blockSum b (2 * r + 2) + j * Δ := by
      have h1 : (j + 1) * Δ = j * Δ + Δ := by ring
      have h2 := (alt_telescope_even h r (j + 1) (by omega)).1
      omega
    rwa [heq] at hsym
  have hmem_m1 : b (2 * r + 2) - Δ ∈ blockPairs b Δ (2 * r + 3) := by
    simpa using alt_telescope_pairs h r 1 (le_refl 1) (by omega)
  have hmem_m2 : blockSum b (2 * r + 2) ∈ blockPairs b Δ (2 * r + 3) := by
    have hsym := (blockPairs_symm hmem_m1).2
    have heq : blockSum b (2 * r + 3) - Δ - (b (2 * r + 2) - Δ) = blockSum b (2 * r + 2) := by
      have := h_even_r.1
      omega
    rwa [heq] at hsym
  have hlm : IsGapDense (blockPairs b Δ (2 * r + 3)) G A (blockSum b (2 * r + 2)) := by
    rw [← hmid_hi_eq]
    exact isGapDense_union hleft hmid (by omega) hmem_m1
  exact ⟨isGapDense_union hlm hright (by omega) hmem_m2, hA_mem, hB_mem⟩

/-- Step 1 (`m = 2r + 4`) and Step 2 (`m = 2r + 5`): `blockPairs b Δ (2r + 5)` is `(b₁ - r * Δ)`-gap-dense
on `[A_r, S (2r + 5) - Δ - A_r]` with total span exceeding `b (2r + 5)`. -/
theorem blockPairs_dense_2r5 {b : ℕ → ℕ} {b₀ b₁ Δ : ℕ} (h : AltBlockSpec b b₀ b₁ Δ)
    {r : ℕ} (hr : 1 ≤ r) (hG : b₀ + Δ ≤ b₁ - r * Δ) :
    let G := b₁ - r * Δ
    let A := b (2 * r + 2) - (r + 1) * Δ
    let B := blockSum b (2 * r + 5) - Δ - A
    IsGapDense (blockPairs b Δ (2 * r + 5)) G A B ∧
    A ∈ blockPairs b Δ (2 * r + 5) ∧
    B ∈ blockPairs b Δ (2 * r + 5) ∧
    b (2 * r + 5) ≤ B - A := by
  intro G A B
  obtain ⟨hbase, hA23, hB23⟩ := blockPairs_dense_base h hr hG
  have hb0_le_G : b₀ ≤ G := by omega
  have h_even_r := (alt_telescope_even h r (r + 1) (le_refl _)).1
  have h_b2r2 : b (2 * r + 2) = b₁ + blockSum b (2 * r + 1) + Δ := by
    have := (alt_even_sum h (r + 1) (by omega)).1
    have h1 : 2 * (r + 1) = 2 * r + 2 := by omega
    have h2 : 2 * (r + 1) - 1 = 2 * r + 1 := by omega
    rw [h2, h1] at this; exact this
  have h_b2r3 : b (2 * r + 3) = b₁ + blockSum b (2 * r + 2) := by
    have := (alt_even_sum h (r + 1) (by omega)).2
    have h1 : 2 * (r + 1) + 1 = 2 * r + 3 := by omega
    have h2 : 2 * (r + 1) = 2 * r + 2 := by omega
    rw [h1, h2] at this; exact this
  have h_b2r4 : b (2 * r + 4) = b₁ + blockSum b (2 * r + 3) + Δ := by
    have := (alt_even_sum h (r + 2) (by omega)).1
    have h1 : 2 * (r + 2) = 2 * r + 4 := by omega
    have h2 : 2 * (r + 2) - 1 = 2 * r + 3 := by omega
    rw [h2, h1] at this; exact this
  have h_b2r5 : b (2 * r + 5) = b₁ + blockSum b (2 * r + 4) := by
    have := (alt_even_sum h (r + 2) (by omega)).2
    have h1 : 2 * (r + 2) + 1 = 2 * r + 5 := by omega
    have h2 : 2 * (r + 2) = 2 * r + 4 := by omega
    rw [h1, h2] at this; exact this
  have h_b2r3_rec : b (2 * r + 3) + Δ = b (2 * r + 2) + b (2 * r + 1) := by
    have := h.hodd (r + 1) (by omega)
    have h1 : 2 * (r + 1) + 1 = 2 * r + 3 := by omega
    have h2 : 2 * (r + 1) = 2 * r + 2 := by omega
    have h3 : 2 * (r + 1) - 1 = 2 * r + 1 := by omega
    rw [h1, h3, h2] at this; exact this
  have h_b2r4_rec : b (2 * r + 4) = b (2 * r + 3) + b (2 * r + 2) + Δ := by
    have := h.heven (r + 2) (by omega)
    have h1 : 2 * (r + 2) = 2 * r + 4 := by omega
    have h2 : 2 * (r + 2) - 1 = 2 * r + 3 := by omega
    have h3 : 2 * (r + 2) - 2 = 2 * r + 2 := by omega
    rw [h3, h2, h1] at this; exact this
  have h_S2r3 : blockSum b (2 * r + 3) = blockSum b (2 * r + 2) + b (2 * r + 2) :=
    blockSum_succ b (2 * r + 2)
  have h_S2r4 : blockSum b (2 * r + 4) = blockSum b (2 * r + 3) + b (2 * r + 3) :=
    blockSum_succ b (2 * r + 3)
  have h_S2r5 : blockSum b (2 * r + 5) = blockSum b (2 * r + 4) + b (2 * r + 4) :=
    blockSum_succ b (2 * r + 4)
  have hb1_le_b2r1 : b₁ ≤ b (2 * r + 1) := by
    have hmono : ∀ j : ℕ, 1 ≤ j → b₁ ≤ b j := by
      intro j hj
      induction j with
      | zero => omega
      | succ j ihj =>
        by_cases hj0 : j = 0
        · subst hj0; rw [h.hb1]
        · exact le_trans (ihj (by omega)) (alt_mono h j)
    exact hmono (2 * r + 1) (by omega)
  -- Step 1: `m = 2r + 4`
  have h24 : IsGapDense (blockPairs b Δ (2 * r + 4)) G A (blockSum b (2 * r + 4) - Δ - A) := by
    have hI1 : IsGapDense (blockPairs b Δ (2 * r + 4)) G A (blockSum b (2 * r + 3) - Δ - A) :=
      isGapDense_mono (blockPairs_mono (by omega)) (le_refl _) hbase
    have hI2 : IsGapDense (blockPairs b Δ (2 * r + 4)) G
        (b (2 * r + 3) + A) (blockSum b (2 * r + 4) - Δ - A) := by
      have hsh := isGapDense_shift (c := b (2 * r + 3)) hbase
      have h1 : A + b (2 * r + 3) = b (2 * r + 3) + A := by omega
      have h2 : blockSum b (2 * r + 3) - Δ - A + b (2 * r + 3) =
          blockSum b (2 * r + 4) - Δ - A := by
        have := (blockPairs_symm hA23).1
        omega
      rw [h1, h2] at hsh
      exact isGapDense_mono (blockPairs_add_term) (le_refl _) hsh
    have hMid : IsGapDense (blockPairs b Δ (2 * r + 4)) G
        (b (2 * r + 3)) (b (2 * r + 3) + blockSum b (2 * r + 1)) := by
      have hsig := blockSubSums_gapDense h (2 * r + 1) (by omega)
      have hsh := isGapDense_shift (c := b (2 * r + 3)) hsig
      have h1 : 0 + b (2 * r + 3) = b (2 * r + 3) := by omega
      have h2 : blockSum b (2 * r + 1) + b (2 * r + 3) = b (2 * r + 3) + blockSum b (2 * r + 1) := by omega
      rw [h1, h2] at hsh
      exact isGapDense_mono (alt_shift_sigma_odd h r) hb0_le_G hsh
    have hB23_in24 : blockSum b (2 * r + 3) - Δ - A ∈ blockPairs b Δ (2 * r + 4) :=
      blockPairs_mono (by omega) hB23
    have hMid_hi_in24 : b (2 * r + 3) + blockSum b (2 * r + 1) ∈ blockPairs b Δ (2 * r + 4) := by
      apply alt_shift_sigma_odd h r
      refine ⟨blockSum b (2 * r + 1), ?_, by dsimp only; omega⟩
      exact ⟨Finset.range (2 * r + 1), fun i hi => Finset.mem_range.mp hi, rfl⟩
    have hov1 : b (2 * r + 3) ≤ (blockSum b (2 * r + 3) - Δ - A) + G := by
      have : (r + 1) * Δ = r * Δ + Δ := by ring
      omega
    have hov2 : b (2 * r + 3) + A ≤ (b (2 * r + 3) + blockSum b (2 * r + 1)) + G := by
      have : (r + 1) * Δ = r * Δ + Δ := by ring
      omega
    have h12 := isGapDense_union hI1 hMid hov1 hB23_in24
    exact isGapDense_union h12 hI2 hov2 hMid_hi_in24
  -- Step 2: `m = 2r + 5`
  have hA24 : A ∈ blockPairs b Δ (2 * r + 4) := blockPairs_mono (by omega) hA23
  have hB24 : blockSum b (2 * r + 4) - Δ - A ∈ blockPairs b Δ (2 * r + 4) := (blockPairs_symm hA24).2
  have h25 : IsGapDense (blockPairs b Δ (2 * r + 5)) G A B := by
    have hI1 : IsGapDense (blockPairs b Δ (2 * r + 5)) G A (blockSum b (2 * r + 4) - Δ - A) :=
      isGapDense_mono (blockPairs_mono (by omega)) (le_refl _) h24
    have hI2 : IsGapDense (blockPairs b Δ (2 * r + 5)) G (b (2 * r + 4) + A) B := by
      have hsh := isGapDense_shift (c := b (2 * r + 4)) h24
      have h1 : A + b (2 * r + 4) = b (2 * r + 4) + A := by omega
      have h2 : blockSum b (2 * r + 4) - Δ - A + b (2 * r + 4) = B := by
        have := (blockPairs_symm hA24).1
        omega
      rw [h1, h2] at hsh
      exact isGapDense_mono (blockPairs_add_term) (le_refl _) hsh
    have hMid : IsGapDense (blockPairs b Δ (2 * r + 5)) G
        (b (2 * r + 4) - Δ) (b (2 * r + 4) - Δ + blockSum b (2 * r + 2)) := by
      have hsig := blockSubSums_gapDense h (2 * r + 2) (by omega)
      have hsh := isGapDense_shift (c := b (2 * r + 4) - Δ) hsig
      have h1 : 0 + (b (2 * r + 4) - Δ) = b (2 * r + 4) - Δ := by omega
      have h2 : blockSum b (2 * r + 2) + (b (2 * r + 4) - Δ) =
          b (2 * r + 4) - Δ + blockSum b (2 * r + 2) := by omega
      rw [h1, h2] at hsh
      exact isGapDense_mono (alt_shift_sigma_even h (r + 1)) hb0_le_G hsh
    have hB24_in25 : blockSum b (2 * r + 4) - Δ - A ∈ blockPairs b Δ (2 * r + 5) :=
      blockPairs_mono (by omega) hB24
    have hMid_hi_in25 : b (2 * r + 4) - Δ + blockSum b (2 * r + 2) ∈ blockPairs b Δ (2 * r + 5) := by
      have h25 : 2 * (r + 1) + 3 = 2 * r + 5 := by omega
      have h24 : 2 * (r + 1) + 2 = 2 * r + 4 := by omega
      have h22 : 2 * (r + 1) = 2 * r + 2 := by omega
      rw [← h25, ← h24, ← h22]
      apply alt_shift_sigma_even h (r + 1)
      refine ⟨blockSum b (2 * (r + 1)), ?_, by dsimp only; omega⟩
      exact ⟨Finset.range (2 * (r + 1)), fun i hi => Finset.mem_range.mp hi, rfl⟩
    have hov1 : b (2 * r + 4) - Δ ≤ (blockSum b (2 * r + 4) - Δ - A) + G := by
      have : (r + 1) * Δ = r * Δ + Δ := by ring
      omega
    have hov2 : b (2 * r + 4) + A ≤ (b (2 * r + 4) - Δ + blockSum b (2 * r + 2)) + G := by
      have : (r + 1) * Δ = r * Δ + Δ := by ring
      omega
    have h12 := isGapDense_union hI1 hMid hov1 hB24_in25
    exact isGapDense_union h12 hI2 hov2 hMid_hi_in25
  have hA25 : A ∈ blockPairs b Δ (2 * r + 5) := blockPairs_mono (by omega) hA24
  have hB25 : B ∈ blockPairs b Δ (2 * r + 5) := (blockPairs_symm hA25).2
  have hwidth : b (2 * r + 5) ≤ B - A := by
    have : (r + 1) * Δ = r * Δ + Δ := by ring
    have := (blockPairs_symm hA25).1
    omega
  exact ⟨h25, hA25, hB25, hwidth⟩

end AltBlock

/-! ### 5. Connecting `AltBlockSpec` to `seqOfDisp` and Building the Infinite Stage Machine -/

/-- Pure canonical alternating `Δ`-sequence defined for ALL `n : ℕ`. -/
def altSeq (b₀ b₁ Δ : ℕ) : ℕ → ℕ
  | 0 => b₀
  | 1 => b₁
  | n + 2 =>
    if (n + 2) % 2 = 0 then
      altSeq b₀ b₁ Δ (n + 1) + altSeq b₀ b₁ Δ n + Δ
    else
      altSeq b₀ b₁ Δ (n + 1) + altSeq b₀ b₁ Δ n - Δ

lemma altSeq_ge_b0 {b₀ b₁ Δ : ℕ} (hle : b₀ ≤ b₁) (hΔ : Δ ≤ b₀) :
    ∀ n : ℕ, b₀ ≤ altSeq b₀ b₁ Δ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => simp [altSeq]
    | 1 => simp [altSeq, hle]
    | m + 2 =>
      simp only [altSeq]
      split_ifs
      · have h1 := ih (m + 1) (by omega)
        omega
      · have h1 := ih (m + 1) (by omega)
        have h2 := ih m (by omega)
        omega

lemma altSeq_spec {b₀ b₁ Δ : ℕ} (hle : b₀ ≤ b₁) (hub : b₁ ≤ 2 * b₀)
    (hΔpos : 1 ≤ Δ) (hΔle : Δ ≤ b₀) :
    AltBlockSpec (altSeq b₀ b₁ Δ) b₀ b₁ Δ where
  hb0 := rfl
  hb1 := rfl
  h_le := hle
  h_ub := hub
  hΔ_pos := hΔpos
  hΔ_le := hΔle
  heven := by
    intro k hk
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
    have h1 : 2 * (1 + m) = 2 * m + 2 := by omega
    have h2 : 2 * (1 + m) - 1 = 2 * m + 1 := by omega
    have h3 : 2 * (1 + m) - 2 = 2 * m := by omega
    rw [h3, h2, h1, altSeq]
    have hmod : (2 * m + 2) % 2 = 0 := by omega
    simp [hmod]
  hodd := by
    intro k hk
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
    have h1 : 2 * (1 + m) + 1 = (2 * m + 1) + 2 := by omega
    have h2 : 2 * (1 + m) = (2 * m + 1) + 1 := by omega
    have h3 : 2 * (1 + m) - 1 = 2 * m + 1 := by omega
    rw [h1, h3, h2, altSeq]
    have hmod : (2 * m + 1 + 2) % 2 ≠ 0 := by omega
    simp only [hmod, ↓reduceIte]
    have hge := altSeq_ge_b0 hle hΔle (2 * m + 1)
    omega

/-- Exact agreement between `seqOfDisp d (K + 1 + j)` and `altSeq (prefSum d K) (prefSum d (K + 1)) Δ j`
across the entire `(2r + 5)`-term gadget (plus the next term `j = 2r + 5` when `d (K + 2r + 5) = 0`). -/
lemma seqOfDisp_eq_altSeq {d : ℕ → ℕ} {K r Δ : ℕ} (hK : 4 ≤ K)
    (hle : prefSum d K ≤ prefSum d (K + 1)) (hΔle : Δ ≤ prefSum d K)
    (h0 : d K = 0) (h1 : d (K + 1) = 0)
    (halt : ∀ j < 2 * r + 3, d (K + 2 + j) = if j % 2 = 0 then Δ else 0) :
    ∀ j < 2 * r + 5,
      seqOfDisp d (K + 1 + j) = altSeq (prefSum d K) (prefSum d (K + 1)) Δ j := by
  intro j hj
  induction j using Nat.strong_induction_on with
  | h j ih =>
    match j with
    | 0 =>
      simp only [add_zero, altSeq]
      rw [seqOfDisp_succ_eq d (by omega), h0, add_zero]
    | 1 =>
      simp only [altSeq]
      have heq : K + 1 + 1 = (K + 1) + 1 := by omega
      rw [heq, seqOfDisp_succ_eq d (by omega), h1, add_zero]
    | m + 2 =>
      have hm_lt : m < 2 * r + 3 := by omega
      have hdm : d (K + 2 + m) = if m % 2 = 0 then Δ else 0 := halt m hm_lt
      have h_prev_d : d (K + 1 + m) = if m = 0 then 0 else if (m - 1) % 2 = 0 then Δ else 0 := by
        by_cases hm0 : m = 0
        · subst hm0; simpa using h1
        · have := halt (m - 1) (by omega)
          have heq : K + 2 + (m - 1) = K + 1 + m := by omega
          rw [heq] at this
          simp [hm0, this]
      have ha_cur : seqOfDisp d (K + 1 + (m + 2)) =
          prefSum d (K + 2 + m) + d (K + 2 + m) := by
        have heq : K + 1 + (m + 2) = (K + 2 + m) + 1 := by omega
        rw [heq, seqOfDisp_succ_eq d (by omega)]
      have ha_prev : seqOfDisp d (K + 1 + (m + 1)) =
          prefSum d (K + 1 + m) + d (K + 1 + m) := by
        have heq : K + 1 + (m + 1) = (K + 1 + m) + 1 := by omega
        rw [heq, seqOfDisp_succ_eq d (by omega)]
      have hps : prefSum d (K + 2 + m) = prefSum d (K + 1 + m) + seqOfDisp d (K + 1 + m) := by
        have heq : K + 2 + m = (K + 1 + m) + 1 := by omega
        rw [heq, prefSum_succ]
      have ih1 := ih (m + 1) (by omega) (by omega)
      have ih0 := ih m (by omega) (by omega)
      simp only [altSeq]
      rw [← ih1, ← ih0]
      split_ifs with hmod
      · have hm_even : m % 2 = 0 := by omega
        rw [hdm] at ha_cur
        simp only [hm_even, ↓reduceIte] at ha_cur
        have hd_prev_zero : d (K + 1 + m) = 0 := by
          rw [h_prev_d]
          by_cases hm0 : m = 0
          · simp [hm0]
          · have hodd : (m - 1) % 2 ≠ 0 := by omega
            simp [hm0, hodd]
        rw [hd_prev_zero, add_zero] at ha_prev
        omega
      · have hm_odd : m % 2 ≠ 0 := by omega
        rw [hdm] at ha_cur
        simp only [hm_odd, ↓reduceIte, add_zero] at ha_cur
        have hm_ne0 : m ≠ 0 := by omega
        have hd_prev_eq : d (K + 1 + m) = Δ := by
          rw [h_prev_d]
          have hev : (m - 1) % 2 = 0 := by omega
          simp [hm_ne0, hev]
        rw [hd_prev_eq] at ha_prev
        have hge : Δ ≤ seqOfDisp d (K + 1 + (m + 1)) := by
          rw [ih1]
          exact le_trans hΔle (altSeq_ge_b0 hle hΔle (m + 1))
        omega

/-- Helper to evaluate `seqOfDisp` from a finite prefix list of displacements `ds`
(`ds[i]` represents `d (i + 3)` for `i < ds.length`, and `0` beyond). -/
def dispOfList (ds : List ℕ) (n : ℕ) : ℕ :=
  if n < 3 then 0 else ds.getD (n - 3) 0

lemma dispOfList_append_left (ds ext : List ℕ) {n : ℕ} (hn : n < ds.length + 3) :
    dispOfList (ds ++ ext) n = dispOfList ds n := by
  unfold dispOfList
  split_ifs with hlt
  · rfl
  · have hi : n - 3 < ds.length := by omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma dispOfList_append_right (ds ext : List ℕ) {j : ℕ} (hj : j < ext.length) :
    dispOfList (ds ++ ext) (ds.length + 3 + j) = ext[j] := by
  unfold dispOfList
  have h1 : ¬ (ds.length + 3 + j < 3) := by omega
  simp only [h1, ↓reduceIte]
  have h2 : ds.length + 3 + j - 3 = ds.length + j := by omega
  rw [h2, List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right _ _)]
  have h3 : ds.length + j - ds.length = j := by omega
  rw [h3, List.getElem?_eq_getElem hj]
  rfl

lemma dispOfList_beyond (ds : List ℕ) {n : ℕ} (hn : ds.length + 3 ≤ n) :
    dispOfList ds n = 0 := by
  unfold dispOfList
  have h1 : ¬ (n < 3) := by omega
  simp only [h1, ↓reduceIte, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none (by omega)]
  rfl

/-- One gap-halving gadget step appended to `ds`, ending with `0` so `d (ds2.length + 2) = 0`. -/
def appendHalveStep (P : ℕ) (W : ℕ) (ds : List ℕ) (L : ℕ) : List ℕ × ℕ :=
  let Δ := W / 2
  let E := P + 2 * L
  let r := (E + Δ) / Δ + 1
  let pad := max (5 * Δ) ((r + 1) * Δ + 1) + E + W + 2
  let ds1 := ds ++ List.replicate pad 0
  let K' := ds1.length + 3
  let gadget := [0, 0] ++ (List.range (2 * r + 3)).map (fun j => if j % 2 = 0 then Δ else 0) ++ [0]
  let ds2 := ds1 ++ gadget
  let Ar := seqOfDisp (dispOfList ds2) (K' + 1 + (2 * r + 2)) - (r + 1) * Δ
  (ds2, Ar + L + Δ)

/-- Recursive halving loop closing density gap `W` down to `1`. -/
def halveLoop (P : ℕ) : (W : ℕ) → List ℕ → ℕ → List ℕ × ℕ
  | W, ds, L =>
    if hW : W ≤ 1 then (ds, L)
    else
      let res := appendHalveStep P W ds L
      have hlt : (W + 1) / 2 < W := by omega
      halveLoop P ((W + 1) / 2) res.1 res.2
termination_by W => W

/-- One complete stage: close tail starting at `M = ds.length + 3`, pad past `2 * maxE'`, insert ratio jump, and finish with `0`. -/
def buildStage (ds : List ℕ) (maxE : ℕ) : List ℕ × ℕ :=
  let M := ds.length + 3
  let P := prefSum (dispOfList ds) M
  let (dsClosed, Lq) := halveLoop P P ds 0
  let maxE' := max maxE (P + 2 * Lq)
  let dsPad := dsClosed ++ List.replicate (2 * maxE' + 4) 0
  let Kj := dsPad.length + 3
  let jumpD := seqOfDisp (dispOfList dsPad) Kj / 5
  (dsPad ++ [jumpD, 0], maxE')

/-- Infinite sequence of stage prefixes `(ds_q, maxE_q)`. -/
def stagePrefix : ℕ → List ℕ × ℕ
  | 0 => ([0, 0], 0)
  | q + 1 => buildStage (stagePrefix q).1 (stagePrefix q).2

/-- Prefix-extension relation: `ds₁` is a prefix of `ds₂`. -/
def IsListPrefix (ds₁ ds₂ : List ℕ) : Prop :=
  ∃ ext : List ℕ, ds₂ = ds₁ ++ ext

lemma isListPrefix_refl (ds : List ℕ) : IsListPrefix ds ds := ⟨[], by simp⟩

lemma isListPrefix_trans {a b c : List ℕ} (h1 : IsListPrefix a b) (h2 : IsListPrefix b c) :
    IsListPrefix a c := by
  rcases h1 with ⟨e1, rfl⟩
  rcases h2 with ⟨e2, rfl⟩
  exact ⟨e1 ++ e2, by simp [List.append_assoc]⟩

lemma appendHalveStep_prefix (P W : ℕ) (ds : List ℕ) (L : ℕ) :
    IsListPrefix ds (appendHalveStep P W ds L).1 := by
  unfold appendHalveStep
  dsimp only
  rw [List.append_assoc]
  exact ⟨_, rfl⟩

lemma halveLoop_prefix (P : ℕ) : ∀ (W : ℕ) (ds : List ℕ) (L : ℕ),
    IsListPrefix ds (halveLoop P W ds L).1 := by
  intro W
  induction W using Nat.strong_induction_on with
  | h W ih =>
    intro ds L
    rw [halveLoop]
    split_ifs with hW
    · exact isListPrefix_refl ds
    · have hlt : (W + 1) / 2 < W := by omega
      exact isListPrefix_trans (appendHalveStep_prefix P W ds L)
        (ih ((W + 1) / 2) hlt _ _)

lemma buildStage_prefix_and_len (ds : List ℕ) (maxE : ℕ) :
    IsListPrefix ds (buildStage ds maxE).1 ∧
    ds.length + 2 ≤ (buildStage ds maxE).1.length := by
  unfold buildStage
  dsimp only
  have hp := halveLoop_prefix (prefSum (dispOfList ds) (ds.length + 3))
    (prefSum (dispOfList ds) (ds.length + 3)) ds 0
  rcases hp with ⟨e, he⟩
  refine ⟨⟨e ++ List.replicate (2 * max maxE (prefSum (dispOfList ds) (ds.length + 3) +
      2 * (halveLoop (prefSum (dispOfList ds) (ds.length + 3))
        (prefSum (dispOfList ds) (ds.length + 3)) ds 0).2) + 4) 0 ++
      [seqOfDisp (dispOfList ((halveLoop (prefSum (dispOfList ds) (ds.length + 3))
        (prefSum (dispOfList ds) (ds.length + 3)) ds 0).1 ++
        List.replicate (2 * max maxE (prefSum (dispOfList ds) (ds.length + 3) +
          2 * (halveLoop (prefSum (dispOfList ds) (ds.length + 3))
            (prefSum (dispOfList ds) (ds.length + 3)) ds 0).2) + 4) 0))
        (((halveLoop (prefSum (dispOfList ds) (ds.length + 3))
          (prefSum (dispOfList ds) (ds.length + 3)) ds 0).1 ++
          List.replicate (2 * max maxE (prefSum (dispOfList ds) (ds.length + 3) +
            2 * (halveLoop (prefSum (dispOfList ds) (ds.length + 3))
              (prefSum (dispOfList ds) (ds.length + 3)) ds 0).2) + 4) 0).length + 3) / 5, 0], ?_⟩, ?_⟩
  · rw [he]
    simp [List.append_assoc]
  · rw [he]
    simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]
    omega

lemma stagePrefix_mono {q₁ q₂ : ℕ} (hq : q₁ ≤ q₂) :
    IsListPrefix (stagePrefix q₁).1 (stagePrefix q₂).1 := by
  induction hq with
  | refl => exact isListPrefix_refl _
  | @step m _ ih =>
    exact isListPrefix_trans ih (buildStage_prefix_and_len _ _).1

lemma stagePrefix_len_ge (q : ℕ) :
    2 * q + 2 ≤ (stagePrefix q).1.length := by
  induction q with
  | zero => simp [stagePrefix]
  | succ q ih =>
    have h := (buildStage_prefix_and_len (stagePrefix q).1 (stagePrefix q).2).2
    change (stagePrefix q).1.length + 2 ≤ (stagePrefix (q + 1)).1.length at h
    omega

lemma stagePrefix_maxE_mono {q₁ q₂ : ℕ} (hq : q₁ ≤ q₂) :
    (stagePrefix q₁).2 ≤ (stagePrefix q₂).2 := by
  induction hq with
  | refl => exact le_refl _
  | @step m _ ih =>
    have hstep : (stagePrefix m).2 ≤ (stagePrefix (m + 1)).2 := by
      change (stagePrefix m).2 ≤ (buildStage (stagePrefix m).1 (stagePrefix m).2).2
      unfold buildStage
      dsimp only
      exact le_max_left _ _
    exact le_trans ih hstep

/-- The master infinite displacement sequence `masterDisp : ℕ → ℕ`. -/
def masterDisp (n : ℕ) : ℕ :=
  dispOfList (stagePrefix (n + 1)).1 n

/-- The master counterexample sequence `masterSeq : ℕ → ℕ`. -/
def masterSeq : ℕ → ℕ :=
  seqOfDisp masterDisp

/-- Consistency: on all indices `< (stagePrefix q).1.length + 3`, `masterDisp` equals `dispOfList (stagePrefix q).1`. -/
lemma masterDisp_eq_stage {q n : ℕ} (hn : n < (stagePrefix q).1.length + 3) :
    masterDisp n = dispOfList (stagePrefix q).1 n := by
  unfold masterDisp
  rcases le_total q (n + 1) with hle | hle
  · obtain ⟨ext, hext⟩ := stagePrefix_mono hle
    rw [hext, dispOfList_append_left _ _ hn]
  · obtain ⟨ext, hext⟩ := stagePrefix_mono hle
    have hlen : n < (stagePrefix (n + 1)).1.length + 3 := by
      have := stagePrefix_len_ge (n + 1)
      omega
    rw [hext, dispOfList_append_left _ _ hlen]

/-! ### 6. Invariant Propagation Through `appendHalveStep`, `halveLoop`, and `buildStage` -/

/-- A finite displacement list `ds` is admissible if `dispOfList ds` is admissible. -/
def ListAdmissible (ds : List ℕ) : Prop :=
  DispAdmissible (dispOfList ds)

lemma listAdmissible_append_zeros {ds : List ℕ} (hadm : ListAdmissible ds) (k : ℕ) :
    ListAdmissible (ds ++ List.replicate k 0) := by
  intro n hn
  by_cases hlt : n < ds.length + 3
  · rw [dispOfList_append_left _ _ hlt]
    have hcongr : seqOfDisp (dispOfList (ds ++ List.replicate k 0)) n =
        seqOfDisp (dispOfList ds) n :=
      seqOfDisp_congr (fun i hi => dispOfList_append_left _ _ (by omega)) n (le_refl n)
    rw [hcongr]
    exact hadm n hn
  · by_cases hlt2 : n < ds.length + k + 3
    · have h0 : dispOfList (ds ++ List.replicate k 0) n = 0 := by
        have heq : n = ds.length + 3 + (n - (ds.length + 3)) := by omega
        rw [heq, dispOfList_append_right _ _ (by simp; omega)]
        simp
      rw [h0]
      omega
    · rw [dispOfList_beyond _ (by simp; omega)]
      omega

/-- After appending `pad` zeros (with `pad ≥ 1`), the last value of `seqOfDisp` is at least `pad`,
and the displacement at index `ds1.length + 2` is `0`. -/
lemma append_zeros_large {ds : List ℕ} (hadm : ListAdmissible ds) {pad : ℕ} (hpad : 1 ≤ pad) :
    let ds1 := ds ++ List.replicate pad 0
    pad ≤ seqOfDisp (dispOfList ds1) (ds1.length + 3) ∧
    dispOfList ds1 (ds1.length + 2) = 0 := by
  intro ds1
  have hadm1 : ListAdmissible ds1 := listAdmissible_append_zeros hadm pad
  have hmono := seqOfDisp_strictMono hadm1
  refine ⟨?_, ?_⟩
  · have hlin : ds1.length + 3 ≤ seqOfDisp (dispOfList ds1) (ds1.length + 3) :=
      hmono.id_le (ds1.length + 3)
    have hlen : pad ≤ ds1.length := by simp [ds1]
    omega
  · have heq : ds1.length + 2 = ds.length + 3 + (pad - 1) := by
      simp [ds1]; omega
    rw [heq]
    have h := dispOfList_append_right ds (List.replicate pad 0) (j := pad - 1) (by simp; omega)
    simpa using h

lemma subsetSums_congr {a b : ℕ → ℕ} {I : Set ℕ} (h : ∀ i ∈ I, a i = b i) :
    subsetSums a I = subsetSums b I := by
  ext t
  constructor <;> rintro ⟨F, hF, rfl⟩
  · exact ⟨F, hF, Finset.sum_congr rfl (fun i hi => (h i (hF hi)).symm)⟩
  · exact ⟨F, hF, Finset.sum_congr rfl (fun i hi => h i (hF hi))⟩

lemma sum_Ico_add_eq_sum_range (f : ℕ → ℕ) (m k : ℕ) :
    ∑ i ∈ Finset.Ico m (m + k), f i = ∑ j ∈ Finset.range k, f (m + j) := by
  rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]

lemma blockSubSums_eq_subsetSums_Ico (a : ℕ → ℕ) (M0 m : ℕ) :
    blockSubSums (fun j => a (M0 + j)) m = subsetSums a (Set.Ico M0 (M0 + m)) := by
  ext t
  constructor
  · rintro ⟨F, hF, rfl⟩
    refine ⟨F.image (fun j => M0 + j), ?_, ?_⟩
    · intro x hx
      rw [Finset.mem_coe, Finset.mem_image] at hx
      rcases hx with ⟨j, hj, rfl⟩
      have hjm : j < m := hF hj
      exact ⟨Nat.le_add_right M0 j, Nat.add_lt_add_left hjm M0⟩
    · rw [Finset.sum_image]
      intro x _ y _ hxy
      dsimp only at hxy
      omega
  · rintro ⟨G, hG, rfl⟩
    refine ⟨G.image (fun x => x - M0), ?_, ?_⟩
    · intro j hj
      rw [Finset.mem_coe, Finset.mem_image] at hj
      rcases hj with ⟨x, hx, rfl⟩
      have hx_mem : x ∈ Set.Ico M0 (M0 + m) := hG hx
      simp only [Set.mem_Ico, Set.mem_Iio] at hx_mem ⊢
      omega
    · rw [Finset.sum_image]
      · refine Finset.sum_congr rfl (fun x hx => ?_)
        have hx_mem : x ∈ Set.Ico M0 (M0 + m) := hG hx
        rw [Nat.add_sub_cancel' hx_mem.1]
      · intro x hx y hy hxy
        have hx_mem : x ∈ Set.Ico M0 (M0 + m) := hG hx
        have hy_mem : y ∈ Set.Ico M0 (M0 + m) := hG hy
        rw [Set.mem_Ico] at hx_mem hy_mem
        dsimp only at hxy
        omega

lemma blockSubSums_congr {a b : ℕ → ℕ} {m : ℕ} (h : ∀ i < m, a i = b i) :
    blockSubSums a m = blockSubSums b m := by
  ext t
  constructor <;> rintro ⟨F, hF, rfl⟩
  · exact ⟨F, hF, Finset.sum_congr rfl (fun i hi => (h i (hF hi)).symm)⟩
  · exact ⟨F, hF, Finset.sum_congr rfl (fun i hi => h i (hF hi))⟩

lemma blockPairs_congr {a b : ℕ → ℕ} {Δ m : ℕ} (h : ∀ i < m, a i = b i) :
    blockPairs a Δ m = blockPairs b Δ m := by
  ext x
  simp [blockPairs, blockSubSums_congr h]

lemma gadget_length (r Δ : ℕ) :
    ([0, 0] ++ (List.range (2 * r + 3)).map (fun j => if j % 2 = 0 then Δ else 0) ++ [0]).length =
      2 * r + 6 := by
  simp

lemma gadget_getElem (r Δ j : ℕ) (hj : j < 2 * r + 3) :
    (([0, 0] ++ (List.range (2 * r + 3)).map (fun j => if j % 2 = 0 then Δ else 0) ++ [0])[2 + j]'(by
      simp; omega)) = if j % 2 = 0 then Δ else 0 := by
  rw [List.getElem_append_left (by simp; omega)]
  rw [List.getElem_append_right (by simp)]
  simp

lemma gadget_getElem_last (r Δ : ℕ) :
    (([0, 0] ++ (List.range (2 * r + 3)).map (fun j => if j % 2 = 0 then Δ else 0) ++ [0])[2 * r + 5]'(by
      simp)) = 0 := by
  have hlen : ([0, 0] ++ (List.range (2 * r + 3)).map
      (fun j => if j % 2 = 0 then Δ else 0)).length ≤ 2 * r + 5 := by
    simp
  rw [List.getElem_append_right hlen]
  simp

private lemma appendHalveStep_arith_bound {P L r Δ b2r1 b2r2 b2r3 b2r4 : ℕ}
    (hE : P + 2 * L + Δ ≤ r * Δ)
    (htel : (r + 1) * Δ ≤ b2r2)
    (hmul : (r + 1) * Δ = r * Δ + Δ)
    (hrec1 : b2r4 = b2r3 + b2r2 + Δ)
    (hrec2 : b2r3 + Δ = b2r2 + b2r1) :
    P + 2 * (b2r2 - (r + 1) * Δ + L + Δ) ≤ b2r4 := by
  omega

/-- Admissibility and closure invariants for a single `appendHalveStep`. -/
lemma appendHalveStep_invariants {P W L : ℕ} {ds : List ℕ}
    (hadm : ListAdmissible ds)
    (hLast0 : dispOfList ds (ds.length + 2) = 0)
    (hM4 : 4 ≤ ds.length + 3)
    (hW : 2 ≤ W)
    {M : ℕ} (hM_le : M ≤ ds.length + 3)
    (hP_eq : P = prefSum (dispOfList ds) M)
    (hDense : IsDense (subsetSums (seqOfDisp (dispOfList ds)) (Set.Ico M (ds.length + 3)))
      W L (∑ i ∈ Finset.Ico M (ds.length + 3), seqOfDisp (dispOfList ds) i - L))
    (hDef : (L = 0 ∧ W = P ∧ 2 ≤ P) ∨ (P + 2 * L ≤ seqOfDisp (dispOfList ds) (ds.length + 2) ∧
      2 * L ≤ ∑ i ∈ Finset.Ico M (ds.length + 3), seqOfDisp (dispOfList ds) i)) :
    let res := appendHalveStep P W ds L
    ListAdmissible res.1 ∧
    dispOfList res.1 (res.1.length + 2) = 0 ∧
    IsDense (subsetSums (seqOfDisp (dispOfList res.1)) (Set.Ico M (res.1.length + 3)))
      ((W + 1) / 2) res.2
      (∑ i ∈ Finset.Ico M (res.1.length + 3), seqOfDisp (dispOfList res.1) i - res.2) ∧
    P + 2 * res.2 ≤ seqOfDisp (dispOfList res.1) (res.1.length + 2) ∧
    2 * res.2 ≤ ∑ i ∈ Finset.Ico M (res.1.length + 3), seqOfDisp (dispOfList res.1) i := by
  intro res
  set Δ := W / 2
  set E := P + 2 * L
  set r := (E + Δ) / Δ + 1
  set pad := max (5 * Δ) ((r + 1) * Δ + 1) + E + W + 2
  set ds1 := ds ++ List.replicate pad 0
  set K' := ds1.length + 3
  set gadget := [0, 0] ++ (List.range (2 * r + 3)).map (fun j => if j % 2 = 0 then Δ else 0) ++ [0]
  set ds2 := ds1 ++ gadget
  have hres1 : res.1 = ds2 := rfl
  have hres2 : res.2 = seqOfDisp (dispOfList ds2) (K' + 1 + (2 * r + 2)) - (r + 1) * Δ + L + Δ := rfl
  have hΔ_pos : 1 ≤ Δ := by omega
  have hΔ_lt_W : Δ < W := by omega
  have hr_ge1 : 1 ≤ r := Nat.succ_le_succ (Nat.zero_le _)
  have hE_lt_rΔ : E + Δ ≤ r * Δ := by
    have hlt := Nat.lt_div_mul_add (a := E + Δ) (b := Δ) (by omega)
    have hrmul : r * Δ = ((E + Δ) / Δ) * Δ + Δ := by dsimp [r]; ring
    omega
  have hpad_ge1 : 1 ≤ pad := by omega
  have hds1_len : ds1.length = ds.length + pad := by simp [ds1]
  have hK'_ge4 : 4 ≤ K' := by dsimp [K']; omega
  have hadm1 : ListAdmissible ds1 := listAdmissible_append_zeros hadm pad
  have hglen : gadget.length = 2 * r + 6 := gadget_length r Δ
  have hds2_len : ds2.length = ds1.length + (2 * r + 6) := by simp [ds2, hglen]
  have hd2_eq_ds1 : ∀ i < K', dispOfList ds2 i = dispOfList ds1 i :=
    fun i hi => dispOfList_append_left ds1 gadget hi
  have hseq2_eq_ds1 : ∀ k ≤ K', seqOfDisp (dispOfList ds2) k = seqOfDisp (dispOfList ds1) k :=
    seqOfDisp_congr hd2_eq_ds1
  have hps2_eq_ds1 : ∀ k ≤ K' + 1, prefSum (dispOfList ds2) k = prefSum (dispOfList ds1) k :=
    prefSum_congr hd2_eq_ds1
  have hd2_K' : dispOfList ds2 K' = 0 := by
    change dispOfList (ds1 ++ gadget) (ds1.length + 3) = 0
    have h := dispOfList_append_right ds1 gadget (j := 0) (by rw [hglen]; omega)
    simpa [gadget] using h
  have hd2_K'1 : dispOfList ds2 (K' + 1) = 0 := by
    change dispOfList (ds1 ++ gadget) (ds1.length + 3 + 1) = 0
    have h := dispOfList_append_right ds1 gadget (j := 1) (by rw [hglen]; omega)
    simpa [gadget] using h
  have hd2_alt : ∀ j < 2 * r + 3,
      dispOfList ds2 (K' + 2 + j) = if j % 2 = 0 then Δ else 0 := by
    intro j hj
    have h := dispOfList_append_right ds1 gadget (j := 2 + j) (by rw [hglen]; omega)
    have hds2 : ds1 ++ gadget = ds2 := rfl
    have hidx : ds1.length + 3 + (2 + j) = K' + 2 + j := by omega
    rw [hds2, hidx] at h
    rw [h]
    exact gadget_getElem r Δ j hj
  have hd2_last0 : dispOfList ds2 (ds2.length + 2) = 0 := by
    have hidx : ds2.length + 2 = ds1.length + 3 + (2 * r + 5) := by omega
    rw [hidx]
    change dispOfList (ds1 ++ gadget) (ds1.length + 3 + (2 * r + 5)) = 0
    rw [dispOfList_append_right ds1 gadget (j := 2 * r + 5) (by rw [hglen]; omega)]
    exact gadget_getElem_last r Δ
  -- Prove `ListAdmissible ds2`
  have hlarge1 : pad ≤ seqOfDisp (dispOfList ds1) K' := (append_zeros_large hadm hpad_ge1).1
  have h_aK'_ge : 5 * Δ ≤ seqOfDisp (dispOfList ds1) K' := by omega
  have hadm2 : ListAdmissible ds2 := by
    intro n hn
    by_cases hlt : n < K'
    · rw [hd2_eq_ds1 n hlt, hseq2_eq_ds1 n (le_of_lt hlt)]
      exact hadm1 n hn
    · by_cases hlt2 : n < K' + (2 * r + 6)
      · have h_dn_le : dispOfList ds2 n ≤ Δ := by
          by_cases h0 : n = K'
          · rw [h0, hd2_K']; omega
          · by_cases h1 : n = K' + 1
            · rw [h1, hd2_K'1]; omega
            · by_cases hlast : n = K' + (2 * r + 5)
              · have heq : n = ds2.length + 2 := by omega
                rw [heq, hd2_last0]; omega
              · have hj : n - (K' + 2) < 2 * r + 3 := by omega
                have heq : n = K' + 2 + (n - (K' + 2)) := by omega
                rw [heq, hd2_alt _ hj]
                split_ifs <;> omega
        have hgeK' : ∀ m, K' ≤ m → m ≤ n →
            seqOfDisp (dispOfList ds1) K' ≤ seqOfDisp (dispOfList ds2) m := by
          intro m hKm hmn
          induction m with
          | zero => omega
          | succ m ihm =>
            by_cases hKm' : K' ≤ m
            · by_cases hmeq : m = K'
              · subst hmeq
                have hd_prev0 : dispOfList ds1 (K' - 1) = 0 := (append_zeros_large hadm hpad_ge1).2
                have h_aK' : seqOfDisp (dispOfList ds1) K' = prefSum (dispOfList ds1) (K' - 1) := by
                  have h1 := seqOfDisp_succ_eq (dispOfList ds1) (n := K' - 1) (by omega)
                  have h2 : K' - 1 + 1 = K' := by omega
                  rw [h2, hd_prev0, add_zero] at h1
                  exact h1
                have hps_le : prefSum (dispOfList ds1) (K' - 1) ≤ prefSum (dispOfList ds2) K' := by
                  rw [hps2_eq_ds1 K' (by omega)]
                  have h2 : K' = (K' - 1) + 1 := by omega
                  conv_rhs => rw [h2, prefSum_succ]
                  omega
                have hle := prefSum_le_seqOfDisp_succ (dispOfList ds2) K'
                omega
              · have _ := ihm hKm' (by omega)
                have hKlt : K' < m := by omega
                have hsingle2 : seqOfDisp (dispOfList ds2) K' ≤ prefSum (dispOfList ds2) m :=
                  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hKlt)
                rw [hseq2_eq_ds1 K' (le_refl K')] at hsingle2
                exact le_trans hsingle2 (prefSum_le_seqOfDisp_succ (dispOfList ds2) m)
            · have hmeq : m + 1 = K' := by omega
              rw [hmeq, hseq2_eq_ds1 K' (le_refl K')]
        have hge := hgeK' n (by omega) (le_refl n)
        omega
      · rw [dispOfList_beyond ds2 (by omega)]
        omega
  -- Propagate `W`-density through the `pad` zero steps up to `K' + 1`
  have hDense_ds1 : ∀ k ≤ pad + 1,
      IsDense (subsetSums (seqOfDisp (dispOfList ds1)) (Set.Ico M (ds.length + 3 + k)))
        W L (∑ i ∈ Finset.Ico M (ds.length + 3 + k), seqOfDisp (dispOfList ds1) i - L) ∧
      2 * L ≤ ∑ i ∈ Finset.Ico M (ds.length + 3 + k), seqOfDisp (dispOfList ds1) i := by
    intro k hk
    induction k with
    | zero =>
      simp only [add_zero]
      have hcongr_s : ∀ i ∈ Finset.Ico M (ds.length + 3),
          seqOfDisp (dispOfList ds1) i = seqOfDisp (dispOfList ds) i := by
        intro i hi
        rw [Finset.mem_Ico] at hi
        exact seqOfDisp_congr (fun j hj => dispOfList_append_left _ _ (by omega)) i (by omega)
      have hsum_eq : ∑ i ∈ Finset.Ico M (ds.length + 3), seqOfDisp (dispOfList ds1) i =
          ∑ i ∈ Finset.Ico M (ds.length + 3), seqOfDisp (dispOfList ds) i :=
        Finset.sum_congr rfl hcongr_s
      have hss_eq : subsetSums (seqOfDisp (dispOfList ds1)) (Set.Ico M (ds.length + 3)) =
          subsetSums (seqOfDisp (dispOfList ds)) (Set.Ico M (ds.length + 3)) := by
        ext t
        constructor <;> rintro ⟨F, hF, rfl⟩
        · refine ⟨F, hF, Finset.sum_congr rfl (fun i hi => (hcongr_s i (Finset.mem_Ico.mpr (hF hi))).symm)⟩
        · refine ⟨F, hF, Finset.sum_congr rfl (fun i hi => hcongr_s i (Finset.mem_Ico.mpr (hF hi)))⟩
      rw [hsum_eq, hss_eq]
      refine ⟨hDense, ?_⟩
      rcases hDef with ⟨rfl, _⟩ | ⟨_, h2L⟩
      · omega
      · exact h2L
    | succ k ih =>
      obtain ⟨hD_prev, h2L_prev⟩ := ih (by omega)
      set idx := ds.length + 3 + k
      have hM_idx : M ≤ idx := by omega
      have hsum_split : prefSum (dispOfList ds1) idx =
          P + ∑ i ∈ Finset.Ico M idx, seqOfDisp (dispOfList ds1) i := by
        have h1 : prefSum (dispOfList ds1) M = P := by
          rw [hP_eq]
          exact prefSum_congr (fun j hj => dispOfList_append_left _ _ (by omega)) M (by omega)
        rw [← h1, prefSum, prefSum, Finset.sum_range_add_sum_Ico _ hM_idx]
      have h_d_prev : dispOfList ds1 (idx - 1) = 0 := by
        by_cases hk0 : k = 0
        · have heq : idx - 1 = ds.length + 2 := by omega
          rw [heq, dispOfList_append_left _ _ (by omega), hLast0]
        · have heq : idx - 1 = ds.length + 3 + (k - 1) := by omega
          rw [heq]
          have h := dispOfList_append_right ds (List.replicate pad 0) (j := k - 1) (by simp; omega)
          simpa using h
      have h_aidx_le : seqOfDisp (dispOfList ds1) idx ≤
          (∑ i ∈ Finset.Ico M idx, seqOfDisp (dispOfList ds1) i - L) - L + W ∧
          (L = 0 ∨ seqOfDisp (dispOfList ds1) idx ≤
            (∑ i ∈ Finset.Ico M idx, seqOfDisp (dispOfList ds1) i - L) - L + 1) := by
        have h_idx_eq : seqOfDisp (dispOfList ds1) idx = prefSum (dispOfList ds1) (idx - 1) := by
          have h1 := seqOfDisp_succ_eq (dispOfList ds1) (n := idx - 1) (by omega)
          have h2 : idx - 1 + 1 = idx := by omega
          rw [h2, h_d_prev, add_zero] at h1
          exact h1
        have h_ps_step : prefSum (dispOfList ds1) idx =
            prefSum (dispOfList ds1) (idx - 1) + seqOfDisp (dispOfList ds1) (idx - 1) := by
          have h1 := prefSum_succ (dispOfList ds1) (idx - 1)
          have h2 : idx - 1 + 1 = idx := by omega
          rw [h2] at h1
          exact h1
        rcases hDef with ⟨rfl, hWP, _⟩ | ⟨hdef_ge, _⟩
        · have hpos := seqOfDisp_pos hadm1 (idx - 1)
          refine ⟨by omega, Or.inl rfl⟩
        · have hmono_prev : seqOfDisp (dispOfList ds) (ds.length + 2) ≤
              seqOfDisp (dispOfList ds1) (idx - 1) := by
            have hcongr_le : seqOfDisp (dispOfList ds) (ds.length + 2) =
                seqOfDisp (dispOfList ds1) (ds.length + 2) :=
              seqOfDisp_congr (fun j hj => (dispOfList_append_left _ _ (by omega)).symm)
                (ds.length + 2) (le_refl _)
            rw [hcongr_le]
            exact (seqOfDisp_strictMono hadm1).monotone (by omega)
          refine ⟨by omega, Or.inr (by omega)⟩
      have hsum_inc : ∑ i ∈ Finset.Ico M (idx + 1), seqOfDisp (dispOfList ds1) i =
          (∑ i ∈ Finset.Ico M idx, seqOfDisp (dispOfList ds1) i) + seqOfDisp (dispOfList ds1) idx :=
        Finset.sum_Ico_succ_top hM_idx (seqOfDisp (dispOfList ds1))
      have hnew_2L : 2 * L ≤ ∑ i ∈ Finset.Ico M (idx + 1), seqOfDisp (dispOfList ds1) i := by
        rw [hsum_inc]; omega
      refine ⟨?_, hnew_2L⟩
      have hidx_succ : ds.length + 3 + (k + 1) = idx + 1 := by omega
      rw [hidx_succ]
      rcases h_aidx_le.2 with rfl | hov
      · simp only [Nat.sub_zero] at hD_prev h_aidx_le ⊢
        exact isDense_step_zero hM_idx hD_prev h_aidx_le.1
      · rw [hsum_inc]
        have hsub_eq : (∑ i ∈ Finset.Ico M idx, seqOfDisp (dispOfList ds1) i) +
            seqOfDisp (dispOfList ds1) idx - L =
            (∑ i ∈ Finset.Ico M idx, seqOfDisp (dispOfList ds1) i - L) +
            seqOfDisp (dispOfList ds1) idx := by omega
        rw [hsub_eq]
        exact isDense_step_overlap hM_idx hD_prev hov (by omega)
  -- Connect `pad + 1` density from `ds1` to `ds2` on `I = Set.Ico M (K' + 1)`
  have hK'1_eq : ds.length + 3 + (pad + 1) = K' + 1 := by omega
  have hI_raw := hDense_ds1 (pad + 1) (le_refl _)
  rw [hK'1_eq] at hI_raw
  have ha2_eq_a1_I : ∀ i < K' + 1,
      seqOfDisp (dispOfList ds2) i = seqOfDisp (dispOfList ds1) i := by
    intro i hi
    have hi_le : i ≤ K' := by omega
    exact hseq2_eq_ds1 i hi_le
  set I : Set ℕ := Set.Ico M (K' + 1)
  set J : Set ℕ := Set.Ico (K' + 1) (ds2.length + 3)
  set SI : ℕ := ∑ i ∈ Finset.Ico M (K' + 1), seqOfDisp (dispOfList ds2) i
  have hSI_eq : SI = ∑ i ∈ Finset.Ico M (K' + 1), seqOfDisp (dispOfList ds1) i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_Ico] at hi
    exact ha2_eq_a1_I i hi.2
  have hI_ss : subsetSums (seqOfDisp (dispOfList ds2)) I =
      subsetSums (seqOfDisp (dispOfList ds1)) I := by
    apply subsetSums_congr
    intro i hi
    exact ha2_eq_a1_I i hi.2
  have hDense_I : IsDense (subsetSums (seqOfDisp (dispOfList ds2)) I) W L (SI - L) := by
    rw [hI_ss, hSI_eq]
    exact hI_raw.1
  have h2L_I : 2 * L ≤ SI := by rw [hSI_eq]; exact hI_raw.2
  -- Setup `altSeq` matching the `(2r + 5)` gadget terms from `K' + 1`
  set b₀ := prefSum (dispOfList ds2) K'
  set b₁ := prefSum (dispOfList ds2) (K' + 1)
  set b := altSeq b₀ b₁ Δ
  have hb0_eq_ps1 : b₀ = prefSum (dispOfList ds1) K' := hps2_eq_ds1 K' (by omega)
  have hb1_split : b₁ = b₀ + seqOfDisp (dispOfList ds2) K' := prefSum_succ (dispOfList ds2) K'
  have haK'_eq : seqOfDisp (dispOfList ds2) K' = seqOfDisp (dispOfList ds1) K' :=
    hseq2_eq_ds1 K' (le_refl K')
  have hb0_ge_aK' : seqOfDisp (dispOfList ds1) K' ≤ b₀ := by
    have hd_prev0 : dispOfList ds1 (K' - 1) = 0 := (append_zeros_large hadm hpad_ge1).2
    have h_aK' : seqOfDisp (dispOfList ds1) K' = prefSum (dispOfList ds1) (K' - 1) := by
      have h1 := seqOfDisp_succ_eq (dispOfList ds1) (n := K' - 1) (by omega)
      have h2 : K' - 1 + 1 = K' := by omega
      rw [h2, hd_prev0, add_zero] at h1
      exact h1
    rw [hb0_eq_ps1, h_aK']
    have h2 : K' = (K' - 1) + 1 := by omega
    conv_rhs => rw [h2, prefSum_succ]
    omega
  have hb0_ge_pad : pad ≤ b₀ := le_trans hlarge1 hb0_ge_aK'
  have hle_b : b₀ ≤ b₁ := by omega
  have hub_b : b₁ ≤ 2 * b₀ := by omega
  have hΔle_b : Δ ≤ b₀ := by omega
  have hpad_r : (r + 1) * Δ + 1 ≤ pad := by dsimp [pad]; omega
  have hmul_r0 : (r + 1) * Δ = r * Δ + Δ := by ring
  have hG_cond : b₀ + Δ ≤ b₁ - r * Δ := by omega
  have hspec : AltBlockSpec b b₀ b₁ Δ := altSeq_spec hle_b hub_b hΔ_pos hΔle_b
  have hagree : ∀ j < 2 * r + 5, seqOfDisp (dispOfList ds2) (K' + 1 + j) = b j :=
    seqOfDisp_eq_altSeq hK'_ge4 hle_b hΔle_b hd2_K' hd2_K'1 hd2_alt
  -- `blockPairs b Δ (2 * r + 5)` lifts via `isDense_lift_pairs`
  have hbp := blockPairs_dense_2r5 hspec hr_ge1 hG_cond
  rcases hbp with ⟨hG_dense, hA_mem, hB_mem, _⟩
  set G := b₁ - r * Δ
  set A := b (2 * r + 2) - (r + 1) * Δ
  set B := blockSum b (2 * r + 5) - Δ - A
  have hJ_len : ds2.length + 3 = K' + 1 + (2 * r + 5) := by omega
  have hbp_congr : blockPairs b Δ (2 * r + 5) =
      blockPairs (fun j => seqOfDisp (dispOfList ds2) (K' + 1 + j)) Δ (2 * r + 5) :=
    blockPairs_congr (fun j hj => (hagree j hj).symm)
  have hP_sub : ∀ p ∈ blockPairs b Δ (2 * r + 5),
      p ∈ subsetSums (seqOfDisp (dispOfList ds2)) J ∧
      p + Δ ∈ subsetSums (seqOfDisp (dispOfList ds2)) J := by
    intro p hp
    rw [hbp_congr] at hp
    simpa [J, hJ_len, blockPairs, blockSubSums_eq_subsetSums_Ico] using hp
  have hb1_eq_P_SI : b₁ = P + SI := by
    have hP2 : prefSum (dispOfList ds2) M = P := by
      rw [hP_eq]
      exact prefSum_congr (N := M) (fun j hj => by
        rw [hd2_eq_ds1 j (by omega), dispOfList_append_left _ _ (by omega)]) M (Nat.le_succ M)
    rw [← hP2]
    dsimp [b₁, SI, prefSum]
    exact (Finset.sum_range_add_sum_Ico (seqOfDisp (dispOfList ds2)) (by omega : M ≤ K' + 1)).symm
  have hK'_in_I : K' ∈ Finset.Ico M (K' + 1) := Finset.mem_Ico.mpr ⟨by omega, Nat.lt_succ_self K'⟩
  have hSI_ge_pad : pad ≤ SI :=
    le_trans (le_trans hlarge1 haK'_eq.symm.le)
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hK'_in_I)
  have hpad_EW : E + W + 2 ≤ pad := by dsimp [pad]; omega
  have hL_le_U : L + Δ ≤ SI - L := by
    have hE_def : E = P + 2 * L := rfl
    omega
  have hb1_ge_rΔ : r * Δ ≤ P + SI := by
    rw [← hb1_eq_P_SI]
    omega
  have hgap : G + Δ ≤ (SI - L) - L := by
    dsimp [G]
    rw [hb1_eq_P_SI]
    have hE_def : E = P + 2 * L := rfl
    omega
  have hdisj : Disjoint I J := by
    rw [Set.disjoint_left]
    intro i hiI hiJ
    simp only [I, J, Set.mem_Ico] at hiI hiJ
    omega
  have hlifted := isDense_lift_pairs hdisj hDense_I hΔ_lt_W hP_sub hG_dense hB_mem hL_le_U hgap
  have hunion : I ∪ J = Set.Ico M (ds2.length + 3) := by
    ext i
    simp only [I, J, Set.mem_union, Set.mem_Ico]
    omega
  have hmax_W : max Δ (W - Δ) = (W + 1) / 2 := max_div_two_eq W hW
  have hA_eq : A = seqOfDisp (dispOfList ds2) (K' + 1 + (2 * r + 2)) - (r + 1) * Δ := by
    dsimp [A]
    rw [hagree (2 * r + 2) (by omega)]
  have hL_new : A + L + Δ = res.2 := by rw [hA_eq, hres2]
  have hSJ_eq : blockSum b (2 * r + 5) =
      ∑ i ∈ Finset.Ico (K' + 1) (ds2.length + 3), seqOfDisp (dispOfList ds2) i := by
    dsimp [blockSum]
    have hsum_agree : ∑ j ∈ Finset.range (2 * r + 5), b j =
        ∑ j ∈ Finset.range (2 * r + 5), seqOfDisp (dispOfList ds2) (K' + 1 + j) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      exact (hagree j hj).symm
    rw [hsum_agree, hJ_len, sum_Ico_add_eq_sum_range]
  have hStotal_eq : ∑ i ∈ Finset.Ico M (ds2.length + 3), seqOfDisp (dispOfList ds2) i =
      SI + blockSum b (2 * r + 5) := by
    rw [hSJ_eq]
    dsimp [SI]
    exact (Finset.sum_Ico_consecutive (seqOfDisp (dispOfList ds2))
      (by omega : M ≤ K' + 1) (by omega : K' + 1 ≤ ds2.length + 3)).symm
  have hA_plus_Δ_le : A + Δ ≤ blockSum b (2 * r + 5) := (blockPairs_symm hA_mem).1
  have hU_new : B + (SI - L) =
      ∑ i ∈ Finset.Ico M (ds2.length + 3), seqOfDisp (dispOfList ds2) i - res.2 := by
    rw [hStotal_eq, ← hL_new]
    dsimp [B]
    omega
  rw [hunion, hmax_W, hL_new, hU_new, ← hres1] at hlifted
  -- Bound `P + 2 * res.2 ≤ seqOfDisp (dispOfList ds2) (ds2.length + 2)` and `2 * res.2 ≤ S_total`
  have htel_le : (r + 1) * Δ ≤ b (2 * r + 2) := (alt_telescope_even hspec r (r + 1) (le_refl _)).1
  have hb2r4_rec : b (2 * r + 4) = b (2 * r + 3) + b (2 * r + 2) + Δ := by
    have := hspec.heven (r + 2) (by omega)
    have h1 : 2 * (r + 2) = 2 * r + 4 := by omega
    have h2 : 2 * (r + 2) - 1 = 2 * r + 3 := by omega
    have h3 : 2 * (r + 2) - 2 = 2 * r + 2 := by omega
    rw [h3, h2, h1] at this
    exact this
  have hb2r3_rec : b (2 * r + 3) + Δ = b (2 * r + 2) + b (2 * r + 1) := by
    have := hspec.hodd (r + 1) (by omega)
    have h1 : 2 * (r + 1) + 1 = 2 * r + 3 := by omega
    have h2 : 2 * (r + 1) = 2 * r + 2 := by omega
    have h3 : 2 * (r + 1) - 1 = 2 * r + 1 := by omega
    rw [h1, h3, h2] at this
    exact this
  have hlast_idx : ds2.length + 2 = K' + 1 + (2 * r + 4) := by omega
  have h_alast_eq : seqOfDisp (dispOfList ds2) (ds2.length + 2) = b (2 * r + 4) := by
    rw [hlast_idx]
    exact hagree (2 * r + 4) (by omega)
  have h_inv4 : P + 2 * res.2 ≤ seqOfDisp (dispOfList ds2) (ds2.length + 2) := by
    rw [hres2, ← hA_eq, h_alast_eq]
    exact appendHalveStep_arith_bound hE_lt_rΔ htel_le (by ring) hb2r4_rec hb2r3_rec
  have h_inv5 : 2 * res.2 ≤ ∑ i ∈ Finset.Ico M (ds2.length + 3), seqOfDisp (dispOfList ds2) i := by
    have hmem : ds2.length + 2 ∈ Finset.Ico M (ds2.length + 3) :=
      Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    have hsingle := Finset.single_le_sum (f := seqOfDisp (dispOfList ds2))
      (fun _ _ => Nat.zero_le _) hmem
    exact le_trans (Nat.le_add_left _ P) (le_trans h_inv4 hsingle)
  rw [← hres1] at hadm2 hd2_last0 h_inv4 h_inv5
  exact ⟨hadm2, hd2_last0, hlifted, h_inv4, h_inv5⟩

/-- Closure invariants through the full `halveLoop P W ds L` recursion (`W ≥ 1`). -/
lemma halveLoop_invariants (P : ℕ) :
    ∀ (W : ℕ) (ds : List ℕ) (L M : ℕ),
      ListAdmissible ds →
      dispOfList ds (ds.length + 2) = 0 →
      4 ≤ ds.length + 3 →
      1 ≤ W →
      M ≤ ds.length + 3 →
      P = prefSum (dispOfList ds) M →
      IsDense (subsetSums (seqOfDisp (dispOfList ds)) (Set.Ico M (ds.length + 3)))
        W L (∑ i ∈ Finset.Ico M (ds.length + 3), seqOfDisp (dispOfList ds) i - L) →
      ((L = 0 ∧ W = P ∧ 2 ≤ P) ∨ (P + 2 * L ≤ seqOfDisp (dispOfList ds) (ds.length + 2) ∧
        2 * L ≤ ∑ i ∈ Finset.Ico M (ds.length + 3), seqOfDisp (dispOfList ds) i)) →
      let res := halveLoop P W ds L
      IsListPrefix ds res.1 ∧
      ListAdmissible res.1 ∧
      dispOfList res.1 (res.1.length + 2) = 0 ∧
      IsDense (subsetSums (seqOfDisp (dispOfList res.1)) (Set.Ico M (res.1.length + 3)))
        1 res.2
        (∑ i ∈ Finset.Ico M (res.1.length + 3), seqOfDisp (dispOfList res.1) i - res.2) ∧
      P + 2 * res.2 ≤ seqOfDisp (dispOfList res.1) (res.1.length + 2) ∧
      2 * res.2 ≤ ∑ i ∈ Finset.Ico M (res.1.length + 3), seqOfDisp (dispOfList res.1) i := by
  intro W
  induction W using Nat.strong_induction_on with
  | h W ih =>
    intro ds L M hadm hLast0 hM4 hW hM_le hP_eq hDense hDef
    rw [halveLoop]
    split_ifs with hW1
    · have hWeq : W = 1 := by omega
      subst hWeq
      have hDef' : P + 2 * L ≤ seqOfDisp (dispOfList ds) (ds.length + 2) ∧
          2 * L ≤ ∑ i ∈ Finset.Ico M (ds.length + 3), seqOfDisp (dispOfList ds) i := by
        rcases hDef with ⟨_, _, _⟩ | hgood
        · omega
        · exact hgood
      exact ⟨isListPrefix_refl ds, hadm, hLast0, hDense, hDef'.1, hDef'.2⟩
    · have hW2 : 2 ≤ W := by omega
      have hlt : (W + 1) / 2 < W := by omega
      have hW_next : 1 ≤ (W + 1) / 2 := by omega
      have hstep := appendHalveStep_invariants hadm hLast0 hM4 hW2 hM_le hP_eq hDense hDef
      rcases hstep with ⟨hadm', hLast0', hDense', hDef1', hDef2'⟩
      have hpref := appendHalveStep_prefix P W ds L
      rcases hpref with ⟨ext, hext⟩
      have hlen_le : ds.length ≤ (appendHalveStep P W ds L).1.length := by
        rw [hext, List.length_append]
        omega
      have hP_next : P = prefSum (dispOfList (appendHalveStep P W ds L).1) M :=
        Eq.trans hP_eq (prefSum_congr (fun i hi => by
          rw [hext, dispOfList_append_left _ _ (by omega)]) M (by omega)).symm
      have hrec := ih ((W + 1) / 2) hlt (appendHalveStep P W ds L).1 (appendHalveStep P W ds L).2
        M hadm' hLast0' (by omega) hW_next (by omega) hP_next hDense' (Or.inr ⟨hDef1', hDef2'⟩)
      rcases hrec with ⟨hp2, hrec_rest⟩
      exact ⟨isListPrefix_trans ⟨ext, hext⟩ hp2, hrec_rest⟩

/-- Stage invariants through `buildStage ds maxE`. -/
lemma buildStage_invariants (ds : List ℕ) (maxE : ℕ)
    (hadm : ListAdmissible ds)
    (hLen2 : 2 ≤ ds.length)
    (hLast0 : dispOfList ds (ds.length + 2) = 0) :
    let res := buildStage ds maxE
    ListAdmissible res.1 ∧
    2 ≤ res.1.length ∧
    dispOfList res.1 (res.1.length + 2) = 0 ∧
    (∃ dsClosed Lq,
      IsListPrefix ds dsClosed ∧
      IsListPrefix dsClosed res.1 ∧
      ds.length ≤ dsClosed.length ∧
      dispOfList dsClosed (dsClosed.length + 2) = 0 ∧
      IsDense (subsetSums (seqOfDisp (dispOfList dsClosed)) (Set.Ico (ds.length + 3) (dsClosed.length + 3)))
        1 Lq (∑ i ∈ Finset.Ico (ds.length + 3) (dsClosed.length + 3), seqOfDisp (dispOfList dsClosed) i - Lq) ∧
      prefSum (dispOfList ds) (ds.length + 3) + 2 * Lq ≤
        seqOfDisp (dispOfList dsClosed) (dsClosed.length + 2) ∧
      2 * Lq ≤ ∑ i ∈ Finset.Ico (ds.length + 3) (dsClosed.length + 3), seqOfDisp (dispOfList dsClosed) i) ∧
    (∃ Kj,
      ds.length + 3 ≤ Kj ∧
      Kj + 1 < res.1.length + 3 ∧
      4 ≤ Kj ∧
      dispOfList res.1 (Kj - 1) = 0 ∧
      dispOfList res.1 Kj = seqOfDisp (dispOfList res.1) Kj / 5 ∧
      20 ≤ seqOfDisp (dispOfList res.1) Kj) := by
  intro res
  set M := ds.length + 3
  set P := prefSum (dispOfList ds) M
  set dsClosed := (halveLoop P P ds 0).1
  set Lq := (halveLoop P P ds 0).2
  set maxE' := max maxE (P + 2 * Lq)
  set pad := 2 * maxE' + 4
  set dsPad := dsClosed ++ List.replicate pad 0
  set Kj := dsPad.length + 3
  set jumpD := seqOfDisp (dispOfList dsPad) Kj / 5
  have hres1 : res.1 = dsPad ++ [jumpD, 0] := rfl
  have hP17 : 17 ≤ P := by
    have h4_le_M : 4 ≤ M := by omega
    have hsum_sub : ∑ i ∈ Finset.range 4, seqOfDisp (dispOfList ds) i ≤
        ∑ i ∈ Finset.range M, seqOfDisp (dispOfList ds) i :=
      Finset.sum_le_sum_of_subset (Finset.range_mono h4_le_M)
    have h4 : ∑ i ∈ Finset.range 4, seqOfDisp (dispOfList ds) i = 17 := by
      simp [Finset.sum_range_succ, seqOfDisp, seqPair]
    dsimp [P, prefSum]
    omega
  have hDense0 : IsDense (subsetSums (seqOfDisp (dispOfList ds)) (Set.Ico M (ds.length + 3)))
      P 0 (∑ i ∈ Finset.Ico M (ds.length + 3), seqOfDisp (dispOfList ds) i - 0) := by
    intro t ht1 ht2
    have heq : Set.Ico M (ds.length + 3) = ∅ := Set.Ico_eq_empty (by omega)
    have hfi : Finset.Ico M (ds.length + 3) = ∅ := Finset.Ico_eq_empty (by omega)
    rw [hfi, Finset.sum_empty, Nat.sub_zero] at ht2
    have ht0 : t = 0 := by omega
    subst ht0
    exact ⟨0, ⟨∅, by simp, by simp⟩, le_refl 0, by omega⟩
  have hloop := halveLoop_invariants P P ds 0 M hadm hLast0 (by omega) (by omega) (le_refl M) rfl
    hDense0 (Or.inl ⟨rfl, rfl, by omega⟩)
  rcases hloop with ⟨hpref_c, hadm_c, hLast0_c, hDense_c, hInv1_c, hInv2_c⟩
  have hlen_c : ds.length ≤ dsClosed.length := by
    rcases hpref_c with ⟨e, he⟩
    dsimp only [dsClosed] at he ⊢
    rw [he, List.length_append]
    omega
  have hadmPad : ListAdmissible dsPad := listAdmissible_append_zeros hadm_c pad
  have hpad1 : 1 ≤ pad := by omega
  have hzeros := append_zeros_large hadm_c hpad1
  have hdPad_prev0 : dispOfList dsPad (Kj - 1) = 0 := hzeros.2
  have hdsNext_len : res.1.length = dsPad.length + 2 := by
    rw [hres1]; simp
  have hcongr_next : ∀ i < Kj, dispOfList res.1 i = dispOfList dsPad i := by
    intro i hi
    rw [hres1]
    exact dispOfList_append_left dsPad [jumpD, 0] hi
  have hseq_next_Kj : ∀ k ≤ Kj, seqOfDisp (dispOfList res.1) k = seqOfDisp (dispOfList dsPad) k :=
    seqOfDisp_congr hcongr_next
  have hdNext_prev0 : dispOfList res.1 (Kj - 1) = 0 := by
    rw [hcongr_next (Kj - 1) (by omega), hdPad_prev0]
  have hdNext_Kj : dispOfList res.1 Kj = jumpD := by
    rw [hres1]
    have h := dispOfList_append_right dsPad [jumpD, 0] (j := 0) (by simp)
    simpa [Kj] using h
  have hdNext_Kj1 : dispOfList res.1 (Kj + 1) = 0 := by
    rw [hres1]
    have h := dispOfList_append_right dsPad [jumpD, 0] (j := 1) (by simp)
    simpa [Kj] using h
  have hdNext_last0 : dispOfList res.1 (res.1.length + 2) = 0 := by
    have heq : res.1.length + 2 = Kj + 1 := by omega
    rw [heq, hdNext_Kj1]
  have hadm_next : ListAdmissible res.1 := by
    intro n hn
    by_cases hlt : n < Kj
    · rw [hcongr_next n hlt, hseq_next_Kj n (le_of_lt hlt)]
      exact hadmPad n hn
    · by_cases hKj : n = Kj
      · subst hKj
        rw [hdNext_Kj, hseq_next_Kj Kj (le_refl Kj)]
        exact Nat.mul_div_le _ 5
      · by_cases hKj1 : n = Kj + 1
        · subst hKj1
          rw [hdNext_Kj1]
          omega
        · rw [dispOfList_beyond res.1 (by omega)]
          omega
  have haKj_big : 20 ≤ seqOfDisp (dispOfList res.1) Kj := by
    rw [hseq_next_Kj Kj (le_refl Kj)]
    have hpad_len : 20 ≤ Kj := by
      dsimp [Kj, dsPad, pad, maxE']
      simp
      omega
    exact le_trans hpad_len ((seqOfDisp_strictMono hadmPad).id_le Kj)
  have hdNext_Kj_eq : dispOfList res.1 Kj = seqOfDisp (dispOfList res.1) Kj / 5 := by
    rw [hdNext_Kj, hseq_next_Kj Kj (le_refl Kj)]
  have hClosed_pref : IsListPrefix dsClosed res.1 := by
    refine ⟨List.replicate pad 0 ++ [jumpD, 0], ?_⟩
    rw [hres1, List.append_assoc]
  exact ⟨hadm_next, by omega, hdNext_last0,
    ⟨dsClosed, Lq, hpref_c, hClosed_pref, hlen_c, hLast0_c, hDense_c, hInv1_c, hInv2_c⟩,
    ⟨Kj, by dsimp [Kj, dsPad]; simp; omega, by omega, by dsimp [Kj, dsPad]; simp; omega,
      hdNext_prev0, hdNext_Kj_eq, haKj_big⟩⟩

/-- Every `stagePrefix q` satisfies `ListAdmissible`, `2 ≤ ds.length`, and zero final displacement. -/
lemma stagePrefix_invariants (q : ℕ) :
    ListAdmissible (stagePrefix q).1 ∧
    2 ≤ (stagePrefix q).1.length ∧
    dispOfList (stagePrefix q).1 ((stagePrefix q).1.length + 2) = 0 := by
  induction q with
  | zero =>
    have hzero : ∀ n : ℕ, dispOfList [0, 0] n = 0 := by
      intro n
      match n with
      | 0 | 1 | 2 | 3 | 4 => simp [dispOfList]
      | k + 5 => rw [dispOfList_beyond [0, 0] (by simp)]
    refine ⟨?_, by simp [stagePrefix], ?_⟩
    · intro n _
      dsimp [stagePrefix]
      rw [hzero n]
      omega
    · dsimp [stagePrefix]
      exact hzero _
  | succ q ih =>
    have h := buildStage_invariants (stagePrefix q).1 (stagePrefix q).2 ih.1 ih.2.1 ih.2.2
    exact ⟨h.1, h.2.1, h.2.2.1⟩

/-- The master infinite sequence `masterDisp` is admissible at every `n ≥ 3`. -/
theorem masterDisp_admissible : DispAdmissible masterDisp := by
  intro n hn
  have hinv := stagePrefix_invariants (n + 1)
  have hlen : n < (stagePrefix (n + 1)).1.length + 3 := by
    have := stagePrefix_len_ge (n + 1)
    omega
  have hcongr : seqOfDisp masterDisp n = seqOfDisp (dispOfList (stagePrefix (n + 1)).1) n :=
    seqOfDisp_congr (fun i hi => masterDisp_eq_stage (by omega)) n (le_refl n)
  rw [masterDisp_eq_stage hlen, hcongr]
  exact hinv.1 n hn

/-- Unbounded inductive extension of a `1`-dense tail past index `N₀` once `P + 2 * L ≤ a (N₀ - 1)`. -/
lemma dense_one_extend_of_prefix_bound {d : ℕ → ℕ} (hadm : DispAdmissible d)
    {M N₀ L : ℕ} (hN4 : 4 ≤ N₀) (hMN : M ≤ N₀)
    (hprev0 : d (N₀ - 1) = 0)
    (hDense : IsDense (subsetSums (seqOfDisp d) (Set.Ico M N₀)) 1 L
      (∑ i ∈ Finset.Ico M N₀, seqOfDisp d i - L))
    (hInv1 : prefSum d M + 2 * L ≤ seqOfDisp d (N₀ - 1))
    (hInv2 : 2 * L ≤ ∑ i ∈ Finset.Ico M N₀, seqOfDisp d i) :
    ∀ k : ℕ, N₀ ≤ k →
      IsDense (subsetSums (seqOfDisp d) (Set.Ico M k)) 1 L
        (∑ i ∈ Finset.Ico M k, seqOfDisp d i - L) ∧
      2 * L ≤ ∑ i ∈ Finset.Ico M k, seqOfDisp d i := by
  intro k hk
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction t with
  | zero => simpa using ⟨hDense, hInv2⟩
  | succ t ih =>
    obtain ⟨hD_prev, h2L_prev⟩ := ih (by omega)
    set idx := N₀ + t
    have hM_idx : M ≤ idx := by omega
    have hsum_split : prefSum d idx =
        prefSum d M + ∑ i ∈ Finset.Ico M idx, seqOfDisp d i := by
      rw [prefSum, prefSum, Finset.sum_range_add_sum_Ico _ hM_idx]
    have h_idx_eq : seqOfDisp d idx = prefSum d (idx - 1) + d (idx - 1) := by
      have h1 := seqOfDisp_succ_eq d (n := idx - 1) (by omega)
      have h2 : idx - 1 + 1 = idx := by omega
      rw [h2] at h1
      exact h1
    have h_ps_step : prefSum d idx = prefSum d (idx - 1) + seqOfDisp d (idx - 1) := by
      have h1 := prefSum_succ d (idx - 1)
      have h2 : idx - 1 + 1 = idx := by omega
      rw [h2] at h1
      exact h1
    have h_key : prefSum d M + 2 * L + d (idx - 1) ≤ seqOfDisp d (idx - 1) := by
      by_cases ht0 : t = 0
      · subst ht0
        dsimp [idx]
        rw [hprev0, add_zero]
        exact hInv1
      · have hrat := (seqOfDisp_ratio_bounds hadm (N₀ - 1)).1
        have hN_eq : N₀ - 1 + 1 = N₀ := by omega
        rw [hN_eq] at hrat
        have hmono := (seqOfDisp_strictMono hadm).monotone (by omega : N₀ ≤ idx - 1)
        have hadm_prev := hadm (idx - 1) (by omega)
        omega
    have hov : seqOfDisp d idx ≤
        (∑ i ∈ Finset.Ico M idx, seqOfDisp d i - L) - L + 1 := by
      omega
    have hLU : L ≤ ∑ i ∈ Finset.Ico M idx, seqOfDisp d i - L := by omega
    have hsum_inc : ∑ i ∈ Finset.Ico M (idx + 1), seqOfDisp d i =
        (∑ i ∈ Finset.Ico M idx, seqOfDisp d i) + seqOfDisp d idx :=
      Finset.sum_Ico_succ_top hM_idx (seqOfDisp d)
    have h2L_next : 2 * L ≤ ∑ i ∈ Finset.Ico M (idx + 1), seqOfDisp d i := by
      rw [hsum_inc]; omega
    have hsub_eq : ∑ i ∈ Finset.Ico M (idx + 1), seqOfDisp d i - L =
        (∑ i ∈ Finset.Ico M idx, seqOfDisp d i - L) + seqOfDisp d idx := by
      rw [hsum_inc]; omega
    have hidx_succ : N₀ + (t + 1) = idx + 1 := by omega
    rw [hidx_succ]
    refine ⟨?_, h2L_next⟩
    rw [hsub_eq]
    exact isDense_step_overlap hM_idx hD_prev hov hLU

theorem masterSeq_strictMono : StrictMono masterSeq :=
  seqOfDisp_strictMono masterDisp_admissible

theorem masterSeq_hasUniformRatioGap : HasUniformRatioGap masterSeq :=
  seqOfDisp_hasUniformRatioGap masterDisp_admissible

theorem masterSeq_finiteDeletionComplete : FiniteDeletionComplete masterSeq := by
  apply finiteDeletionComplete_of_tails
  intro N
  have hinv_q := stagePrefix_invariants N
  have hst := buildStage_invariants (stagePrefix N).1 (stagePrefix N).2
    hinv_q.1 hinv_q.2.1 hinv_q.2.2
  rcases hst.2.2.2.1 with
    ⟨dsClosed, Lq, hpref_c, hpref_next, hlen_c, hLast0_c, hDense_c, hInv1_c, hInv2_c⟩
  let M := (stagePrefix N).1.length + 3
  let N₀ := dsClosed.length + 3
  have hM_ge_N : N ≤ M := by
    have := stagePrefix_len_ge N
    omega
  have hMN : M ≤ N₀ := by
    dsimp [M, N₀]
    omega
  have hN4 : 4 ≤ N₀ := by
    have := hinv_q.2.1
    dsimp [N₀]
    omega
  have h_len_closed_lt_next : dsClosed.length + 3 ≤ (stagePrefix (N + 1)).1.length + 3 := by
    rcases hpref_next with ⟨ext, hext⟩
    change dsClosed.length + 3 ≤ (buildStage (stagePrefix N).1 (stagePrefix N).2).1.length + 3
    rw [hext, List.length_append]
    omega
  have hd_eq : ∀ i < N₀, masterDisp i = dispOfList dsClosed i := by
    intro i hi
    have hi_next : i < (stagePrefix (N + 1)).1.length + 3 := by omega
    rw [masterDisp_eq_stage hi_next]
    rcases hpref_next with ⟨ext, hext⟩
    change dispOfList (buildStage (stagePrefix N).1 (stagePrefix N).2).1 i = dispOfList dsClosed i
    rw [hext, dispOfList_append_left _ _ hi]
  have hseq_eq : ∀ k ≤ N₀, masterSeq k = seqOfDisp (dispOfList dsClosed) k :=
    fun k hk => seqOfDisp_congr hd_eq k hk
  have hprev0 : masterDisp (N₀ - 1) = 0 := by
    rw [hd_eq (N₀ - 1) (by omega)]
    have heq : N₀ - 1 = dsClosed.length + 2 := by omega
    rw [heq]
    exact hLast0_c
  have hcongr_Ico : ∀ i ∈ Finset.Ico M N₀,
      masterSeq i = seqOfDisp (dispOfList dsClosed) i := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    exact hseq_eq i (by omega)
  have hsum_eq : ∑ i ∈ Finset.Ico M N₀, masterSeq i =
      ∑ i ∈ Finset.Ico M N₀, seqOfDisp (dispOfList dsClosed) i :=
    Finset.sum_congr rfl hcongr_Ico
  have hss_eq : subsetSums masterSeq (Set.Ico M N₀) =
      subsetSums (seqOfDisp (dispOfList dsClosed)) (Set.Ico M N₀) := by
    apply subsetSums_congr
    intro i hi
    exact hseq_eq i hi.2.le
  have hDense_master : IsDense (subsetSums masterSeq (Set.Ico M N₀)) 1 Lq
      (∑ i ∈ Finset.Ico M N₀, masterSeq i - Lq) := by
    rw [hss_eq, hsum_eq]
    exact hDense_c
  have hP_eq : prefSum masterDisp M = prefSum (dispOfList (stagePrefix N).1) M :=
    prefSum_congr (fun i hi => masterDisp_eq_stage (q := N) hi) M (Nat.le_succ M)
  have hInv1_master : prefSum masterDisp M + 2 * Lq ≤ masterSeq (N₀ - 1) := by
    rw [hP_eq, hseq_eq (N₀ - 1) (by omega)]
    have heq : N₀ - 1 = dsClosed.length + 2 := by omega
    rw [heq]
    exact hInv1_c
  have hInv2_master : 2 * Lq ≤ ∑ i ∈ Finset.Ico M N₀, masterSeq i := by
    rw [hsum_eq]
    exact hInv2_c
  have hext := dense_one_extend_of_prefix_bound masterDisp_admissible hN4 hMN hprev0
    hDense_master hInv1_master hInv2_master
  refine ⟨M, hM_ge_N, Lq, ?_⟩
  intro n hn
  set k := max N₀ (M + n + Lq + 1)
  have hk_ge : N₀ ≤ k := le_max_left _ _
  have hk_big : M + n + Lq + 1 ≤ k := le_max_right _ _
  have hDk := (hext k hk_ge).1
  have hsum_ge : k - M ≤ ∑ i ∈ Finset.Ico M k, masterSeq i := by
    calc
      k - M = ∑ _i ∈ Finset.Ico M k, 1 := by simp
      _ ≤ ∑ i ∈ Finset.Ico M k, masterSeq i := by
        apply Finset.sum_le_sum
        intro i _
        have h2 := seqOfDisp_ge_two masterDisp_admissible i
        change 2 ≤ masterSeq i at h2
        omega
  have hn_le_U : n ≤ ∑ i ∈ Finset.Ico M k, masterSeq i - Lq := by omega
  have hmem_Ico : n ∈ subsetSums masterSeq (Set.Ico M k) :=
    isDense_one_iff.mp hDk n hn hn_le_U
  exact subsetSums_mono Set.Ico_subset_Ici_self hmem_Ico

theorem masterSeq_valueFiniteDeletionComplete : ValueFiniteDeletionComplete masterSeq :=
  valueFiniteDeletionComplete_of_index masterSeq_strictMono masterSeq_finiteDeletionComplete

theorem masterSeq_infiniteDeletionIncomplete : InfiniteDeletionIncomplete masterSeq :=
  seqOfDisp_infiniteDeletionIncomplete masterDisp_admissible

theorem masterSeq_valueInfiniteDeletionIncomplete : ValueInfiniteDeletionIncomplete masterSeq :=
  valueInfiniteDeletionIncomplete_of_index masterSeq_strictMono masterSeq_infiniteDeletionIncomplete

theorem masterSeq_not_tendsto_goldenRatio :
    ¬ Tendsto (quotient masterSeq) atTop (𝓝 Real.goldenRatio) := by
  intro htend
  have hmem : Set.Iio ((165 : ℝ) / 100) ∈ 𝓝 Real.goldenRatio :=
    Iio_mem_nhds goldenRatio_lt_165
  have hev := htend.eventually hmem
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  have hinv_q := stagePrefix_invariants N
  have hst := buildStage_invariants (stagePrefix N).1 (stagePrefix N).2
    hinv_q.1 hinv_q.2.1 hinv_q.2.2
  rcases hst.2.2.2.2 with ⟨Kj, hKj_ge, hKj_lt, hKj4, hdprev0, hdKj, hbig⟩
  have hKj_ge_N : N ≤ Kj := by
    have := stagePrefix_len_ge N
    omega
  have hlt165 : quotient masterSeq Kj < (165 : ℝ) / 100 := hN Kj hKj_ge_N
  have hcongr_next : ∀ i < Kj + 2, masterDisp i = dispOfList (stagePrefix (N + 1)).1 i := by
    intro i hi
    apply masterDisp_eq_stage
    change i < (buildStage (stagePrefix N).1 (stagePrefix N).2).1.length + 3
    omega
  have h_aKj : masterSeq Kj = seqOfDisp (dispOfList (stagePrefix (N + 1)).1) Kj :=
    seqOfDisp_congr (fun i hi => hcongr_next i (by omega)) Kj (le_refl Kj)
  have h_aKj1 : masterSeq (Kj + 1) = seqOfDisp (dispOfList (stagePrefix (N + 1)).1) (Kj + 1) :=
    seqOfDisp_congr (fun i hi => hcongr_next i (by omega)) (Kj + 1) (le_refl (Kj + 1))
  have hm_prev0 : masterDisp (Kj - 1) = 0 := by
    rw [hcongr_next (Kj - 1) (by omega)]
    exact hdprev0
  have hm_Kj : masterDisp Kj = masterSeq Kj / 5 := by
    rw [hcongr_next Kj (by omega), h_aKj]
    exact hdKj
  have hm_big : 20 ≤ masterSeq Kj := by
    rw [h_aKj]
    exact hbig
  have hge165 := jump_ratio_gt_goldenRatio masterDisp_admissible hKj4 hm_prev0 hm_Kj hm_big
  change (165 : ℝ) / 100 ≤ quotient masterSeq Kj at hge165
  linarith

/-- **Full Unconditional Solution to JSP-000288 / Erdős Problem #346:**
The answer is **No**: there exists a strictly increasing sequence `a : ℕ → ℕ` (with uniform ratio gap
`1 + ε ≤ a (n + 1) / a n`) that is stably complete upon removing any finite set of indices OR values,
incomplete upon removing any infinite set of indices OR values, AND whose consecutive term ratios
`a (n + 1) / a n` fail to converge to the golden ratio `Real.goldenRatio` (in fact they cannot converge
to `φ`, as infinitely many indices satisfy `a (K + 1) / a K ≥ 165 / 100 > φ`). -/
theorem jsp_000288_disproof :
    ∃ a : ℕ → ℕ,
      StrictMono a ∧
      HasUniformRatioGap a ∧
      FiniteDeletionComplete a ∧
      ValueFiniteDeletionComplete a ∧
      InfiniteDeletionIncomplete a ∧
      ValueInfiniteDeletionIncomplete a ∧
      ¬ Tendsto (quotient a) atTop (𝓝 Real.goldenRatio) :=
  ⟨masterSeq,
    masterSeq_strictMono,
    masterSeq_hasUniformRatioGap,
    masterSeq_finiteDeletionComplete,
    masterSeq_valueFiniteDeletionComplete,
    masterSeq_infiniteDeletionIncomplete,
    masterSeq_valueInfiniteDeletionIncomplete,
    masterSeq_not_tendsto_goldenRatio⟩

end JSP_000288

#check JSP_000288.masterSeq_strictMono
#check JSP_000288.masterSeq_hasUniformRatioGap
#check JSP_000288.masterSeq_finiteDeletionComplete
#check JSP_000288.masterSeq_valueFiniteDeletionComplete
#check JSP_000288.masterSeq_infiniteDeletionIncomplete
#check JSP_000288.masterSeq_valueInfiniteDeletionIncomplete
#check JSP_000288.masterSeq_not_tendsto_goldenRatio
#check JSP_000288.jsp_000288_disproof

#print axioms JSP_000288.masterSeq_strictMono
#print axioms JSP_000288.masterSeq_hasUniformRatioGap
#print axioms JSP_000288.masterSeq_finiteDeletionComplete
#print axioms JSP_000288.masterSeq_valueFiniteDeletionComplete
#print axioms JSP_000288.masterSeq_infiniteDeletionIncomplete
#print axioms JSP_000288.masterSeq_valueInfiniteDeletionIncomplete
#print axioms JSP_000288.masterSeq_not_tendsto_goldenRatio
#print axioms JSP_000288.jsp_000288_disproof
