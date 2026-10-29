/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.VariableSizeLineageCount
public import Rhone.Coalescent.Sfs
public import Rhone.Statistics.SfsLevelBlockLaw

/-!
# Expected site frequency spectrum of the coalescent with a population-size function

Source: polanski_kimmel2003, p. 428, eq. (1). -/

@[expose] public section

namespace Rhone.Statistics

open MeasureTheory ProbabilityTheory Finset MarkovChain Coalescent Rhone.Combinatorics Probability
open Filter
open scoped ENNReal NNReal Topology

noncomputable def variableSizeBranchMutationRate (n : ℕ) (θ : ℝ≥0)
    (q : KingmanMutationHistory n) (b : KingmanMutationBranch n) : ℝ≥0 :=
  ⟨if b.2 ∈ (q.1 b.1.val).parts ∧ 1 < (q.1 b.1.val).parts.card then
      max 0 ((θ : ℝ) / 2 * (q.2 (b.1.val + 1) - q.2 b.1.val))
    else 0, by split_ifs <;> positivity⟩

theorem measurable_variableSizeBranchMutationRate (n : ℕ) (θ : ℝ≥0)
    (b : KingmanMutationBranch n) :
    Measurable (fun q : KingmanMutationHistory n => variableSizeBranchMutationRate n θ q b) := by
  apply Measurable.subtype_mk
  apply Measurable.ite
  · have hm : Measurable (fun q : KingmanMutationHistory n => q.1 b.1.val) :=
      (measurable_pi_apply b.1.val).comp measurable_fst
    exact hm (MeasurableSet.of_discrete (s :=
      {π : Finpartition (Finset.univ : Finset (Fin n)) |
        b.2 ∈ π.parts ∧ 1 < π.parts.card}))
  · fun_prop
  · fun_prop

noncomputable def variableSizeBranchMutationKernel (n : ℕ) (θ : ℝ≥0) :
    Kernel (KingmanMutationHistory n) (KingmanMutationBranch n → ℕ) where
  toFun q := Measure.pi (fun b : KingmanMutationBranch n =>
    poissonMeasure (variableSizeBranchMutationRate n θ q b))
  measurable' := by
    classical
    apply Measure.measurable_of_measurable_coe
    intro s hs
    have he : (fun q : KingmanMutationHistory n =>
        Measure.pi (fun b : KingmanMutationBranch n =>
          poissonMeasure (variableSizeBranchMutationRate n θ q b)) s) =
        fun q => ∑' x : KingmanMutationBranch n → ℕ,
          s.indicator (fun x =>
            Measure.pi (fun b : KingmanMutationBranch n =>
              poissonMeasure (variableSizeBranchMutationRate n θ q b)) {x}) x := by
      funext q
      exact (Measure.tsum_indicator_apply_singleton _ s hs).symm
    rw [he]
    apply Measurable.tsum
    intro x
    by_cases hx : x ∈ s
    · simp only [Set.indicator_of_mem hx, Measure.pi_singleton, poissonMeasure_singleton]
      apply Finset.measurable_prod
      intro b _
      have hb := measurable_variableSizeBranchMutationRate n θ b
      fun_prop
    · simp only [Set.indicator_of_notMem hx]
      exact measurable_const

instance variableSizeBranchMutationKernel_markov (n : ℕ) (θ : ℝ≥0) :
    IsMarkovKernel (variableSizeBranchMutationKernel n θ) where
  isProbabilityMeasure q := by
    change IsProbabilityMeasure (Measure.pi (fun b : KingmanMutationBranch n =>
      poissonMeasure (variableSizeBranchMutationRate n θ q b)))
    infer_instance

noncomputable def variableSizeMarkedLaw (n : ℕ) (ν : ℝ → ℝ) (θ : ℝ≥0) :
    Measure (KingmanMutationHistory n × (KingmanMutationBranch n → ℕ)) :=
  (variableSizeLaw n ν).compProd (variableSizeBranchMutationKernel n θ)

theorem zero_le_sfsBlockCount (n i : ℕ) (π : Finpartition (Finset.univ : Finset (Fin n))) :
    0 ≤ sfsBlockCount n i π := by
  unfold sfsBlockCount
  refine Finset.sum_nonneg fun B _ => ?_
  split_ifs <;> norm_num

theorem sum_variableSizeBranchMutationRate_sfs (n i : ℕ) (θ : ℝ≥0)
    (q : KingmanMutationHistory n) :
    ∑ b : KingmanMutationBranch n,
        (if b.2.card = i then (1 : ℝ) else 0) * (variableSizeBranchMutationRate n θ q b : ℝ) =
      ∑ m : Fin (n - 1),
        (if 1 < (q.1 m).parts.card then sfsBlockCount n i (q.1 m) else 0) *
          max 0 ((θ : ℝ) / 2 * (q.2 ((m : ℕ) + 1) - q.2 m)) := by
  classical
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun m _ => ?_
  change (∑ B : Finset (Fin n), (if B.card = i then (1 : ℝ) else 0) *
    (if B ∈ (q.1 m.val).parts ∧ 1 < (q.1 m.val).parts.card then
      max 0 ((θ : ℝ) / 2 * (q.2 (m.val + 1) - q.2 m.val)) else 0)) = _
  by_cases ht : 1 < (q.1 m.val).parts.card
  · simp only [ht, and_true, ↓reduceIte]
    have he (B : Finset (Fin n)) :
        (if B.card = i then (1 : ℝ) else 0) * (if B ∈ (q.1 m.val).parts then
          max 0 ((θ : ℝ) / 2 * (q.2 (m.val + 1) - q.2 m.val)) else 0) =
        if B ∈ (q.1 m.val).parts then (if B.card = i then (1 : ℝ) else 0) *
          max 0 ((θ : ℝ) / 2 * (q.2 (m.val + 1) - q.2 m.val)) else 0 := by
      split_ifs <;> simp
    simp_rw [he]
    rw [Finset.sum_ite_mem_eq, ← Finset.sum_mul]
    rfl
  · simp [ht]

theorem ofReal_max_zero_mul {c : ℝ} (hc : 0 ≤ c) (W : ℝ) :
    ENNReal.ofReal (max 0 (c * W)) = ENNReal.ofReal c * ENNReal.ofReal W := by
  rcases le_total 0 W with hW | hW
  · rw [max_eq_right (mul_nonneg hc hW), ENNReal.ofReal_mul hc]
  · rw [max_eq_left (mul_nonpos_of_nonneg_of_nonpos hc hW), ENNReal.ofReal_zero,
      ENNReal.ofReal_of_nonpos hW, mul_zero]

theorem lintegral_variableSizeBranchMutationKernel_sfs (n i : ℕ) (θ : ℝ≥0)
    (q : KingmanMutationHistory n) :
    ∫⁻ y, ENNReal.ofReal (markedKingmanSfs n i (q, y))
        ∂variableSizeBranchMutationKernel n θ q =
      ∑ m : Fin (n - 1),
        ENNReal.ofReal (if 1 < (q.1 m).parts.card then sfsBlockCount n i (q.1 m) else 0) *
          (ENNReal.ofReal ((θ : ℝ) / 2) * ENNReal.ofReal (q.2 ((m : ℕ) + 1) - q.2 m)) := by
  have hint : Integrable (fun y => markedKingmanSfs n i (q, y))
      (variableSizeBranchMutationKernel n θ q) := by
    simp_rw [markedKingmanSfs_eq_weighted]
    exact pi_poisson_integrable_weighted_count (variableSizeBranchMutationRate n θ q)
      (fun b => if b.2.card = i then (1 : ℝ) else 0)
  have hval : ∫ y, markedKingmanSfs n i (q, y) ∂variableSizeBranchMutationKernel n θ q =
      ∑ b : KingmanMutationBranch n,
        (if b.2.card = i then (1 : ℝ) else 0) * (variableSizeBranchMutationRate n θ q b : ℝ) := by
    simp_rw [markedKingmanSfs_eq_weighted]
    exact pi_poisson_integral_weighted_count (variableSizeBranchMutationRate n θ q)
      (fun b => if b.2.card = i then (1 : ℝ) else 0)
  have hg : ∀ m : Fin (n - 1),
      0 ≤ (if 1 < (q.1 m).parts.card then sfsBlockCount n i (q.1 m) else 0) := by
    intro m
    split_ifs
    · exact zero_le_sfsBlockCount n i _
    · exact le_rfl
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun y => markedKingmanSfs_nonneg n i _), hval,
    sum_variableSizeBranchMutationRate_sfs, ENNReal.ofReal_sum_of_nonneg]
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [ENNReal.ofReal_mul (hg m), ofReal_max_zero_mul (by positivity)]
  · intro m _
    exact mul_nonneg (hg m) (le_max_left _ _)

theorem lintegral_sfsBlockCount_level (n : ℕ) {m i : ℕ} (hm : m + 1 < n) (hi : 1 ≤ i)
    (hin : i < n) :
    ∫⁻ ω, ENNReal.ofReal (if 1 < (ω m).parts.card then sfsBlockCount n i (ω m) else 0)
        ∂(partitionChain (Fin n)).jumpChain.pathLaw ⊥ =
      ENNReal.ofReal (((n - m : ℕ) : ℝ) * ((subtendProb n (n - m) i : ℚ) : ℝ)) := by
  have h := integral_sfsBlockCount_level (n := n) (k := n - m) (i := i) (by omega) (by omega)
    hi hin
  rw [show n - (n - m) = m from by omega] at h
  have hmeas : Measurable fun ω : ℕ → Finpartition (Finset.univ : Finset (Fin n)) =>
      sfsBlockCount n i (ω m) :=
    (Measurable.of_discrete (f := sfsBlockCount n i)).comp (measurable_pi_apply m)
  obtain ⟨C, hC⟩ := (Set.finite_range fun π : Finpartition (Finset.univ : Finset (Fin n)) =>
    ‖sfsBlockCount n i π‖).bddAbove
  have hint : Integrable (fun ω : ℕ → Finpartition (Finset.univ : Finset (Fin n)) =>
      sfsBlockCount n i (ω m)) ((partitionChain (Fin n)).jumpChain.pathLaw ⊥) :=
    (integrable_const C).mono' hmeas.aestronglyMeasurable
      (Eventually.of_forall fun ω => hC (Set.mem_range_self (ω m)))
  rw [← h, ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun ω => zero_le_sfsBlockCount n i _)]
  refine lintegral_congr_ae ?_
  filter_upwards [partition_path_countdown_general n] with ω hω
  have hcard : 1 < (ω m).parts.card := by
    rw [hω m]
    omega
  simp only [hcard, ↓reduceIte]

theorem subtendProb_nonneg (n k i : ℕ) : 0 ≤ subtendProb n k i :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem lintegral_variableSizeMarkedLaw_sfs {ν : ℝ → ℝ} (hν : IsSizeFunction ν) {n i : ℕ}
    (hi : 1 ≤ i) (hin : i < n) (θ : ℝ≥0) :
    ∫⁻ x, ENNReal.ofReal (markedKingmanSfs n i x) ∂variableSizeMarkedLaw n ν θ =
      ENNReal.ofReal ((θ : ℝ) / 2) * ∑ k ∈ Icc 2 n,
        ENNReal.ofReal ((k : ℝ) * ((subtendProb n k i : ℚ) : ℝ)) *
          ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (lineageLaw n (cumIntensity ν t) k) := by
  have := isProbabilityMeasure_variableSizeLaw n hν
  rw [variableSizeMarkedLaw,
    Measure.lintegral_compProd (measurable_markedKingmanSfs n i).ennreal_ofReal]
  simp_rw [lintegral_variableSizeBranchMutationKernel_sfs]
  have hmeas : ∀ m : Fin (n - 1), Measurable fun q : KingmanMutationHistory n =>
      ENNReal.ofReal (if 1 < (q.1 m).parts.card then sfsBlockCount n i (q.1 m) else 0) *
        (ENNReal.ofReal ((θ : ℝ) / 2) * ENNReal.ofReal (q.2 ((m : ℕ) + 1) - q.2 m)) := by
    intro m
    have h1 : Measurable fun q : KingmanMutationHistory n =>
        ENNReal.ofReal (if 1 < (q.1 m).parts.card then sfsBlockCount n i (q.1 m) else 0) :=
      (Measurable.of_discrete (f := fun π : Finpartition (Finset.univ : Finset (Fin n)) =>
        ENNReal.ofReal (if 1 < π.parts.card then sfsBlockCount n i π else 0))).comp
          ((measurable_pi_apply (m : ℕ)).comp measurable_fst)
    have h2 : Measurable fun q : KingmanMutationHistory n =>
        ENNReal.ofReal ((θ : ℝ) / 2) * ENNReal.ofReal (q.2 ((m : ℕ) + 1) - q.2 m) := by
      fun_prop
    exact h1.mul h2
  rw [lintegral_finsetSum _ fun m _ => hmeas m, Finset.mul_sum,
    ← sum_range_sub_eq_sum_Icc n fun k => ENNReal.ofReal ((θ : ℝ) / 2) *
      (ENNReal.ofReal ((k : ℝ) * ((subtendProb n k i : ℚ) : ℝ)) *
        ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (lineageLaw n (cumIntensity ν t) k)),
    ← Fin.sum_univ_eq_sum_range (fun m => ENNReal.ofReal ((θ : ℝ) / 2) *
      (ENNReal.ofReal (((n - m : ℕ) : ℝ) * ((subtendProb n (n - m) i : ℚ) : ℝ)) *
        ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (lineageLaw n (cumIntensity ν t) (n - m)))) (n - 1)]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hm : (m : ℕ) + 1 < n := by
    have := m.2
    omega
  rw [lintegral_congr fun q => mul_left_comm _ _ _,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_variableSizeLaw_mul_levelTime n hν hm (fun π =>
      ENNReal.ofReal (if 1 < π.parts.card then sfsBlockCount n i π else 0)),
    lintegral_sfsBlockCount_level n hm hi hin, lintegral_variableSizeLaw_levelTime n hν hm]

theorem variableSizeMarkedLaw_sfs_mean_of_levelTime {ν : ℝ → ℝ} (hν : IsSizeFunction ν)
    {n i : ℕ} (hi : 1 ≤ i) (hin : i < n) (θ : ℝ≥0) (τ : ℕ → ℝ)
    (hτ : ∀ k ∈ Icc 2 n, 0 ≤ τ k)
    (h : ∀ k ∈ Icc 2 n, ∫⁻ t in Set.Ioi 0,
      ENNReal.ofReal (lineageLaw n (cumIntensity ν t) k) = ENNReal.ofReal (τ k)) :
    ∫ x, markedKingmanSfs n i x ∂variableSizeMarkedLaw n ν θ =
      (θ : ℝ) / 2 * ∑ k ∈ Icc 2 n, (k : ℝ) * ((subtendProb n k i : ℚ) : ℝ) * τ k := by
  have hsp : ∀ k : ℕ, (0 : ℝ) ≤ (k : ℝ) * ((subtendProb n k i : ℚ) : ℝ) := fun k =>
    mul_nonneg (Nat.cast_nonneg _) (by exact_mod_cast subtendProb_nonneg n k i)
  have hsum : ∑ k ∈ Icc 2 n, ENNReal.ofReal ((k : ℝ) * ((subtendProb n k i : ℚ) : ℝ)) *
        ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (lineageLaw n (cumIntensity ν t) k) =
      ENNReal.ofReal (∑ k ∈ Icc 2 n, (k : ℝ) * ((subtendProb n k i : ℚ) : ℝ) * τ k) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun k hk => mul_nonneg (hsp k) (hτ k hk)]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [h k hk, ENNReal.ofReal_mul (hsp k)]
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun x => markedKingmanSfs_nonneg n i x)
    (measurable_markedKingmanSfs n i).aestronglyMeasurable,
    lintegral_variableSizeMarkedLaw_sfs hν hi hin θ, hsum,
    ← ENNReal.ofReal_mul (by positivity), ENNReal.toReal_ofReal]
  exact mul_nonneg (by positivity)
    (Finset.sum_nonneg fun k hk => mul_nonneg (hsp k) (hτ k hk))

theorem sum_Icc_subtendProb_holdingTime {n i : ℕ} (hi : 1 ≤ i) (hin : i < n) :
    ∑ k ∈ Icc 2 n, (k : ℝ) * ((subtendProb n k i : ℚ) : ℝ) * ((holdingTime k : ℚ) : ℝ) =
      ((expSfsCoeff n i : ℚ) : ℝ) := by
  have hq : ∑ k ∈ Icc 2 n, (k : ℚ) * subtendProb n k i * holdingTime k = expSfsCoeff n i := by
    unfold expSfsCoeff
    symm
    rw [← Finset.sum_subset (Finset.Icc_subset_Icc le_rfl (by omega : n - i + 1 ≤ n))]
    · exact Finset.sum_congr rfl fun k _ => by ring
    · intro k hk hk'
      have h1 := mem_Icc.1 hk
      have h2 : n - i + 1 < k := by
        by_contra hcon
        exact hk' (mem_Icc.2 ⟨h1.1, by omega⟩)
      have h3 : (n - i - 1).choose (k - 2) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [subtendProb, h3]
  rw [← hq]
  push_cast
  rfl

theorem variableSizeMarkedLaw_one_sfs_mean {n i : ℕ} (hi : 1 ≤ i) (hin : i < n) (θ : ℝ≥0) :
    ∫ x, markedKingmanSfs n i x ∂variableSizeMarkedLaw n (fun _ => 1) θ = (θ : ℝ) / i := by
  have hht : ∀ k ∈ Icc 2 n, (0 : ℝ) ≤ ((holdingTime k : ℚ) : ℝ) := by
    intro k _
    have : (0 : ℚ) ≤ holdingTime k := div_nonneg zero_le_one (coalRate_nonneg k)
    exact_mod_cast this
  rw [variableSizeMarkedLaw_sfs_mean_of_levelTime isSizeFunction_one hi hin θ
    (fun k => ((holdingTime k : ℚ) : ℝ)) hht, sum_Icc_subtendProb_holdingTime hi hin,
    expSfsCoeff_eq hi hin]
  · have hi0 : (i : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  · intro k hk
    have hk' := mem_Icc.1 hk
    simp only [cumIntensity_one]
    exact lintegral_lineageLaw n hk'.1 hk'.2

structure IsEpochSchedule (K : ℕ) (c a : ℕ → ℝ) : Prop where
  start : c 0 = 0
  lt_succ : ∀ e, e < K → c e < c (e + 1)
  size_pos : ∀ e, e ≤ K → 0 < a e

noncomputable def piecewiseSize (K : ℕ) (c a : ℕ → ℝ) (t : ℝ) : ℝ :=
  a ((range K).filter fun e => c (e + 1) < t).card

noncomputable def epochIntensity (c a : ℕ → ℝ) (e : ℕ) : ℝ :=
  ∑ e' ∈ range e, (c (e' + 1) - c e') / a e'

noncomputable def piecewiseLevelTime (n K : ℕ) (c a : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Icc k n, lineageCoeff n k j / (coalRate j : ℝ) *
    (∑ e ∈ range K, a e * (Real.exp (-((coalRate j : ℝ) * epochIntensity c a e)) -
        Real.exp (-((coalRate j : ℝ) * epochIntensity c a (e + 1)))) +
      a K * Real.exp (-((coalRate j : ℝ) * epochIntensity c a K)))

noncomputable def piecewiseExpSfs (θ : ℝ) (n K : ℕ) (c a : ℕ → ℝ) (i : ℕ) : ℝ :=
  θ / 2 * ∑ k ∈ Icc 2 n, (k : ℝ) * ((subtendProb n k i : ℚ) : ℝ) * piecewiseLevelTime n K c a k

variable {K : ℕ} {c a : ℕ → ℝ}

theorem IsEpochSchedule.mono (h : IsEpochSchedule K c a) {i j : ℕ} (hij : i ≤ j)
    (hj : j ≤ K) : c i ≤ c j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih => exact (ih (by omega)).trans (h.lt_succ j (by omega)).le

theorem IsEpochSchedule.nonneg (h : IsEpochSchedule K c a) {e : ℕ} (he : e ≤ K) :
    0 ≤ c e := by
  have := h.mono (Nat.zero_le e) he
  rwa [h.start] at this

theorem card_filter_changePoint_le (K : ℕ) (c : ℕ → ℝ) (t : ℝ) :
    ((range K).filter fun e => c (e + 1) < t).card ≤ K :=
  (Finset.card_filter_le _ _).trans (Finset.card_range K).le

theorem piecewiseSize_pos (h : IsEpochSchedule K c a) (t : ℝ) : 0 < piecewiseSize K c a t :=
  h.size_pos _ (card_filter_changePoint_le K c t)

theorem piecewiseSize_of_mem_Ioc (h : IsEpochSchedule K c a) {e : ℕ} (he : e < K) {t : ℝ}
    (ht : t ∈ Set.Ioc (c e) (c (e + 1))) : piecewiseSize K c a t = a e := by
  have hf : ((range K).filter fun e' => c (e' + 1) < t) = range e := by
    ext e'
    simp only [mem_filter, mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      by_contra hcon
      have h3 := h.mono (show e + 1 ≤ e' + 1 by omega) (by omega)
      linarith [ht.2]
    · intro h1
      exact ⟨by omega, lt_of_le_of_lt (h.mono (show e' + 1 ≤ e by omega) (by omega)) ht.1⟩
  rw [piecewiseSize, hf, card_range]

theorem piecewiseSize_of_lt (h : IsEpochSchedule K c a) {t : ℝ} (ht : c K < t) :
    piecewiseSize K c a t = a K := by
  have hf : ((range K).filter fun e' => c (e' + 1) < t) = range K := by
    refine Finset.filter_true_of_mem fun e' he' => ?_
    have := mem_range.1 he'
    exact lt_of_le_of_lt (h.mono (show e' + 1 ≤ K by omega) le_rfl) ht
  rw [piecewiseSize, hf, card_range]

theorem measurable_piecewiseSize (K : ℕ) (c a : ℕ → ℝ) : Measurable (piecewiseSize K c a) := by
  have hmono : Monotone fun t : ℝ => ((range K).filter fun e => c (e + 1) < t).card := by
    intro s t hst
    refine Finset.card_le_card (Finset.monotone_filter_right _ fun e _ he => ?_)
    exact lt_of_lt_of_le he hst
  exact (Measurable.of_discrete (f := a)).comp hmono.measurable

theorem intervalIntegrable_inv_piecewiseSize (h : IsEpochSchedule K c a) (s t : ℝ) :
    IntervalIntegrable (fun u => (piecewiseSize K c a u)⁻¹) volume s t := by
  have hmeas : Measurable fun u => (piecewiseSize K c a u)⁻¹ :=
    (measurable_piecewiseSize K c a).inv
  refine (intervalIntegrable_const (c := ∑ j ∈ range (K + 1), (a j)⁻¹)).mono_fun'
    hmeas.aestronglyMeasurable (Eventually.of_forall fun u => ?_)
  change ‖(piecewiseSize K c a u)⁻¹‖ ≤ ∑ j ∈ range (K + 1), (a j)⁻¹
  rw [Real.norm_of_nonneg (inv_nonneg.2 (piecewiseSize_pos h u).le)]
  refine Finset.single_le_sum (f := fun j => (a j)⁻¹) (fun j hj => ?_)
    (mem_range.2 (Nat.lt_succ_of_le (card_filter_changePoint_le K c u)))
  have := mem_range.1 hj
  exact inv_nonneg.2 (h.size_pos j (by omega)).le

theorem integral_inv_piecewiseSize_epoch (h : IsEpochSchedule K c a) {e : ℕ} (he : e < K)
    {s t : ℝ} (hs : c e ≤ s) (hst : s ≤ t) (ht : t ≤ c (e + 1)) :
    ∫ u in s..t, (piecewiseSize K c a u)⁻¹ = (t - s) / a e := by
  have hcongr : ∫ u in s..t, (piecewiseSize K c a u)⁻¹ = ∫ _ in s..t, (a e)⁻¹ := by
    rw [intervalIntegral.integral_of_le hst, intervalIntegral.integral_of_le hst]
    refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
    rw [piecewiseSize_of_mem_Ioc h he ⟨lt_of_le_of_lt hs hu.1, hu.2.trans ht⟩]
  rw [hcongr, intervalIntegral.integral_const, smul_eq_mul, div_eq_mul_inv]

theorem integral_inv_piecewiseSize_tail (h : IsEpochSchedule K c a) {s t : ℝ} (hs : c K ≤ s)
    (hst : s ≤ t) : ∫ u in s..t, (piecewiseSize K c a u)⁻¹ = (t - s) / a K := by
  have hcongr : ∫ u in s..t, (piecewiseSize K c a u)⁻¹ = ∫ _ in s..t, (a K)⁻¹ := by
    rw [intervalIntegral.integral_of_le hst, intervalIntegral.integral_of_le hst]
    refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
    rw [piecewiseSize_of_lt h (lt_of_le_of_lt hs hu.1)]
  rw [hcongr, intervalIntegral.integral_const, smul_eq_mul, div_eq_mul_inv]

theorem epochIntensity_succ (c a : ℕ → ℝ) (e : ℕ) :
    epochIntensity c a (e + 1) = epochIntensity c a e + (c (e + 1) - c e) / a e :=
  Finset.sum_range_succ _ _

theorem cumIntensity_piecewiseSize_changePoint (h : IsEpochSchedule K c a) {e : ℕ}
    (he : e ≤ K) : cumIntensity (piecewiseSize K c a) (c e) = epochIntensity c a e := by
  induction e with
  | zero => rw [h.start, cumIntensity_zero, epochIntensity, Finset.sum_range_zero]
  | succ e ih =>
    have h1 := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_inv_piecewiseSize h 0 (c e))
      (intervalIntegrable_inv_piecewiseSize h (c e) (c (e + 1)))
    have h2 := ih (by omega)
    rw [cumIntensity] at h2 ⊢
    rw [← h1, h2, integral_inv_piecewiseSize_epoch h (by omega) le_rfl
      (h.lt_succ e (by omega)).le le_rfl, epochIntensity_succ]

theorem cumIntensity_piecewiseSize_of_mem_Icc (h : IsEpochSchedule K c a) {e : ℕ} (he : e < K)
    {t : ℝ} (ht : t ∈ Set.Icc (c e) (c (e + 1))) :
    cumIntensity (piecewiseSize K c a) t = epochIntensity c a e + (t - c e) / a e := by
  have h1 := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_inv_piecewiseSize h 0 (c e))
    (intervalIntegrable_inv_piecewiseSize h (c e) t)
  have h2 := cumIntensity_piecewiseSize_changePoint h he.le
  rw [cumIntensity] at h2 ⊢
  rw [← h1, h2, integral_inv_piecewiseSize_epoch h he le_rfl ht.1 ht.2]

theorem cumIntensity_piecewiseSize_of_le (h : IsEpochSchedule K c a) {t : ℝ} (ht : c K ≤ t) :
    cumIntensity (piecewiseSize K c a) t = epochIntensity c a K + (t - c K) / a K := by
  have h1 := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_inv_piecewiseSize h 0 (c K))
    (intervalIntegrable_inv_piecewiseSize h (c K) t)
  have h2 := cumIntensity_piecewiseSize_changePoint h (le_refl K)
  rw [cumIntensity] at h2 ⊢
  rw [← h1, h2, integral_inv_piecewiseSize_tail h le_rfl ht]

theorem isSizeFunction_piecewiseSize (h : IsEpochSchedule K c a) :
    IsSizeFunction (piecewiseSize K c a) where
  pos := fun t _ => piecewiseSize_pos h t
  intervalIntegrable := fun t _ => intervalIntegrable_inv_piecewiseSize h 0 t
  tendsto_atTop := by
    have h0 : Tendsto (fun t : ℝ => t - c K) atTop atTop := by
      simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-c K) tendsto_id
    have h1 : Tendsto (fun t : ℝ => epochIntensity c a K + (t - c K) / a K) atTop atTop :=
      tendsto_atTop_add_const_left _ _ (h0.atTop_div_const (h.size_pos K le_rfl))
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop (c K)] with t ht
    exact (cumIntensity_piecewiseSize_of_le h ht).symm

theorem hasDerivAt_epoch_primitive {r a' : ℝ} (hr : r ≠ 0) (ha : a' ≠ 0) (x b t : ℝ) :
    HasDerivAt (fun t => -(a' / r) * Real.exp (-(r * (x + (t - b) / a'))))
      (Real.exp (-(r * (x + (t - b) / a')))) t := by
  have h1 : HasDerivAt (fun t => -(r * (x + (t - b) / a'))) (-(r * (1 / a'))) t :=
    (((((hasDerivAt_id t).sub_const b).div_const a').const_add x).const_mul r).neg
  have h2 := h1.exp.const_mul (-(a' / r))
  convert h2 using 1
  field_simp

theorem intervalIntegrable_exp_neg_cumIntensity {ν : ℝ → ℝ} (hν : IsSizeFunction ν) (r : ℝ)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    IntervalIntegrable (fun u => Real.exp (-(r * cumIntensity ν u))) volume s t := by
  have hcont : ContinuousOn (fun u => Real.exp (-(r * cumIntensity ν u))) (Set.Ici 0) :=
    Real.continuous_exp.comp_continuousOn ((continuousOn_const.mul hν.continuousOn).neg)
  refine (hcont.mono fun u hu => ?_).intervalIntegrable
  rcases Set.mem_uIcc.1 hu with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact hs.trans h1
  · exact ht.trans h1

theorem integral_exp_neg_cumIntensity_epoch (h : IsEpochSchedule K c a) {e : ℕ} (he : e < K)
    {r : ℝ} (hr : r ≠ 0) :
    ∫ t in (c e)..(c (e + 1)), Real.exp (-(r * cumIntensity (piecewiseSize K c a) t)) =
      a e / r * (Real.exp (-(r * epochIntensity c a e)) -
        Real.exp (-(r * epochIntensity c a (e + 1)))) := by
  have hle := (h.lt_succ e he).le
  have hae : a e ≠ 0 := (h.size_pos e he.le).ne'
  have hcongr : ∫ t in (c e)..(c (e + 1)),
        Real.exp (-(r * cumIntensity (piecewiseSize K c a) t)) =
      ∫ t in (c e)..(c (e + 1)),
        Real.exp (-(r * (epochIntensity c a e + (t - c e) / a e))) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hle] at ht
    rw [cumIntensity_piecewiseSize_of_mem_Icc h he ht]
  rw [hcongr, intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_epoch_primitive hr hae (epochIntensity c a e) (c e) t)
    (Continuous.intervalIntegrable (by fun_prop) _ _), epochIntensity_succ]
  simp only [sub_self, zero_div, add_zero]
  ring

theorem integral_exp_neg_cumIntensity_prefix (h : IsEpochSchedule K c a) {e : ℕ} (he : e ≤ K)
    {r : ℝ} (hr : r ≠ 0) :
    ∫ t in (0 : ℝ)..(c e), Real.exp (-(r * cumIntensity (piecewiseSize K c a) t)) =
      ∑ e' ∈ range e, a e' / r * (Real.exp (-(r * epochIntensity c a e')) -
        Real.exp (-(r * epochIntensity c a (e' + 1)))) := by
  have hν := isSizeFunction_piecewiseSize h
  induction e with
  | zero => rw [h.start, intervalIntegral.integral_same, Finset.sum_range_zero]
  | succ e ih =>
    have h1 := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_exp_neg_cumIntensity hν r le_rfl (h.nonneg (by omega : e ≤ K)))
      (intervalIntegrable_exp_neg_cumIntensity hν r (h.nonneg (by omega : e ≤ K))
        (h.nonneg he))
    rw [← h1, ih (by omega), integral_exp_neg_cumIntensity_epoch h (by omega) hr,
      Finset.sum_range_succ]

theorem integral_exp_neg_cumIntensity_tail (h : IsEpochSchedule K c a) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t => Real.exp (-(r * cumIntensity (piecewiseSize K c a) t)))
        (Set.Ioi (c K)) ∧
      ∫ t in Set.Ioi (c K), Real.exp (-(r * cumIntensity (piecewiseSize K c a) t)) =
        a K / r * Real.exp (-(r * epochIntensity c a K)) := by
  have haK := h.size_pos K le_rfl
  let G : ℝ → ℝ := fun t => Real.exp (-(r * (epochIntensity c a K + (t - c K) / a K)))
  let F : ℝ → ℝ := fun t => -(a K / r) * G t
  have hderiv : ∀ t ∈ Set.Ici (c K), HasDerivAt F (G t) t := fun t _ =>
    hasDerivAt_epoch_primitive hr.ne' haK.ne' (epochIntensity c a K) (c K) t
  have hG0 : Tendsto G atTop (𝓝 0) := by
    have h0 : Tendsto (fun t : ℝ => t - c K) atTop atTop := by
      simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-c K) tendsto_id
    have h1 : Tendsto (fun t : ℝ => r * (epochIntensity c a K + (t - c K) / a K))
        atTop atTop :=
      (tendsto_atTop_add_const_left _ _ (h0.atTop_div_const haK)).const_mul_atTop hr
    exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h1)
  have hF0 : Tendsto F atTop (𝓝 0) := by
    have h2 := hG0.const_mul (-(a K / r))
    rw [mul_zero] at h2
    exact h2
  have hGint : IntegrableOn G (Set.Ioi (c K)) :=
    integrableOn_Ioi_deriv_of_nonneg' hderiv (fun t _ => (Real.exp_pos _).le) hF0
  have hGval : ∫ t in Set.Ioi (c K), G t = a K / r * Real.exp (-(r * epochIntensity c a K)) := by
    rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hGint hF0]
    simp only [F, G, sub_self, zero_div, add_zero]
    ring
  have heq : Set.EqOn G (fun t => Real.exp (-(r * cumIntensity (piecewiseSize K c a) t)))
      (Set.Ioi (c K)) := by
    intro t ht
    simp only [G]
    rw [cumIntensity_piecewiseSize_of_le h (le_of_lt ht)]
  exact ⟨hGint.congr_fun heq measurableSet_Ioi,
    (setIntegral_congr_fun measurableSet_Ioi heq).symm.trans hGval⟩

theorem integral_exp_neg_cumIntensity_piecewiseSize (h : IsEpochSchedule K c a) {r : ℝ}
    (hr : 0 < r) :
    IntegrableOn (fun t => Real.exp (-(r * cumIntensity (piecewiseSize K c a) t)))
        (Set.Ioi 0) ∧
      ∫ t in Set.Ioi 0, Real.exp (-(r * cumIntensity (piecewiseSize K c a) t)) =
        1 / r * (∑ e ∈ range K, a e * (Real.exp (-(r * epochIntensity c a e)) -
            Real.exp (-(r * epochIntensity c a (e + 1)))) +
          a K * Real.exp (-(r * epochIntensity c a K))) := by
  have hν := isSizeFunction_piecewiseSize h
  have hcK := h.nonneg (le_refl K)
  obtain ⟨htail, htailval⟩ := integral_exp_neg_cumIntensity_tail h hr
  have hpre : IntegrableOn
      (fun t => Real.exp (-(r * cumIntensity (piecewiseSize K c a) t))) (Set.Ioc 0 (c K)) :=
    (intervalIntegrable_exp_neg_cumIntensity hν r le_rfl hcK).1
  have hunion : Set.Ioc 0 (c K) ∪ Set.Ioi (c K) = Set.Ioi 0 := Set.Ioc_union_Ioi_eq_Ioi hcK
  refine ⟨hunion ▸ hpre.union htail, ?_⟩
  rw [← hunion, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hpre htail,
    htailval, ← intervalIntegral.integral_of_le hcK,
    integral_exp_neg_cumIntensity_prefix h le_rfl hr.ne', mul_add, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun e _ => by ring
  · ring

theorem lineageLaw_cumIntensity_nonneg {ν : ℝ → ℝ} (hν : IsSizeFunction ν) {n k : ℕ}
    (hk : 2 ≤ k) (hkn : k ≤ n) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ lineageLaw n (cumIntensity ν t) k := by
  have h := variableSizeLaw_real_lineageCount n hν (m := n - k) (by omega) ht
  rw [show n - (n - k) = k from by omega] at h
  rw [← h]
  exact measureReal_nonneg

theorem integral_lineageLaw_piecewiseSize (h : IsEpochSchedule K c a) (n : ℕ) {k : ℕ}
    (hk : 2 ≤ k) :
    IntegrableOn (fun t => lineageLaw n (cumIntensity (piecewiseSize K c a) t) k)
        (Set.Ioi 0) ∧
      ∫ t in Set.Ioi 0, lineageLaw n (cumIntensity (piecewiseSize K c a) t) k =
        piecewiseLevelTime n K c a k := by
  have hrate : ∀ j ∈ Icc k n, (0 : ℝ) < (coalRate j : ℝ) := by
    intro j hj
    have := mem_Icc.1 hj
    exact_mod_cast coalRate_pos (by omega : 2 ≤ j)
  have hL : (fun t => lineageLaw n (cumIntensity (piecewiseSize K c a) t) k) =
      fun t => ∑ j ∈ Icc k n,
        Real.exp (-((coalRate j : ℝ) * cumIntensity (piecewiseSize K c a) t)) *
          lineageCoeff n k j := by
    funext t
    simp only [lineageLaw, show 1 ≤ k from by omega, ↓reduceIte]
  have hint : ∀ j ∈ Icc k n, Integrable (fun t =>
      Real.exp (-((coalRate j : ℝ) * cumIntensity (piecewiseSize K c a) t)) *
        lineageCoeff n k j) (volume.restrict (Set.Ioi 0)) := fun j hj =>
    (integral_exp_neg_cumIntensity_piecewiseSize h (hrate j hj)).1.mul_const _
  rw [hL]
  refine ⟨integrable_finsetSum _ hint, ?_⟩
  rw [integral_finsetSum _ hint, piecewiseLevelTime]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [integral_mul_const, (integral_exp_neg_cumIntensity_piecewiseSize h (hrate j hj)).2]
  ring

theorem piecewiseLevelTime_nonneg (h : IsEpochSchedule K c a) {n k : ℕ} (hk : 2 ≤ k)
    (hkn : k ≤ n) : 0 ≤ piecewiseLevelTime n K c a k := by
  rw [← (integral_lineageLaw_piecewiseSize h n hk).2]
  exact setIntegral_nonneg measurableSet_Ioi fun t ht =>
    lineageLaw_cumIntensity_nonneg (isSizeFunction_piecewiseSize h) hk hkn (le_of_lt ht)

theorem lintegral_lineageLaw_piecewiseSize (h : IsEpochSchedule K c a) {n k : ℕ} (hk : 2 ≤ k)
    (hkn : k ≤ n) :
    ∫⁻ t in Set.Ioi 0,
        ENNReal.ofReal (lineageLaw n (cumIntensity (piecewiseSize K c a) t) k) =
      ENNReal.ofReal (piecewiseLevelTime n K c a k) := by
  obtain ⟨hint, hval⟩ := integral_lineageLaw_piecewiseSize h n hk
  rw [← hval, ofReal_integral_eq_lintegral_ofReal hint]
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact lineageLaw_cumIntensity_nonneg (isSizeFunction_piecewiseSize h) hk hkn (le_of_lt ht)

theorem variableSizeMarkedLaw_piecewise_sfs_mean (h : IsEpochSchedule K c a) {n i : ℕ}
    (hi : 1 ≤ i) (hin : i < n) (θ : ℝ≥0) :
    ∫ x, markedKingmanSfs n i x ∂variableSizeMarkedLaw n (piecewiseSize K c a) θ =
      piecewiseExpSfs θ n K c a i := by
  rw [variableSizeMarkedLaw_sfs_mean_of_levelTime (isSizeFunction_piecewiseSize h) hi hin θ
    (fun k => piecewiseLevelTime n K c a k)
    (fun k hk => piecewiseLevelTime_nonneg h (mem_Icc.1 hk).1 (mem_Icc.1 hk).2)
    (fun k hk => lintegral_lineageLaw_piecewiseSize h (mem_Icc.1 hk).1 (mem_Icc.1 hk).2),
    piecewiseExpSfs]

theorem piecewiseExpSfs_of_size_one (h : IsEpochSchedule K c a) (ha : ∀ e, e ≤ K → a e = 1)
    {n i : ℕ} (hi : 1 ≤ i) (hin : i < n) (θ : ℝ) :
    piecewiseExpSfs θ n K c a i = θ / i := by
  have hΛ : ∀ t : ℝ, 0 ≤ t → cumIntensity (piecewiseSize K c a) t = t := by
    intro t ht
    rw [cumIntensity_congr (ν₁ := piecewiseSize K c a) (ν₂ := fun _ => 1)
      (fun s _ => ha _ (card_filter_changePoint_le K c s)) ht, cumIntensity_one]
  have hlt : ∀ k ∈ Icc 2 n, piecewiseLevelTime n K c a k = ((holdingTime k : ℚ) : ℝ) := by
    intro k hk
    have hk' := mem_Icc.1 hk
    have h1 := lintegral_lineageLaw_piecewiseSize h hk'.1 hk'.2 (n := n)
    rw [setLIntegral_congr_fun measurableSet_Ioi
      (g := fun t => ENNReal.ofReal (lineageLaw n t k))
      (fun t ht => by simp only; rw [hΛ t (le_of_lt ht)]),
      lintegral_lineageLaw n hk'.1 hk'.2] at h1
    have hht : (0 : ℝ) ≤ ((holdingTime k : ℚ) : ℝ) := by
      have : (0 : ℚ) ≤ holdingTime k := div_nonneg zero_le_one (coalRate_nonneg k)
      exact_mod_cast this
    exact ((ENNReal.ofReal_eq_ofReal_iff hht
      (piecewiseLevelTime_nonneg h hk'.1 hk'.2)).1 h1).symm
  rw [piecewiseExpSfs, Finset.sum_congr rfl fun k hk => by rw [hlt k hk],
    sum_Icc_subtendProb_holdingTime hi hin, expSfsCoeff_eq hi hin]
  have hi0 : (i : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

end Rhone.Statistics
