/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.VariableSizeClock
public import Rhone.Coalescent.KingmanFiniteRewards
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.CDF

/-!
# The Kingman coalescent with a population-size function, as a time change

Source: griffiths_tavare1994, sec. 2, eq. (3)–(5), p. 404; durrett2008, Thm 4.6, eq. (4.5). -/

@[expose] public section

namespace Rhone.Coalescent

open MeasureTheory ProbabilityTheory Finset MarkovChain Filter
open scoped ENNReal

abbrev VariableSizePath (n : ℕ) :=
  (ℕ → Finpartition (Finset.univ : Finset (Fin n))) × (ℕ → ℝ)

noncomputable def variableSizeJumpTime (n : ℕ) (ν : ℝ → ℝ) (p : VariableSizePath n) (m : ℕ) :
    ℝ := cumIntensityInv ν ((partitionChain (Fin n)).jumpTime p m)

noncomputable def variableSizePath (n : ℕ) (ν : ℝ → ℝ) (p : VariableSizePath n) :
    VariableSizePath n := (p.1, variableSizeJumpTime n ν p)

noncomputable def variableSizeLaw (n : ℕ) (ν : ℝ → ℝ) : Measure (VariableSizePath n) :=
  ((partitionChain (Fin n)).jumpHoldLaw ⊥).map (variableSizePath n ν)

noncomputable def kingmanClockTime (n : ℕ) (e : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ l ∈ range m, e l / (coalRate (n - l) : ℝ)

noncomputable def clockPrefixExtend (m : ℕ) (x : Fin m → ℝ) (l : ℕ) : ℝ :=
  if h : l < m then x ⟨l, h⟩ else 0

variable {ν : ℝ → ℝ}

theorem IsSizeFunction.measurable_cumIntensity_max (hν : IsSizeFunction ν) :
    Measurable fun t : ℝ => cumIntensity ν (max 0 t) :=
  (hν.continuousOn.comp_continuous (continuous_const.max continuous_id)
    fun t => le_max_left 0 t).measurable

theorem measurable_partition_jumpTime (n m : ℕ) :
    Measurable fun p : VariableSizePath n => (partitionChain (Fin n)).jumpTime p m := by
  unfold RateChain.jumpTime RateChain.holdTime
  have hr : Measurable (partitionChain (Fin n)).rate := Measurable.of_discrete
  refine Finset.measurable_sum _ fun k _ => ?_
  fun_prop

theorem measurable_variableSizePath (n : ℕ) (hν : IsSizeFunction ν) :
    Measurable (variableSizePath n ν) :=
  measurable_fst.prodMk (measurable_pi_iff.2 fun m =>
    hν.measurable_cumIntensityInv.comp (measurable_partition_jumpTime n m))

theorem isProbabilityMeasure_variableSizeLaw (n : ℕ) (hν : IsSizeFunction ν) :
    IsProbabilityMeasure (variableSizeLaw n ν) :=
  (Measure.isProbabilityMeasure_map_iff
    (measurable_variableSizePath n hν).aemeasurable).mpr inferInstance

theorem expMeasure_one_Ioi (a : ℝ) :
    expMeasure 1 (Set.Ioi a) = ENNReal.ofReal (Real.exp (-(max 0 a))) := by
  have hc : (expMeasure 1).real (Set.Iic a) = if 0 ≤ a then 1 - Real.exp (-(1 * a)) else 0 := by
    rw [← cdf_eq_real, cdf_expMeasure_eq one_pos]
  have h1 : (expMeasure 1).real (Set.Ioi a) = 1 - (expMeasure 1).real (Set.Iic a) := by
    rw [← Set.compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]
  rw [← ofReal_measureReal, h1, hc]
  congr 1
  split_ifs with h
  · rw [max_eq_right h]
    ring_nf
  · rw [max_eq_left (not_le.1 h).le]
    simp

theorem expMeasure_one_Iio_zero : expMeasure 1 (Set.Iio 0) = 0 := by
  rw [expMeasure, gammaMeasure, withDensity_apply _ measurableSet_Iio]
  exact lintegral_gammaPDF_of_nonpos le_rfl

theorem ae_clockLaw_nonneg : ∀ᵐ e ∂clockLaw, ∀ k, 0 ≤ e k := by
  rw [ae_all_iff]
  intro k
  have h := Measure.infinitePi_map_eval (fun _ : ℕ => expMeasure 1) k
  have hz : clockLaw ((fun e : ℕ → ℝ => e k) ⁻¹' Set.Iio 0) = 0 := by
    rw [clockLaw, ← Measure.map_apply (measurable_pi_apply k) measurableSet_Iio, h]
    exact expMeasure_one_Iio_zero
  rw [ae_iff]
  convert hz using 2
  ext e
  simp

theorem lintegral_clockLaw_split (m : ℕ) {F : (Fin m → ℝ) × ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ e, F (fun j : Fin m => e j, e m) ∂clockLaw =
      ∫⁻ e, ∫⁻ y, F (fun j : Fin m => e j, y) ∂expMeasure 1 ∂clockLaw := by
  have hind : iIndepFun (fun (k : ℕ) (e : ℕ → ℝ) => e k) clockLaw :=
    iIndepFun_infinitePi (P := fun _ : ℕ => expMeasure 1) (X := fun _ => id)
      (fun _ => measurable_id)
  have hfs := hind.indepFun_finset (range m) {m} (by simp) (fun i => measurable_pi_apply i)
  have hφ : Measurable fun (x : {i // i ∈ range m} → ℝ) (j : Fin m) =>
      x ⟨(j : ℕ), mem_range.2 j.2⟩ := by fun_prop
  have hψ : Measurable fun (x : {i // i ∈ ({m} : Finset ℕ)} → ℝ) =>
      x ⟨m, mem_singleton_self m⟩ := by fun_prop
  have hXY : IndepFun (fun (e : ℕ → ℝ) (j : Fin m) => e j) (fun e : ℕ → ℝ => e m) clockLaw :=
    hfs.comp hφ hψ
  have hX : Measurable fun (e : ℕ → ℝ) (j : Fin m) => e j := by fun_prop
  have hY : Measurable fun e : ℕ → ℝ => e m := measurable_pi_apply m
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).1 hXY
  have hYlaw : clockLaw.map (fun e : ℕ → ℝ => e m) = expMeasure 1 :=
    Measure.infinitePi_map_eval (fun _ : ℕ => expMeasure 1) m
  rw [hYlaw] at hmap
  calc ∫⁻ e, F (fun j : Fin m => e j, e m) ∂clockLaw
      = ∫⁻ z, F z ∂clockLaw.map (fun e : ℕ → ℝ => ((fun j : Fin m => e j), e m)) :=
        (lintegral_map hF (hX.prodMk hY)).symm
    _ = ∫⁻ x, ∫⁻ y, F (x, y) ∂expMeasure 1
          ∂clockLaw.map (fun (e : ℕ → ℝ) (j : Fin m) => e j) := by
        rw [hmap, lintegral_prod _ hF.aemeasurable]
    _ = ∫⁻ e, ∫⁻ y, F (fun j : Fin m => e j, y) ∂expMeasure 1 ∂clockLaw :=
        lintegral_map hF.lintegral_prod_right' hX

theorem lintegral_prod_clockLaw_split {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [SFinite μ] (m : ℕ) {F : (Ω × (Fin m → ℝ)) × ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ p, F ((p.1, fun j : Fin m => p.2 j), p.2 m) ∂μ.prod clockLaw =
      ∫⁻ p, ∫⁻ y, F ((p.1, fun j : Fin m => p.2 j), y) ∂expMeasure 1 ∂μ.prod clockLaw := by
  have h1 : Measurable fun p : Ω × (ℕ → ℝ) =>
      F ((p.1, fun j : Fin m => p.2 j), p.2 m) := by fun_prop
  have h2 : Measurable fun p : Ω × (ℕ → ℝ) =>
      ∫⁻ y, F ((p.1, fun j : Fin m => p.2 j), y) ∂expMeasure 1 :=
    hF.lintegral_prod_right'.comp (by fun_prop)
  rw [lintegral_prod _ h1.aemeasurable, lintegral_prod _ h2.aemeasurable]
  refine lintegral_congr fun ω => ?_
  exact lintegral_clockLaw_split m (F := fun z => F ((ω, z.1), z.2)) (by fun_prop)

theorem kingmanClockTime_prefix (n : ℕ) (e : ℕ → ℝ) {j m : ℕ} (hj : j ≤ m) :
    kingmanClockTime n (clockPrefixExtend m fun l : Fin m => e l) j = kingmanClockTime n e j := by
  unfold kingmanClockTime
  refine Finset.sum_congr rfl fun l hl => ?_
  have h : l < m := lt_of_lt_of_le (mem_range.1 hl) hj
  simp only [clockPrefixExtend, h, ↓reduceDIte]

theorem measurable_kingmanClockTime_prefix (n m j : ℕ) :
    Measurable fun x : Fin m → ℝ => kingmanClockTime n (clockPrefixExtend m x) j := by
  unfold kingmanClockTime clockPrefixExtend
  refine Finset.measurable_sum _ fun l _ => ?_
  by_cases h : l < m
  · simp only [h, ↓reduceDIte]
    fun_prop
  · simp only [h, ↓reduceDIte]
    fun_prop

theorem kingmanClockTime_nonneg (n : ℕ) {e : ℕ → ℝ} (he : ∀ k, 0 ≤ e k) (m : ℕ) :
    0 ≤ kingmanClockTime n e m :=
  Finset.sum_nonneg fun l _ =>
    div_nonneg (he l) (by exact_mod_cast coalRate_nonneg (n - l))

theorem kingmanClockTime_mono (n : ℕ) {e : ℕ → ℝ} (he : ∀ k, 0 ≤ e k) {j m : ℕ}
    (hjm : j ≤ m) : kingmanClockTime n e j ≤ kingmanClockTime n e m :=
  Finset.sum_le_sum_of_subset_of_nonneg (range_mono hjm) fun l _ _ =>
    div_nonneg (he l) (by exact_mod_cast coalRate_nonneg (n - l))

theorem ae_jumpTime_eq_clockTime (n : ℕ) :
    ∀ᵐ p ∂(partitionChain (Fin n)).jumpHoldLaw ⊥, ∀ m, m < n →
      (partitionChain (Fin n)).jumpTime p m = kingmanClockTime n p.2 m := by
  have hae : ∀ᵐ p ∂(partitionChain (Fin n)).jumpHoldLaw ⊥,
      ∀ k : ℕ, (p.1 k).parts.card = max (n - k) (min n 1) :=
    Measure.quasiMeasurePreserving_fst.ae (partition_path_countdown_general n)
  filter_upwards [hae] with p hp m hm
  unfold RateChain.jumpTime kingmanClockTime RateChain.holdTime
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' := mem_range.1 hl
  rw [partitionChain_rate, hp l, show max (n - l) (min n 1) = n - l from by omega]

theorem ae_jumpHoldLaw_clock_nonneg (n : ℕ) :
    ∀ᵐ p ∂(partitionChain (Fin n)).jumpHoldLaw ⊥, ∀ k, 0 ≤ p.2 k :=
  Measure.quasiMeasurePreserving_snd.ae ae_clockLaw_nonneg

theorem variableSizeLaw_survival (n : ℕ) (hν : IsSizeFunction ν) {m : ℕ} (hm : m + 1 < n)
    {u : ℝ} (hu : 0 ≤ u)
    (G : (ℕ → Finpartition (Finset.univ : Finset (Fin n))) × (Fin (m + 1) → ℝ) → ℝ≥0∞)
    (hG : Measurable G) :
    ∫⁻ q, G (q.1, fun j => q.2 j) * (Set.Ioi u).indicator 1 (q.2 (m + 1))
        ∂variableSizeLaw n ν =
      ∫⁻ q, G (q.1, fun j => q.2 j) * ENNReal.ofReal (Real.exp (-((coalRate (n - m) : ℝ) *
        max 0 (cumIntensity ν u - cumIntensity ν (q.2 m))))) ∂variableSizeLaw n ν := by
  have hmap := measurable_variableSizePath n hν
  have hc : (0 : ℝ) < (coalRate (n - m) : ℝ) := by
    exact_mod_cast coalRate_pos (by omega : 2 ≤ n - m)
  let H : (ℕ → Finpartition (Finset.univ : Finset (Fin n))) × (Fin m → ℝ) → ℝ≥0∞ := fun z =>
    G (z.1, fun j : Fin (m + 1) =>
      cumIntensityInv ν (kingmanClockTime n (clockPrefixExtend m z.2) j))
  let a : (ℕ → Finpartition (Finset.univ : Finset (Fin n))) × (Fin m → ℝ) → ℝ := fun z =>
    (coalRate (n - m) : ℝ) *
      (cumIntensity ν u - kingmanClockTime n (clockPrefixExtend m z.2) m)
  have hH : Measurable H := by
    refine hG.comp (measurable_fst.prodMk (measurable_pi_iff.2 fun j => ?_))
    exact hν.measurable_cumIntensityInv.comp
      ((measurable_kingmanClockTime_prefix n m j).comp measurable_snd)
  have ha : Measurable a :=
    (measurable_const.sub ((measurable_kingmanClockTime_prefix n m m).comp
      measurable_snd)).const_mul _
  let F : ((ℕ → Finpartition (Finset.univ : Finset (Fin n))) × (Fin m → ℝ)) × ℝ → ℝ≥0∞ :=
    fun w => H w.1 * (if a w.1 < w.2 then 1 else 0)
  have hF : Measurable F :=
    (hH.comp measurable_fst).mul (Measurable.ite
      (measurableSet_lt (ha.comp measurable_fst) measurable_snd) measurable_const
      measurable_const)
  have hGl : Measurable fun q : VariableSizePath n =>
      G (q.1, fun j : Fin (m + 1) => q.2 j) := hG.comp (by fun_prop)
  have hae := (ae_jumpTime_eq_clockTime n).and (ae_jumpHoldLaw_clock_nonneg n)
  have hL : ∫⁻ q, G (q.1, fun j => q.2 j) * (Set.Ioi u).indicator 1 (q.2 (m + 1))
      ∂variableSizeLaw n ν =
      ∫⁻ p, F ((p.1, fun j : Fin m => p.2 j), p.2 m)
        ∂(partitionChain (Fin n)).jumpHoldLaw ⊥ := by
    have hmeasL : Measurable fun q : VariableSizePath n =>
        G (q.1, fun j : Fin (m + 1) => q.2 j) * (Set.Ioi u).indicator 1 (q.2 (m + 1)) :=
      hGl.mul ((measurable_one.indicator measurableSet_Ioi).comp
        ((measurable_pi_apply (m + 1)).comp measurable_snd))
    rw [variableSizeLaw, lintegral_map hmeasL hmap]
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with p hp
    obtain ⟨hT, he⟩ := hp
    have hpre : ∀ j : Fin (m + 1), variableSizeJumpTime n ν p j = cumIntensityInv ν
        (kingmanClockTime n (clockPrefixExtend m fun l : Fin m => p.2 l) j) := by
      intro j
      rw [variableSizeJumpTime, hT j (by omega), kingmanClockTime_prefix n p.2 (by omega)]
    have hstep : kingmanClockTime n p.2 (m + 1) =
        kingmanClockTime n p.2 m + p.2 m / (coalRate (n - m) : ℝ) := by
      unfold kingmanClockTime
      rw [Finset.sum_range_succ]
    have hiff : u < variableSizeJumpTime n ν p (m + 1) ↔
        (coalRate (n - m) : ℝ) * (cumIntensity ν u -
          kingmanClockTime n (clockPrefixExtend m fun l : Fin m => p.2 l) m) < p.2 m := by
      rw [variableSizeJumpTime, hν.lt_cumIntensityInv_iff hu, hT (m + 1) hm, hstep,
        kingmanClockTime_prefix n p.2 le_rfl, ← sub_lt_iff_lt_add', lt_div_iff₀ hc,
        mul_comm]
    simp only [variableSizePath, F, H, a, Set.indicator_apply, Set.mem_Ioi, Pi.one_apply]
    rw [funext hpre]
    by_cases hlt : u < variableSizeJumpTime n ν p (m + 1)
    · have h2 := hiff.1 hlt
      simp only [hlt, h2, ↓reduceIte]
    · have h2 : ¬ _ := fun h => hlt (hiff.2 h)
      simp only [hlt, h2, ↓reduceIte]
  have hR : ∫⁻ q, G (q.1, fun j => q.2 j) * ENNReal.ofReal (Real.exp
        (-((coalRate (n - m) : ℝ) * max 0 (cumIntensity ν u - cumIntensity ν (q.2 m)))))
      ∂variableSizeLaw n ν =
      ∫⁻ p, ∫⁻ y, F ((p.1, fun j : Fin m => p.2 j), y) ∂expMeasure 1
        ∂(partitionChain (Fin n)).jumpHoldLaw ⊥ := by
    have hinner : ∀ z, ∫⁻ y, F (z, y) ∂expMeasure 1 =
        H z * ENNReal.ofReal (Real.exp (-(max 0 (a z)))) := by
      intro z
      have hi : (fun y : ℝ => if a z < y then (1 : ℝ≥0∞) else 0) =
          (Set.Ioi (a z)).indicator 1 := by
        ext y
        simp [Set.indicator_apply]
      simp only [F]
      rw [lintegral_const_mul _ (Measurable.ite measurableSet_Ioi measurable_const
        measurable_const), hi, lintegral_indicator_one measurableSet_Ioi, expMeasure_one_Ioi]
    have hnn : ∀ᵐ q ∂variableSizeLaw n ν, 0 ≤ q.2 m :=
      (ae_map_iff hmap.aemeasurable (measurableSet_le measurable_const
        ((measurable_pi_apply m).comp measurable_snd))).2
        (Eventually.of_forall fun p => cumIntensityInv_nonneg ν _)
    have hmeasR : Measurable fun q : VariableSizePath n =>
        G (q.1, fun j : Fin (m + 1) => q.2 j) * ENNReal.ofReal (Real.exp
          (-((coalRate (n - m) : ℝ) *
            max 0 (cumIntensity ν u - cumIntensity ν (max 0 (q.2 m)))))) := by
      have h1 : Measurable fun q : VariableSizePath n => cumIntensity ν (max 0 (q.2 m)) :=
        hν.measurable_cumIntensity_max.comp ((measurable_pi_apply m).comp measurable_snd)
      exact hGl.mul (by fun_prop)
    have hcongr : ∫⁻ q, G (q.1, fun j => q.2 j) * ENNReal.ofReal (Real.exp
          (-((coalRate (n - m) : ℝ) * max 0 (cumIntensity ν u - cumIntensity ν (q.2 m)))))
        ∂variableSizeLaw n ν =
        ∫⁻ q, G (q.1, fun j => q.2 j) * ENNReal.ofReal (Real.exp
          (-((coalRate (n - m) : ℝ) *
            max 0 (cumIntensity ν u - cumIntensity ν (max 0 (q.2 m))))))
        ∂variableSizeLaw n ν := by
      refine lintegral_congr_ae ?_
      filter_upwards [hnn] with q hq
      rw [max_eq_right hq]
    rw [hcongr, variableSizeLaw, lintegral_map hmeasR hmap]
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with p hp
    obtain ⟨hT, he⟩ := hp
    have hpre : ∀ j : Fin (m + 1), variableSizeJumpTime n ν p j = cumIntensityInv ν
        (kingmanClockTime n (clockPrefixExtend m fun l : Fin m => p.2 l) j) := by
      intro j
      rw [variableSizeJumpTime, hT j (by omega), kingmanClockTime_prefix n p.2 (by omega)]
    have hTm : cumIntensity ν (max 0 (variableSizeJumpTime n ν p m)) =
        kingmanClockTime n (clockPrefixExtend m fun l : Fin m => p.2 l) m := by
      rw [variableSizeJumpTime, max_eq_right (cumIntensityInv_nonneg ν _), hT m (by omega),
        hν.cumIntensity_cumIntensityInv (kingmanClockTime_nonneg n he m),
        kingmanClockTime_prefix n p.2 le_rfl]
    rw [hinner]
    simp only [variableSizePath, H, a]
    rw [funext hpre, hTm, mul_max_of_nonneg _ _ hc.le, mul_zero]
  rw [hL, hR, RateChain.jumpHoldLaw]
  exact lintegral_prod_clockLaw_split _ m hF

theorem variableSizeLaw_survival_of_time (n : ℕ) (hν : IsSizeFunction ν) {m : ℕ}
    (hm : m + 1 < n) {u : ℝ} (hu : 0 ≤ u) {A : Set ℝ} (hA : MeasurableSet A) :
    variableSizeLaw n ν {q | q.2 m ∈ A ∧ u < q.2 (m + 1)} =
      ∫⁻ q in {q : VariableSizePath n | q.2 m ∈ A},
        ENNReal.ofReal (Real.exp (-((coalRate (n - m) : ℝ) *
          max 0 (cumIntensity ν u - cumIntensity ν (q.2 m))))) ∂variableSizeLaw n ν := by
  have hSA : MeasurableSet {q : VariableSizePath n | q.2 m ∈ A} :=
    ((measurable_pi_apply m).comp measurable_snd) hA
  have hSu : MeasurableSet {q : VariableSizePath n | u < q.2 (m + 1)} :=
    ((measurable_pi_apply (m + 1)).comp measurable_snd) measurableSet_Ioi
  let G : (ℕ → Finpartition (Finset.univ : Finset (Fin n))) × (Fin (m + 1) → ℝ) → ℝ≥0∞ :=
    fun z => A.indicator 1 (z.2 (Fin.last m))
  have hG : Measurable G :=
    (measurable_one.indicator hA).comp ((measurable_pi_apply _).comp measurable_snd)
  have key := variableSizeLaw_survival n hν hm hu G hG
  have hl : ∀ q : VariableSizePath n,
      G (q.1, fun j : Fin (m + 1) => q.2 j) * (Set.Ioi u).indicator 1 (q.2 (m + 1)) =
        {q : VariableSizePath n | q.2 m ∈ A ∧ u < q.2 (m + 1)}.indicator 1 q := by
    intro q
    by_cases h1 : q.2 m ∈ A <;> by_cases h2 : u < q.2 (m + 1) <;>
      simp [G, h1, h2]
  have hr : ∀ q : VariableSizePath n,
      G (q.1, fun j : Fin (m + 1) => q.2 j) * ENNReal.ofReal (Real.exp
        (-((coalRate (n - m) : ℝ) * max 0 (cumIntensity ν u - cumIntensity ν (q.2 m))))) =
        {q : VariableSizePath n | q.2 m ∈ A}.indicator (fun q => ENNReal.ofReal (Real.exp
          (-((coalRate (n - m) : ℝ) *
            max 0 (cumIntensity ν u - cumIntensity ν (q.2 m)))))) q := by
    intro q
    by_cases h1 : q.2 m ∈ A <;> simp [G, h1]
  have hSAu : MeasurableSet {q : VariableSizePath n | q.2 m ∈ A ∧ u < q.2 (m + 1)} :=
    hSA.inter hSu
  rw [lintegral_congr hl, lintegral_congr hr, lintegral_indicator hSAu,
    lintegral_indicator hSA] at key
  simpa using key

theorem variableSizeLaw_first_coalescence (n : ℕ) (hν : IsSizeFunction ν) (hn : 2 ≤ n)
    {u : ℝ} (hu : 0 ≤ u) :
    variableSizeLaw n ν {q | u < q.2 1} =
      ENNReal.ofReal (Real.exp (-((coalRate n : ℝ) * cumIntensity ν u))) := by
  have := isProbabilityMeasure_variableSizeLaw n hν
  have h0 : ∀ᵐ q ∂variableSizeLaw n ν, q.2 0 = 0 := by
    have hS : MeasurableSet {q : VariableSizePath n | q.2 0 = 0} :=
      ((measurable_pi_apply 0).comp measurable_snd) (measurableSet_singleton 0)
    rw [variableSizeLaw, ae_map_iff (measurable_variableSizePath n hν).aemeasurable hS]
    refine Filter.Eventually.of_forall fun p => ?_
    simp [variableSizePath, variableSizeJumpTime, RateChain.jumpTime,
      cumIntensityInv_of_nonpos]
  have key := variableSizeLaw_survival_of_time n hν (m := 0) (by omega) hu
    (A := Set.univ) MeasurableSet.univ
  simp only [Set.mem_univ, true_and, Set.ofPred_true, Measure.restrict_univ, zero_add,
    Nat.sub_zero] at key
  rw [key]
  have hc : ∫⁻ q, ENNReal.ofReal (Real.exp (-((coalRate n : ℝ) *
        max 0 (cumIntensity ν u - cumIntensity ν (q.2 0))))) ∂variableSizeLaw n ν =
      ∫⁻ _, ENNReal.ofReal (Real.exp (-((coalRate n : ℝ) * cumIntensity ν u)))
        ∂variableSizeLaw n ν := by
    refine lintegral_congr_ae ?_
    filter_upwards [h0] with q hq
    rw [hq, cumIntensity_zero, sub_zero, max_eq_right (hν.cumIntensity_nonneg hu)]
  rw [hc, lintegral_const, measure_univ, mul_one]

end Rhone.Coalescent
