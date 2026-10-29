/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.VariableSizeCoalescent
public import Rhone.Coalescent.LineageCountLaw

/-!
# The number of ancestral lineages of the variable-size coalescent, and expected times

Source: griffiths_tavare1994, sec. 2, eq. (5), p. 404; durrett2008, Thm 4.6, eq. (4.5); tavare1984,
eq. (6.1), p. 132. -/

@[expose] public section

namespace Rhone.Coalescent

open MeasureTheory ProbabilityTheory Finset MarkovChain Filter
open scoped ENNReal

noncomputable def lineageCdf (n : ℕ) (τ : ℝ) (m : ℕ) : ℝ :=
  1 - ∑ j ∈ range m, lineageLaw n τ (n - j)

theorem lineageLaw_zero (n : ℕ) {j : ℕ} (hj : 1 ≤ j) (hjn : j ≤ n) :
    lineageLaw n 0 j = if j = n then 1 else 0 := by
  rw [← sum_lineageCoeff n j hj hjn]
  simp [lineageLaw, hj]

theorem lineageLaw_succ_self (n : ℕ) (t : ℝ) : lineageLaw n t (n + 1) = 0 := by
  simp [lineageLaw]

theorem continuous_lineageLaw (n j : ℕ) : Continuous fun t => lineageLaw n t j := by
  unfold lineageLaw
  split_ifs
  · fun_prop
  · exact continuous_const

theorem sum_lineageLaw_zero (n : ℕ) {m : ℕ} (hm : m < n) :
    ∑ j ∈ range (m + 1), lineageLaw n 0 (n - j) = 1 := by
  rw [Finset.sum_eq_single 0]
  · rw [Nat.sub_zero, lineageLaw_zero n (by omega) le_rfl, ite_eq_left rfl]
  · intro j hj hj0
    have hj' := mem_range.1 hj
    rw [lineageLaw_zero n (by omega) (by omega), ite_eq_right (by omega)]
  · intro h
    exact absurd (mem_range.2 (Nat.succ_pos m)) h

theorem hasDerivAt_sum_lineageLaw (n : ℕ) {m : ℕ} (hm : m < n) (t : ℝ) :
    HasDerivAt (fun s => ∑ j ∈ range (m + 1), lineageLaw n s (n - j))
      (-((coalRate (n - m) : ℝ) * lineageLaw n t (n - m))) t := by
  induction m with
  | zero =>
    have h := hasDerivAt_lineageLaw n n le_rfl t
    rw [lineageLaw_succ_self] at h
    simp only [zero_add, range_one, sum_singleton, Nat.sub_zero]
    convert h using 1
    ring
  | succ m ih =>
    have h1 := ih (by omega)
    have h2 := hasDerivAt_lineageLaw n (n - (m + 1)) (Nat.sub_le _ _) t
    rw [show n - (m + 1) + 1 = n - m from by omega] at h2
    have h3 := h1.add h2
    have hfun : (fun s => ∑ j ∈ range (m + 1 + 1), lineageLaw n s (n - j)) =
        fun s => ∑ j ∈ range (m + 1), lineageLaw n s (n - j) + lineageLaw n s (n - (m + 1)) := by
      funext s
      rw [Finset.sum_range_succ]
    rw [hfun]
    convert h3 using 1
    ring

theorem sum_lineageLaw_succ_eq (n : ℕ) {m : ℕ} (hm : m < n) (τ : ℝ) :
    ∑ j ∈ range (m + 1), lineageLaw n τ (n - j) =
      Real.exp (-((coalRate (n - m) : ℝ) * τ)) *
        (1 + ∫ s in (0 : ℝ)..τ, (coalRate (n - m) : ℝ) * Real.exp ((coalRate (n - m) : ℝ) * s) *
          ∑ j ∈ range m, lineageLaw n s (n - j)) := by
  set c : ℝ := (coalRate (n - m) : ℝ) with hc
  let g : ℝ → ℝ := fun s => c * Real.exp (c * s) * ∑ j ∈ range m, lineageLaw n s (n - j)
  have hg : Continuous g := by
    refine (continuous_const.mul (by fun_prop)).mul ?_
    exact continuous_finsetSum _ fun j _ => continuous_lineageLaw n (n - j)
  let φ : ℝ → ℝ := fun s => Real.exp (c * s) * ∑ j ∈ range (m + 1), lineageLaw n s (n - j)
  let ψ : ℝ → ℝ := fun s => 1 + ∫ x in (0 : ℝ)..s, g x
  have hφ : ∀ s, HasDerivAt φ (g s) s := by
    intro s
    have h1 : HasDerivAt (fun s => Real.exp (c * s)) (Real.exp (c * s) * c) s := by
      have h := ((hasDerivAt_id s).const_mul c).exp
      simpa using h
    have h2 := h1.mul (hasDerivAt_sum_lineageLaw n hm s)
    convert h2 using 1
    simp only [g, Finset.sum_range_succ, ← hc]
    ring
  have hψ : ∀ s, HasDerivAt ψ (g s) s := fun s =>
    ((hg.integral_hasStrictDerivAt 0 s).hasDerivAt).const_add 1
  have hd : ∀ s, HasDerivAt (fun s => φ s - ψ s) 0 s := by
    intro s
    have h := (hφ s).sub (hψ s)
    rw [sub_self] at h
    exact h
  have hconst := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) τ 0
  have h0 : φ 0 - ψ 0 = 0 := by
    simp [φ, ψ, sum_lineageLaw_zero n hm]
  have hφψ : φ τ = ψ τ := by
    have := hconst.trans h0
    linarith
  have hexp : Real.exp (-(c * τ)) * Real.exp (c * τ) = 1 := by
    rw [← Real.exp_add]
    simp
  calc ∑ j ∈ range (m + 1), lineageLaw n τ (n - j)
      = Real.exp (-(c * τ)) * φ τ := by
        simp only [φ]
        rw [← mul_assoc, hexp, one_mul]
    _ = Real.exp (-(c * τ)) * ψ τ := by rw [hφψ]

theorem ofReal_exp_survival_eq_lintegral {c : ℝ} (hc : 0 < c) {τ : ℝ} (hτ : 0 ≤ τ) (T : ℝ) :
    ENNReal.ofReal (Real.exp (-(c * max 0 (τ - max 0 T)))) =
      ENNReal.ofReal (Real.exp (-(c * τ))) *
        (1 + ∫⁻ s in Set.Ioc 0 τ,
          ENNReal.ofReal (c * Real.exp (c * s)) * (if s < T then 1 else 0)) := by
  have hb0 : 0 ≤ min τ (max 0 T) := le_min hτ (le_max_left 0 T)
  have hset : ∫⁻ s in Set.Ioc 0 τ,
        ENNReal.ofReal (c * Real.exp (c * s)) * (if s < T then 1 else 0) =
      ∫⁻ s in Set.Ioc 0 (min τ (max 0 T)), ENNReal.ofReal (c * Real.exp (c * s)) := by
    have h1 : ∀ s, ENNReal.ofReal (c * Real.exp (c * s)) * (if s < T then 1 else 0) =
        (Set.Iio T).indicator (fun s => ENNReal.ofReal (c * Real.exp (c * s))) s := by
      intro s
      by_cases h : s < T <;> simp [h]
    rw [lintegral_congr h1, lintegral_indicator measurableSet_Iio,
      Measure.restrict_restrict measurableSet_Iio]
    by_cases hT : T ≤ τ
    · have hS : Set.Iio T ∩ Set.Ioc 0 τ = Set.Ioo 0 (min τ (max 0 T)) := by
        ext s
        simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioc, Set.mem_Ioo, lt_min_iff,
          lt_max_iff]
        constructor
        · rintro ⟨h1, h2, h3⟩
          exact ⟨h2, lt_of_lt_of_le h1 hT, Or.inr h1⟩
        · rintro ⟨h1, h2, h3⟩
          rcases h3 with h3 | h3
          · exact absurd h1 (lt_asymm h3)
          · exact ⟨h3, h1, h2.le⟩
      rw [hS]
      exact setLIntegral_congr Ioo_ae_eq_Ioc
    · have hT' := not_le.1 hT
      have hS : Set.Iio T ∩ Set.Ioc 0 τ = Set.Ioc 0 (min τ (max 0 T)) := by
        rw [min_eq_left (hT'.le.trans (le_max_right 0 T))]
        ext s
        simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioc]
        constructor
        · rintro ⟨_, h2, h3⟩
          exact ⟨h2, h3⟩
        · rintro ⟨h2, h3⟩
          exact ⟨lt_of_le_of_lt h3 hT', h2, h3⟩
      rw [hS]
  have hint : ∫⁻ s in Set.Ioc 0 (min τ (max 0 T)), ENNReal.ofReal (c * Real.exp (c * s)) =
      ENNReal.ofReal (Real.exp (c * min τ (max 0 T)) - 1) := by
    have hcont : Continuous fun s : ℝ => c * Real.exp (c * s) := by fun_prop
    rw [← ofReal_integral_eq_lintegral_ofReal
      ((hcont.intervalIntegrable 0 _).1)
      (Filter.Eventually.of_forall fun s => by positivity),
      ← intervalIntegral.integral_of_le hb0]
    congr 1
    have hderiv : ∀ s ∈ Set.uIcc 0 (min τ (max 0 T)),
        HasDerivAt (fun s => Real.exp (c * s)) (c * Real.exp (c * s)) s := by
      intro s _
      have h := ((hasDerivAt_id s).const_mul c).exp
      simpa [mul_comm] using h
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable 0 _)]
    simp
  rw [hset, hint]
  have h1 : (1 : ℝ≥0∞) = ENNReal.ofReal 1 := by simp
  have hge : (0 : ℝ) ≤ Real.exp (c * min τ (max 0 T)) - 1 := by
    have := Real.one_le_exp (mul_nonneg hc.le hb0)
    linarith
  rw [h1, ← ENNReal.ofReal_add zero_le_one hge, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    add_sub_cancel, ← Real.exp_add]
  congr 2
  rcases le_total τ (max 0 T) with h | h
  · rw [min_eq_left h, max_eq_left (sub_nonpos.2 h)]
    ring
  · rw [min_eq_right h, max_eq_right (sub_nonneg.2 h)]
    ring

theorem jumpHoldLaw_jumpTime_survival (n : ℕ) {m : ℕ} (hm : m + 1 < n) {τ : ℝ} (hτ : 0 ≤ τ) :
    (partitionChain (Fin n)).jumpHoldLaw ⊥
        {p | τ < (partitionChain (Fin n)).jumpTime p (m + 1)} =
      ∫⁻ p, ENNReal.ofReal (Real.exp (-((coalRate (n - m) : ℝ) *
        max 0 (τ - max 0 ((partitionChain (Fin n)).jumpTime p m)))))
        ∂(partitionChain (Fin n)).jumpHoldLaw ⊥ := by
  have key := variableSizeLaw_survival_of_time n isSizeFunction_one hm hτ (A := Set.univ)
    MeasurableSet.univ
  simp only [Set.mem_univ, true_and, Set.ofPred_true, Measure.restrict_univ,
    cumIntensity_one] at key
  have hmap := measurable_variableSizePath n isSizeFunction_one
  have hS : MeasurableSet {q : VariableSizePath n | τ < q.2 (m + 1)} :=
    ((measurable_pi_apply (m + 1)).comp measurable_snd) measurableSet_Ioi
  have hf : Measurable fun q : VariableSizePath n => ENNReal.ofReal (Real.exp
      (-((coalRate (n - m) : ℝ) * max 0 (τ - q.2 m)))) := by fun_prop
  rw [variableSizeLaw, Measure.map_apply hmap hS, lintegral_map hf hmap] at key
  have hpre : variableSizePath n (fun _ => 1) ⁻¹' {q : VariableSizePath n | τ < q.2 (m + 1)} =
      {p | τ < (partitionChain (Fin n)).jumpTime p (m + 1)} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, variableSizePath, variableSizeJumpTime,
      cumIntensityInv_one, lt_max_iff, not_lt.2 hτ, false_or]
  rw [hpre] at key
  rw [key]
  refine lintegral_congr fun p => ?_
  simp only [variableSizePath, variableSizeJumpTime, cumIntensityInv_one]

theorem jumpHoldLaw_real_lt_jumpTime (n : ℕ) {m : ℕ} (hm : m < n) {τ : ℝ} (hτ : 0 ≤ τ) :
    ((partitionChain (Fin n)).jumpHoldLaw ⊥).real
      {p | τ < (partitionChain (Fin n)).jumpTime p m} =
      ∑ j ∈ range m, lineageLaw n τ (n - j) := by
  induction m generalizing τ with
  | zero =>
    have h : {p : VariableSizePath n | τ < (partitionChain (Fin n)).jumpTime p 0} = ∅ := by
      ext p
      simp [RateChain.jumpTime, not_lt.2 hτ]
    rw [h]
    simp
  | succ m ih =>
    have hc : (0 : ℝ) < (coalRate (n - m) : ℝ) := by
      exact_mod_cast coalRate_pos (by omega : 2 ≤ n - m)
    set c : ℝ := (coalRate (n - m) : ℝ) with hcdef
    have hT := measurable_partition_jumpTime n m
    have ihm : ∀ s : ℝ, 0 ≤ s → ((partitionChain (Fin n)).jumpHoldLaw ⊥).real
        {p | s < (partitionChain (Fin n)).jumpTime p m} =
        ∑ j ∈ range m, lineageLaw n s (n - j) := fun s hs => ih (by omega) hs
    let g : ℝ → ℝ := fun s => c * Real.exp (c * s) * ∑ j ∈ range m, lineageLaw n s (n - j)
    have hg : Continuous g := by
      refine (continuous_const.mul (by fun_prop)).mul ?_
      exact continuous_finsetSum _ fun j _ => continuous_lineageLaw n (n - j)
    have hunc : Measurable (Function.uncurry fun (p : VariableSizePath n) (s : ℝ) =>
        ENNReal.ofReal (c * Real.exp (c * s)) *
          (if s < (partitionChain (Fin n)).jumpTime p m then (1 : ℝ≥0∞) else 0)) := by
      change Measurable fun z : VariableSizePath n × ℝ =>
        ENNReal.ofReal (c * Real.exp (c * z.2)) *
          (if z.2 < (partitionChain (Fin n)).jumpTime z.1 m then (1 : ℝ≥0∞) else 0)
      refine Measurable.mul (by fun_prop) (Measurable.ite ?_ measurable_const measurable_const)
      exact measurableSet_lt measurable_snd (hT.comp measurable_fst)
    have hstep1 : (partitionChain (Fin n)).jumpHoldLaw ⊥
          {p | τ < (partitionChain (Fin n)).jumpTime p (m + 1)} =
        ENNReal.ofReal (Real.exp (-(c * τ))) * (1 + ∫⁻ s in Set.Ioc 0 τ,
          ENNReal.ofReal (c * Real.exp (c * s)) * (partitionChain (Fin n)).jumpHoldLaw ⊥
            {p | s < (partitionChain (Fin n)).jumpTime p m}) := by
      rw [jumpHoldLaw_jumpTime_survival n hm hτ,
        lintegral_congr fun p => ofReal_exp_survival_eq_lintegral hc hτ _,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left measurable_const,
        lintegral_const, measure_univ, mul_one, lintegral_lintegral_swap hunc.aemeasurable]
      congr 2
      refine lintegral_congr fun s => ?_
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      congr 1
      have hSs : MeasurableSet {p : VariableSizePath n |
          s < (partitionChain (Fin n)).jumpTime p m} := measurableSet_lt measurable_const hT
      rw [← lintegral_indicator_one hSs]
      refine lintegral_congr fun p => ?_
      by_cases h : s < (partitionChain (Fin n)).jumpTime p m <;> simp [h]
    have hstep2 : ∫⁻ s in Set.Ioc 0 τ,
          ENNReal.ofReal (c * Real.exp (c * s)) * (partitionChain (Fin n)).jumpHoldLaw ⊥
            {p | s < (partitionChain (Fin n)).jumpTime p m} =
        ENNReal.ofReal (∫ s in Set.Ioc 0 τ, g s) := by
      have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc 0 τ)] g := by
        rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
        refine Filter.Eventually.of_forall fun s hs => ?_
        simp only [Pi.zero_apply, g]
        rw [← ihm s hs.1.le]
        positivity
      rw [ofReal_integral_eq_lintegral_ofReal (hg.intervalIntegrable 0 τ).1 hnn]
      refine setLIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
      simp only [g]
      rw [← ihm s hs.1.le, ENNReal.ofReal_mul (p := c * Real.exp (c * s)) (by positivity),
        ofReal_measureReal]
    have hint_nn : 0 ≤ ∫ s in Set.Ioc 0 τ, g s := by
      refine setIntegral_nonneg measurableSet_Ioc fun s hs => ?_
      simp only [g]
      rw [← ihm s hs.1.le]
      positivity
    rw [measureReal_def, hstep1, hstep2, sum_lineageLaw_succ_eq n (by omega) τ,
      intervalIntegral.integral_of_le hτ]
    have h1 : (1 : ℝ≥0∞) = ENNReal.ofReal 1 := by simp
    rw [h1, ← ENNReal.ofReal_add zero_le_one hint_nn,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.toReal_ofReal (by positivity)]

theorem ae_jumpTime_mono (n : ℕ) :
    ∀ᵐ p ∂(partitionChain (Fin n)).jumpHoldLaw ⊥, ∀ m, m + 1 < n →
      (partitionChain (Fin n)).jumpTime p m ≤ (partitionChain (Fin n)).jumpTime p (m + 1) := by
  filter_upwards [ae_jumpTime_eq_clockTime n, ae_jumpHoldLaw_clock_nonneg n] with p hT he m hm
  rw [hT m (by omega), hT (m + 1) hm]
  exact kingmanClockTime_mono n he (Nat.le_succ m)

theorem jumpHoldLaw_real_jumpTime_le (n : ℕ) {m : ℕ} (hm : m < n) {τ : ℝ} (hτ : 0 ≤ τ) :
    ((partitionChain (Fin n)).jumpHoldLaw ⊥).real
      {p | (partitionChain (Fin n)).jumpTime p m ≤ τ} = lineageCdf n τ m := by
  have hS : MeasurableSet {p : VariableSizePath n |
      τ < (partitionChain (Fin n)).jumpTime p m} :=
    measurableSet_lt measurable_const (measurable_partition_jumpTime n m)
  have hset : {p : VariableSizePath n | (partitionChain (Fin n)).jumpTime p m ≤ τ} =
      {p | τ < (partitionChain (Fin n)).jumpTime p m}ᶜ := by
    ext p
    simp
  rw [hset, probReal_compl_eq_one_sub hS, jumpHoldLaw_real_lt_jumpTime n hm hτ, lineageCdf]

theorem jumpHoldLaw_real_lineageCount (n : ℕ) {m : ℕ} (hm : m + 1 < n) {τ : ℝ} (hτ : 0 ≤ τ) :
    ((partitionChain (Fin n)).jumpHoldLaw ⊥).real
      {p | (partitionChain (Fin n)).jumpTime p m ≤ τ ∧
        τ < (partitionChain (Fin n)).jumpTime p (m + 1)} = lineageLaw n τ (n - m) := by
  have hC : MeasurableSet {p : VariableSizePath n |
      τ < (partitionChain (Fin n)).jumpTime p m} :=
    measurableSet_lt measurable_const (measurable_partition_jumpTime n m)
  have hae : ({p : VariableSizePath n | τ < (partitionChain (Fin n)).jumpTime p (m + 1)} :
        Set (VariableSizePath n)) =ᵐ[(partitionChain (Fin n)).jumpHoldLaw ⊥]
      ({p | (partitionChain (Fin n)).jumpTime p m ≤ τ ∧
        τ < (partitionChain (Fin n)).jumpTime p (m + 1)} ∪
        {p | τ < (partitionChain (Fin n)).jumpTime p m} : Set (VariableSizePath n)) := by
    refine Filter.eventuallyEqSet_iff.2 ?_
    filter_upwards [ae_jumpTime_mono n] with p hp
    have hmono := hp m hm
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · intro h
      rcases le_or_gt ((partitionChain (Fin n)).jumpTime p m) τ with h1 | h1
      · exact Or.inl ⟨h1, h⟩
      · exact Or.inr h1
    · rintro (h | h)
      · exact h.2
      · exact lt_of_lt_of_le h hmono
  have hdisj : Disjoint {p : VariableSizePath n | (partitionChain (Fin n)).jumpTime p m ≤ τ ∧
        τ < (partitionChain (Fin n)).jumpTime p (m + 1)}
      {p | τ < (partitionChain (Fin n)).jumpTime p m} := by
    rw [Set.disjoint_left]
    rintro p ⟨h1, _⟩ h2
    exact absurd h2 (not_lt.2 h1)
  have h1 := measureReal_congr hae
  rw [measureReal_union hdisj hC, jumpHoldLaw_real_lt_jumpTime n (by omega) hτ,
    jumpHoldLaw_real_lt_jumpTime n (by omega) hτ, Finset.sum_range_succ] at h1
  linarith

variable {ν : ℝ → ℝ}

theorem variableSizeLaw_real_lineageCount (n : ℕ) (hν : IsSizeFunction ν) {m : ℕ}
    (hm : m + 1 < n) {t : ℝ} (ht : 0 ≤ t) :
    (variableSizeLaw n ν).real {q | q.2 m ≤ t ∧ t < q.2 (m + 1)} =
      lineageLaw n (cumIntensity ν t) (n - m) := by
  have hS : MeasurableSet {q : VariableSizePath n | q.2 m ≤ t ∧ t < q.2 (m + 1)} :=
    (measurableSet_le ((measurable_pi_apply m).comp measurable_snd) measurable_const).inter
      (measurableSet_lt measurable_const ((measurable_pi_apply (m + 1)).comp measurable_snd))
  rw [variableSizeLaw, map_measureReal_apply (measurable_variableSizePath n hν) hS,
    ← jumpHoldLaw_real_lineageCount n hm (hν.cumIntensity_nonneg ht)]
  congr 1
  ext p
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, variableSizePath, variableSizeJumpTime]
  rw [hν.lt_cumIntensityInv_iff ht, ← not_lt, hν.lt_cumIntensityInv_iff ht, not_lt]

theorem ae_variableSizeLaw_zero (n : ℕ) (hν : IsSizeFunction ν) :
    ∀ᵐ q ∂variableSizeLaw n ν, q.2 0 = 0 := by
  have hS : MeasurableSet {q : VariableSizePath n | q.2 0 = 0} :=
    ((measurable_pi_apply 0).comp measurable_snd) (measurableSet_singleton 0)
  rw [variableSizeLaw, ae_map_iff (measurable_variableSizePath n hν).aemeasurable hS]
  refine Filter.Eventually.of_forall fun p => ?_
  simp [variableSizePath, variableSizeJumpTime, RateChain.jumpTime,
    cumIntensityInv_of_nonpos]

theorem ae_variableSizeLaw_nonneg (n : ℕ) (hν : IsSizeFunction ν) :
    ∀ᵐ q ∂variableSizeLaw n ν, ∀ m, 0 ≤ q.2 m := by
  rw [ae_all_iff]
  intro m
  have hS : MeasurableSet {q : VariableSizePath n | 0 ≤ q.2 m} :=
    measurableSet_le measurable_const ((measurable_pi_apply m).comp measurable_snd)
  rw [variableSizeLaw, ae_map_iff (measurable_variableSizePath n hν).aemeasurable hS]
  exact Filter.Eventually.of_forall fun p => cumIntensityInv_nonneg ν _

theorem ae_variableSizeLaw_mono (n : ℕ) (hν : IsSizeFunction ν) :
    ∀ᵐ q ∂variableSizeLaw n ν, ∀ m, m + 1 < n → q.2 m ≤ q.2 (m + 1) := by
  rw [ae_all_iff]
  intro m
  by_cases hm : m + 1 < n
  · have hS : MeasurableSet {q : VariableSizePath n | m + 1 < n → q.2 m ≤ q.2 (m + 1)} := by
      simp only [hm, forall_const]
      exact measurableSet_le ((measurable_pi_apply m).comp measurable_snd)
        ((measurable_pi_apply (m + 1)).comp measurable_snd)
    rw [variableSizeLaw, ae_map_iff (measurable_variableSizePath n hν).aemeasurable hS]
    filter_upwards [ae_jumpTime_mono n] with p hp _
    exact hν.monotone_cumIntensityInv (hp m hm)
  · exact Filter.Eventually.of_forall fun q h => absurd h hm

theorem ofReal_sub_eq_lintegral_Ioi {a : ℝ} (ha : 0 ≤ a) (b : ℝ) :
    ENNReal.ofReal (b - a) =
      ∫⁻ t in Set.Ioi (0 : ℝ), if a ≤ t ∧ t < b then (1 : ℝ≥0∞) else 0 := by
  have h1 : ∀ t : ℝ, (if a ≤ t ∧ t < b then (1 : ℝ≥0∞) else 0) =
      (Set.Ico a b).indicator 1 t := by
    intro t
    by_cases h : a ≤ t ∧ t < b
    · simp [h]
    · have h' : t ∉ Set.Ico a b := h
      simp [h, h']
  rw [lintegral_congr h1, lintegral_indicator_one measurableSet_Ico,
    Measure.restrict_apply measurableSet_Ico]
  refine le_antisymm ?_ ?_
  · rw [← Real.volume_Ioo]
    refine measure_mono fun t ht => ⟨⟨ht.1.le, ht.2⟩, ?_⟩
    exact lt_of_le_of_lt ha ht.1
  · rw [← Real.volume_Ico]
    exact measure_mono Set.inter_subset_left

theorem lintegral_variableSizeLaw_levelTime (n : ℕ) (hν : IsSizeFunction ν) {m : ℕ}
    (hm : m + 1 < n) :
    ∫⁻ q, ENNReal.ofReal (q.2 (m + 1) - q.2 m) ∂variableSizeLaw n ν =
      ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (lineageLaw n (cumIntensity ν t) (n - m)) := by
  have := isProbabilityMeasure_variableSizeLaw n hν
  have hunc : Measurable (Function.uncurry fun (q : VariableSizePath n) (t : ℝ) =>
      if q.2 m ≤ t ∧ t < q.2 (m + 1) then (1 : ℝ≥0∞) else 0) := by
    change Measurable fun z : VariableSizePath n × ℝ =>
      if z.1.2 m ≤ z.2 ∧ z.2 < z.1.2 (m + 1) then (1 : ℝ≥0∞) else 0
    refine Measurable.ite ?_ measurable_const measurable_const
    exact (measurableSet_le (by fun_prop) measurable_snd).inter
      (measurableSet_lt measurable_snd (by fun_prop))
  have h1 : ∫⁻ q, ENNReal.ofReal (q.2 (m + 1) - q.2 m) ∂variableSizeLaw n ν =
      ∫⁻ q, (∫⁻ t in Set.Ioi (0 : ℝ),
        (if q.2 m ≤ t ∧ t < q.2 (m + 1) then (1 : ℝ≥0∞) else 0) ∂volume)
        ∂variableSizeLaw n ν := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_variableSizeLaw_nonneg n hν] with q hq
    exact ofReal_sub_eq_lintegral_Ioi (hq m) _
  rw [h1, lintegral_lintegral_swap hunc.aemeasurable]
  refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have hS : MeasurableSet {q : VariableSizePath n | q.2 m ≤ t ∧ t < q.2 (m + 1)} :=
    (measurableSet_le ((measurable_pi_apply m).comp measurable_snd) measurable_const).inter
      (measurableSet_lt measurable_const ((measurable_pi_apply (m + 1)).comp measurable_snd))
  have h2 : ∀ q : VariableSizePath n,
      (if q.2 m ≤ t ∧ t < q.2 (m + 1) then (1 : ℝ≥0∞) else 0) =
        {q : VariableSizePath n | q.2 m ≤ t ∧ t < q.2 (m + 1)}.indicator 1 q := by
    intro q
    by_cases h : q.2 m ≤ t ∧ t < q.2 (m + 1)
    · simp [h]
    · have h' : q ∉ {q : VariableSizePath n | q.2 m ≤ t ∧ t < q.2 (m + 1)} := h
      simp [h, h']
  rw [lintegral_congr h2, lintegral_indicator_one hS,
    ← variableSizeLaw_real_lineageCount n hν hm (le_of_lt ht), ofReal_measureReal]

theorem measurable_kingmanClockTime (n j : ℕ) :
    Measurable fun e : ℕ → ℝ => kingmanClockTime n e j := by
  unfold kingmanClockTime
  fun_prop

theorem lintegral_variableSizeLaw_mul_levelTime (n : ℕ) (hν : IsSizeFunction ν) {m : ℕ}
    (hm : m + 1 < n) (f : Finpartition (Finset.univ : Finset (Fin n)) → ℝ≥0∞) :
    ∫⁻ q, f (q.1 m) * ENNReal.ofReal (q.2 (m + 1) - q.2 m) ∂variableSizeLaw n ν =
      (∫⁻ ω, f (ω m) ∂(partitionChain (Fin n)).jumpChain.pathLaw ⊥) *
        ∫⁻ q, ENNReal.ofReal (q.2 (m + 1) - q.2 m) ∂variableSizeLaw n ν := by
  have hmap := measurable_variableSizePath n hν
  let w : (ℕ → ℝ) → ℝ≥0∞ := fun e => ENNReal.ofReal
    (cumIntensityInv ν (kingmanClockTime n e (m + 1)) - cumIntensityInv ν (kingmanClockTime n e m))
  have hw : Measurable w :=
    ((hν.measurable_cumIntensityInv.comp (measurable_kingmanClockTime n (m + 1))).sub
      (hν.measurable_cumIntensityInv.comp (measurable_kingmanClockTime n m))).ennreal_ofReal
  have key : ∀ g : Finpartition (Finset.univ : Finset (Fin n)) → ℝ≥0∞,
      ∫⁻ q, g (q.1 m) * ENNReal.ofReal (q.2 (m + 1) - q.2 m) ∂variableSizeLaw n ν =
        (∫⁻ ω, g (ω m) ∂(partitionChain (Fin n)).jumpChain.pathLaw ⊥) *
          ∫⁻ e, w e ∂clockLaw := by
    intro g
    have hg : Measurable fun ω : ℕ → Finpartition (Finset.univ : Finset (Fin n)) => g (ω m) :=
      (Measurable.of_discrete (f := g)).comp (measurable_pi_apply m)
    have hmeas : Measurable fun q : VariableSizePath n =>
        g (q.1 m) * ENNReal.ofReal (q.2 (m + 1) - q.2 m) :=
      (hg.comp measurable_fst).mul (by fun_prop)
    rw [variableSizeLaw, lintegral_map hmeas hmap, RateChain.jumpHoldLaw,
      ← lintegral_prod_mul hg.aemeasurable hw.aemeasurable, ← RateChain.jumpHoldLaw]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_jumpTime_eq_clockTime n] with p hT
    simp only [variableSizePath, variableSizeJumpTime, w]
    rw [hT (m + 1) hm, hT m (by omega)]
  have hone := key fun _ => 1
  simp only [one_mul, lintegral_const, measure_univ] at hone
  rw [key f, hone]

theorem lintegral_prod_snd_of_isProbabilityMeasure {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (μ : Measure α) [IsProbabilityMeasure μ] (ν' : Measure β) [SFinite ν']
    {g : β → ℝ≥0∞} (hg : Measurable g) : ∫⁻ z, g z.2 ∂μ.prod ν' = ∫⁻ y, g y ∂ν' := by
  rw [lintegral_prod (fun z : α × β => g z.2) (hg.comp measurable_snd).aemeasurable]
  simp

theorem lintegral_variableSizeLaw_one_levelTime (n : ℕ) {m : ℕ} (hm : m + 1 < n) :
    ∫⁻ q, ENNReal.ofReal (q.2 (m + 1) - q.2 m) ∂variableSizeLaw n (fun _ => 1) =
      ENNReal.ofReal (holdingTime (n - m) : ℝ) := by
  have hmap := measurable_variableSizePath n isSizeFunction_one
  have hc : (0 : ℝ) < (coalRate (n - m) : ℝ) := by
    exact_mod_cast coalRate_pos (by omega : 2 ≤ n - m)
  have hmeas : Measurable fun q : VariableSizePath n =>
      ENNReal.ofReal (q.2 (m + 1) - q.2 m) := by fun_prop
  have hg : Measurable fun e : ℕ → ℝ =>
      ENNReal.ofReal (1 / (coalRate (n - m) : ℝ)) * ENNReal.ofReal (e m) := by fun_prop
  rw [variableSizeLaw, lintegral_map hmeas hmap]
  have h1 : ∫⁻ p, ENNReal.ofReal ((variableSizePath n (fun _ => 1) p).2 (m + 1) -
        (variableSizePath n (fun _ => 1) p).2 m) ∂(partitionChain (Fin n)).jumpHoldLaw ⊥ =
      ∫⁻ p, ENNReal.ofReal (1 / (coalRate (n - m) : ℝ)) * ENNReal.ofReal (p.2 m)
        ∂(partitionChain (Fin n)).jumpHoldLaw ⊥ := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_jumpTime_eq_clockTime n, ae_jumpHoldLaw_clock_nonneg n] with p hT he
    simp only [variableSizePath, variableSizeJumpTime, cumIntensityInv_one]
    rw [hT (m + 1) hm, hT m (by omega), max_eq_right (kingmanClockTime_nonneg n he _),
      max_eq_right (kingmanClockTime_nonneg n he _),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    unfold kingmanClockTime
    rw [Finset.sum_range_succ]
    ring
  rw [h1, RateChain.jumpHoldLaw, lintegral_prod_snd_of_isProbabilityMeasure _ _ hg,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_ofReal_clockLaw, mul_one]
  congr 1
  simp [holdingTime]

theorem lintegral_lineageLaw (n : ℕ) {k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) :
    ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (lineageLaw n t k) =
      ENNReal.ofReal (holdingTime k : ℝ) := by
  have hm : n - k + 1 < n := by omega
  have h1 := lintegral_variableSizeLaw_levelTime n isSizeFunction_one hm
  rw [lintegral_variableSizeLaw_one_levelTime n hm] at h1
  simp only [cumIntensity_one, show n - (n - k) = k from by omega] at h1
  exact h1.symm

theorem sum_range_sub_eq_sum_Icc {M : Type*} [AddCommMonoid M] (n : ℕ) (F : ℕ → M) :
    ∑ m ∈ range (n - 1), F (n - m) = ∑ k ∈ Icc 2 n, F k := by
  refine Finset.sum_nbij' (fun m => n - m) (fun k => n - k) ?_ ?_ ?_ ?_ ?_
  · intro m hm
    have := mem_range.1 hm
    exact mem_Icc.2 ⟨by omega, by omega⟩
  · intro k hk
    have := mem_Icc.1 hk
    exact mem_range.2 (by omega)
  · intro m hm
    have := mem_range.1 hm
    change n - (n - m) = m
    omega
  · intro k hk
    have := mem_Icc.1 hk
    change n - (n - k) = k
    omega
  · intro m _
    rfl

theorem lintegral_variableSizeLaw_tmrca (n : ℕ) (hν : IsSizeFunction ν) :
    ∫⁻ q, ENNReal.ofReal (q.2 (n - 1)) ∂variableSizeLaw n ν =
      ∑ k ∈ Icc 2 n,
        ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (lineageLaw n (cumIntensity ν t) k) := by
  have h1 : ∫⁻ q, ENNReal.ofReal (q.2 (n - 1)) ∂variableSizeLaw n ν =
      ∫⁻ q, ∑ m ∈ range (n - 1), ENNReal.ofReal (q.2 (m + 1) - q.2 m)
        ∂variableSizeLaw n ν := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_variableSizeLaw_zero n hν, ae_variableSizeLaw_mono n hν] with q h0 hmono
    rw [← ENNReal.ofReal_sum_of_nonneg, Finset.sum_range_sub (fun m => q.2 m), h0, sub_zero]
    intro m hm
    have := mem_range.1 hm
    exact sub_nonneg.2 (hmono m (by omega))
  rw [h1, lintegral_finsetSum _ fun m _ => by fun_prop,
    ← sum_range_sub_eq_sum_Icc n fun k =>
      ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (lineageLaw n (cumIntensity ν t) k)]
  refine Finset.sum_congr rfl fun m hm => ?_
  have := mem_range.1 hm
  exact lintegral_variableSizeLaw_levelTime n hν (by omega)

noncomputable def variableSizeTreeLength (n : ℕ) (q : VariableSizePath n) : ℝ :=
  ∑ m : Fin (n - 1), ((n : ℝ) - (m : ℕ)) * (q.2 ((m : ℕ) + 1) - q.2 m)

theorem lintegral_variableSizeLaw_treeLength (n : ℕ) (hν : IsSizeFunction ν) :
    ∫⁻ q, ENNReal.ofReal (variableSizeTreeLength n q) ∂variableSizeLaw n ν =
      ∑ k ∈ Icc 2 n, (k : ℝ≥0∞) *
        ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (lineageLaw n (cumIntensity ν t) k) := by
  have h1 : ∫⁻ q, ENNReal.ofReal (variableSizeTreeLength n q) ∂variableSizeLaw n ν =
      ∫⁻ q, ∑ m ∈ range (n - 1), ((n - m : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (q.2 (m + 1) - q.2 m) ∂variableSizeLaw n ν := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_variableSizeLaw_mono n hν] with q hmono
    have hsum : variableSizeTreeLength n q =
        ∑ m ∈ range (n - 1), ((n - m : ℕ) : ℝ) * (q.2 (m + 1) - q.2 m) := by
      rw [variableSizeTreeLength,
        Fin.sum_univ_eq_sum_range (fun m => ((n : ℝ) - m) * (q.2 (m + 1) - q.2 m)) (n - 1)]
      refine Finset.sum_congr rfl fun m hm => ?_
      have := mem_range.1 hm
      rw [Nat.cast_sub (by omega)]
    rw [hsum, ENNReal.ofReal_sum_of_nonneg]
    · refine Finset.sum_congr rfl fun m hm => ?_
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    · intro m hm
      have := mem_range.1 hm
      exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.2 (hmono m (by omega)))
  rw [h1, lintegral_finsetSum _ fun m _ => by fun_prop,
    ← sum_range_sub_eq_sum_Icc n fun k => (k : ℝ≥0∞) *
      ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (lineageLaw n (cumIntensity ν t) k)]
  refine Finset.sum_congr rfl fun m hm => ?_
  have := mem_range.1 hm
  rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _),
    lintegral_variableSizeLaw_levelTime n hν (by omega)]

end Rhone.Coalescent
