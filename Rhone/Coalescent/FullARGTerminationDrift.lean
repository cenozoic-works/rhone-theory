/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcSupport.CountKernel
public import Rhone.Coalescent.SmcSupport.MarkedEventRates
public import Rhone.Coalescent.SmcSupport.SamplerValidity
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# One-step drift of the unrestricted backward sampler behind `fullARGGenealogyLaw`

Source: griffiths_marjoram1997, sec. 1; griffiths1991_two_locus_graph, p. 101. -/
@[expose] public section

namespace Rhone.Coalescent.IntervalProcess
open MeasureTheory ProbabilityTheory SmcSupport
open scoped ENNReal

noncomputable def absorptionBudget (R : ℝ) (m : ℕ) : ℝ :=
  countBudget R ⌈2 * R⌉₊ (m - 1)

noncomputable def truncatedBudget (R : ℝ) (m : ℕ) (y : AugmentedState) : ℝ :=
  countBudget R ⌈2 * R⌉₊ (min (y.1.2.2.1 - 1) m)

open scoped Classical in
noncomputable def absorptionPotential (R : ℝ) (z : AugmentedState) : ℝ≥0∞ :=
  if Valid z.1 then ENNReal.ofReal (absorptionBudget R z.1.2.2.1) else ⊤

def activeStates : Set AugmentedState := {z | 2 ≤ z.1.2.2.1}

theorem activeStates_measurable : MeasurableSet activeStates :=
  measurableSet_le measurable_const
    (Rhone.Coalescent.IntervalProcess.liveCount_measurable.comp measurable_fst)

theorem absorptionPotential_measurable (R : ℝ) : Measurable (absorptionPotential R) := by
  classical
  unfold absorptionPotential
  exact Measurable.ite (measurable_fst validState_measurable)
    (ENNReal.measurable_ofReal.comp ((measurable_of_countable (absorptionBudget R)).comp
      (Rhone.Coalescent.IntervalProcess.liveCount_measurable.comp measurable_fst)))
    measurable_const

theorem absorptionPotential_initial (R : ℝ) (N : ℕ) (r : EventRecord) :
    absorptionPotential R (initialState N, r) = ENNReal.ofReal (absorptionBudget R N) := by
  classical
  unfold absorptionPotential
  rw [ite_eq_left (initialState_valid N)]
  rfl

theorem sampleStep_liveCount_le (R : ℝ) (s : State) (u : Noise) :
    (sampleStep false R s u).1.2.2.1 ≤ s.2.2.1 + 1 := by
  classical
  unfold sampleStep
  split_ifs with h
  · exact Nat.le_succ _
  · cases selectedAction false R s u with
    | none => exact Nat.le_succ _
    | some a =>
      cases a with
      | inl ij =>
        change (coalSuccessor s ij.1 ij.2).2.2.1 ≤ _
        by_cases hij : ij.1.val < ij.2.val
        · have := coalSuccessor_count s ij.1 ij.2 hij
          omega
        · rw [coalSuccessor, ite_eq_right hij]
          exact Nat.le_succ _
      | inr i =>
        change (splitSuccessor s i _).2.2.1 ≤ _
        rw [splitSuccessor_count]

theorem unrestricted_split_prob_le (R : ℝ) (hR : 0 ≤ R) (s : State) (hs : Valid s)
    (hm : 1 < s.2.2.1) :
    (markedLaw false R s splitSet).toReal ≤ R / (R + ((s.2.2.1 - 1 : ℕ) : ℝ)) := by
  have ht := unrestricted_totalRate_positive R s hm
  rw [markedLaw_split_mass false R s hm (ne_of_gt ht), ENNReal.toReal_div]
  simp only [ENNReal.coe_toReal]
  rw [splitRate_eq_recombinationRate R hR s, totalRate_unrestricted_real R hR s]
  obtain ⟨h0, h1⟩ := recombinationRate_bounds R hR s hs
  have hcast : ((s.2.2.1 - 1 : ℕ) : ℝ) = (s.2.2.1 : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  rw [hcast]
  have hm' : (2 : ℝ) ≤ (s.2.2.1 : ℝ) := by exact_mod_cast hm
  generalize (s.2.2.1 : ℝ) = m at h1 hm' ⊢
  generalize recombinationRate R s = σ at h0 h1 ⊢
  have hn : (0 : ℝ) ≤ m - 1 := by linarith
  rw [div_le_div_iff₀ (by nlinarith) (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_right h1 hn]

theorem eventKernel_truncatedBudget_le (R : ℝ) (hR : 0 ≤ R) (z : AugmentedState)
    (hz : Valid z.1) (hm : 1 < z.1.2.2.1) :
    ∫ y, truncatedBudget R z.1.2.2.1 y ∂eventKernel false R z ≤
      absorptionBudget R z.1.2.2.1 - 1 := by
  have ht := unrestricted_totalRate_positive R z.1 hm
  have he := integral_event_count false R z hm ht
    (fun n => countBudget R ⌈2 * R⌉₊ (min n z.1.2.2.1))
  have hstep := countBudget_step_le R hR ⌈2 * R⌉₊ (z.1.2.2.1 - 1) (Nat.le_ceil _)
    (by omega) (markedLaw false R z.1 splitSet).toReal ENNReal.toReal_nonneg
    (unrestricted_split_prob_le R hR z.1 hz hm)
  have he1 : z.1.2.2.1 - 1 + 1 = z.1.2.2.1 := by omega
  have he2 : z.1.2.2.1 - 1 - 1 = z.1.2.2.1 - 2 := by omega
  rw [he1, he2] at hstep
  have hmin : min (z.1.2.2.1 - 2) z.1.2.2.1 = z.1.2.2.1 - 2 := min_eq_left (Nat.sub_le _ _)
  simp only [min_self, hmin] at he
  unfold truncatedBudget absorptionBudget
  rw [he]
  linarith

theorem eventKernel_absorptionPotential_drift (R : ℝ) (hR : 0 ≤ R)
    (z : AugmentedState) :
    ∫⁻ y, absorptionPotential R y ∂eventKernel false R z +
      activeStates.indicator 1 z ≤ absorptionPotential R z := by
  classical
  by_cases hz : Valid z.1
  swap
  · have htop : absorptionPotential R z = ⊤ := by
      unfold absorptionPotential
      rw [ite_eq_right hz]
    rw [htop]
    exact le_top
  have hpot : absorptionPotential R z = ENNReal.ofReal (absorptionBudget R z.1.2.2.1) := by
    unfold absorptionPotential
    rw [ite_eq_left hz]
  have hmap : Measurable (fun u => sampleStep false R z.1 u) :=
    (sampleStep_measurable false R).comp (measurable_const.prodMk measurable_id)
  have hlin : ∫⁻ y, absorptionPotential R y ∂eventKernel false R z =
      ∫⁻ u, absorptionPotential R (sampleStep false R z.1 u) ∂noiseLaw := by
    rw [eventKernel_apply, lintegral_map (absorptionPotential_measurable R) hmap]
  by_cases hm : 2 ≤ z.1.2.2.1
  swap
  · have hstep : ∀ u, sampleStep false R z.1 u = (z.1, (z.1.1, .inl ())) := by
      intro u
      unfold sampleStep
      rw [ite_eq_left (Or.inl (by omega))]
    have hconst : ∀ u, absorptionPotential R (sampleStep false R z.1 u) =
        absorptionPotential R z := by
      intro u
      rw [hstep u]
      rfl
    rw [hlin, lintegral_congr hconst, lintegral_const, measure_univ, mul_one,
      Set.indicator_of_notMem (show z ∉ activeStates from hm), add_zero]
  · have hm1 : 1 < z.1.2.2.1 := hm
    have hg : Measurable (truncatedBudget R z.1.2.2.1) :=
      (measurable_of_countable (fun n : ℕ => countBudget R ⌈2 * R⌉₊ (min n z.1.2.2.1))).comp
        ((Rhone.Coalescent.IntervalProcess.liveCount_measurable.comp measurable_fst).sub_const 1)
    have hg0 : ∀ y, 0 ≤ truncatedBudget R z.1.2.2.1 y :=
      fun y => countBudget_nonneg R hR _ _
    have hgb : ∀ y, truncatedBudget R z.1.2.2.1 y ≤ countBudget R ⌈2 * R⌉₊ z.1.2.2.1 :=
      fun y => countBudget_monotone R hR _ (min_le_right _ _)
    have hgi : Integrable (truncatedBudget R z.1.2.2.1) (eventKernel false R z) :=
      Integrable.of_bound hg.aestronglyMeasurable (countBudget R ⌈2 * R⌉₊ z.1.2.2.1)
        (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hg0 y)]
          exact hgb y)
    have hbo := eventKernel_truncatedBudget_le R hR z hz hm1
    have hint0 : 0 ≤ ∫ y, truncatedBudget R z.1.2.2.1 y ∂eventKernel false R z :=
      integral_nonneg hg0
    have hae : ∀ᵐ u ∂noiseLaw, absorptionPotential R (sampleStep false R z.1 u) =
        ENNReal.ofReal (truncatedBudget R z.1.2.2.1 (sampleStep false R z.1 u)) := by
      filter_upwards [noiseLaw_interior] with u hu
      have hv := sampleStep_valid false R z.1 hz u (hu 1).1.le (hu 1).2.le (hu 2).1 (hu 2).2
      have hc := sampleStep_liveCount_le R z.1 u
      unfold absorptionPotential truncatedBudget absorptionBudget
      rw [ite_eq_left hv, min_eq_left (by omega)]
    have hreal : ENNReal.ofReal (∫ y, truncatedBudget R z.1.2.2.1 y ∂eventKernel false R z) =
        ∫⁻ u, ENNReal.ofReal (truncatedBudget R z.1.2.2.1 (sampleStep false R z.1 u))
          ∂noiseLaw := by
      rw [ofReal_integral_eq_lintegral_ofReal hgi (Filter.Eventually.of_forall hg0),
        eventKernel_apply]
      exact lintegral_map (f := fun y => ENNReal.ofReal (truncatedBudget R z.1.2.2.1 y))
        (ENNReal.measurable_ofReal.comp hg) hmap
    have hone : activeStates.indicator (1 : AugmentedState → ℝ≥0∞) z = ENNReal.ofReal 1 := by
      rw [Set.indicator_of_mem (show z ∈ activeStates from hm), ENNReal.ofReal_one]
      rfl
    rw [hlin, lintegral_congr_ae hae, ← hreal, hone, hpot]
    calc
      ENNReal.ofReal (∫ y, truncatedBudget R z.1.2.2.1 y ∂eventKernel false R z) +
          ENNReal.ofReal 1 ≤
          ENNReal.ofReal (absorptionBudget R z.1.2.2.1 - 1) + ENNReal.ofReal 1 :=
        add_le_add (ENNReal.ofReal_le_ofReal hbo) le_rfl
      _ = ENNReal.ofReal (absorptionBudget R z.1.2.2.1) := by
        rw [← ENNReal.ofReal_add (by linarith) zero_le_one]
        congr 1
        ring

theorem lintegral_neg_log_unitUniform :
    ∫⁻ v, ENNReal.ofReal (-Real.log v) ∂unitUniform = 1 := by
  have hI : IntegrableOn (fun v : ℝ => -Real.log v) (Set.Ioc 0 1) volume :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      intervalIntegral.intervalIntegrable_log').neg
  have hval : ∫ v in Set.Ioc (0 : ℝ) 1, -Real.log v = 1 := by
    rw [← intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_neg,
      integral_log]
    simp
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] fun v => -Real.log v := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    exact neg_nonneg.mpr (Real.log_nonpos hv.1.le hv.2)
  rw [unitUniform, Measure.restrict_congr_set Ioo_ae_eq_Ioc,
    ← ofReal_integral_eq_lintegral_ofReal hI hnn, hval, ENNReal.ofReal_one]

theorem sampleStep_time_le_clock (R : ℝ) (s : State) (hm : 2 ≤ s.2.2.1) (u : Noise)
    (h0 : 0 < u 1) (h1 : u 1 < 1) :
    (sampleStep false R s u).1.1 ≤ s.1 + -Real.log (u 1) := by
  have hT : (1 : ℝ) ≤ (totalRate false R s : ℝ) := by
    rw [totalRate_eq, NNReal.coe_add, coalRate_unrestricted]
    have h2 : (2 : ℝ) ≤ (s.2.2.1 : ℝ) := by exact_mod_cast hm
    have h3 : (0 : ℝ) ≤ (splitRate R s : ℝ) := NNReal.coe_nonneg _
    nlinarith
  have hl : Real.log (u 1) ≤ 0 := Real.log_nonpos h0.le h1.le
  have hd : -Real.log (u 1) / (totalRate false R s : ℝ) ≤ -Real.log (u 1) :=
    div_le_self (by linarith) hT
  have ht : s.1 - Real.log (u 1) / (totalRate false R s : ℝ) ≤ s.1 + -Real.log (u 1) := by
    rw [neg_div] at hd
    linarith
  have hs : s.1 ≤ s.1 + -Real.log (u 1) := by linarith
  classical
  unfold sampleStep
  split_ifs
  · exact hs
  · cases selectedAction false R s u with
    | none => exact hs
    | some a => cases a <;> exact ht

theorem eventKernel_time_drift (R : ℝ) (z : AugmentedState) :
    ∫⁻ y, ENNReal.ofReal y.1.1 ∂eventKernel false R z ≤
      ENNReal.ofReal z.1.1 + activeStates.indicator 1 z := by
  have hmap : Measurable (fun u => sampleStep false R z.1 u) :=
    (sampleStep_measurable false R).comp (measurable_const.prodMk measurable_id)
  have htime : Measurable (fun y : AugmentedState => ENNReal.ofReal y.1.1) :=
    ENNReal.measurable_ofReal.comp measurable_fst.fst
  rw [eventKernel_apply, lintegral_map htime hmap]
  by_cases hm : 2 ≤ z.1.2.2.1
  · have hone : activeStates.indicator (1 : AugmentedState → ℝ≥0∞) z = 1 := by
      rw [Set.indicator_of_mem (show z ∈ activeStates from hm)]
      rfl
    have hclock : ∫⁻ u, ENNReal.ofReal (-Real.log (u 1)) ∂noiseLaw = 1 := by
      have h := lintegral_map (μ := noiseLaw)
        (f := fun v : ℝ => ENNReal.ofReal (-Real.log v)) (g := fun u : Noise => u 1)
        (ENNReal.measurable_ofReal.comp Real.measurable_log.neg) (measurable_pi_apply 1)
      rw [noiseLaw_eval, lintegral_neg_log_unitUniform] at h
      exact h.symm
    rw [hone]
    calc
      ∫⁻ u, ENNReal.ofReal (sampleStep false R z.1 u).1.1 ∂noiseLaw ≤
          ∫⁻ u, (ENNReal.ofReal z.1.1 + ENNReal.ofReal (-Real.log (u 1))) ∂noiseLaw := by
        apply lintegral_mono_ae
        filter_upwards [noiseLaw_interior] with u hu
        exact (ENNReal.ofReal_le_ofReal
          (sampleStep_time_le_clock R z.1 hm u (hu 1).1 (hu 1).2)).trans ENNReal.ofReal_add_le
      _ = ENNReal.ofReal z.1.1 + 1 := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          hclock]
  · have hstep : ∀ u, sampleStep false R z.1 u = (z.1, (z.1.1, .inl ())) := by
      intro u
      unfold sampleStep
      rw [ite_eq_left (Or.inl (by omega))]
    have hconst : ∀ u, ENNReal.ofReal (sampleStep false R z.1 u).1.1 =
        ENNReal.ofReal z.1.1 := by
      intro u
      rw [hstep u]
    rw [lintegral_congr hconst, lintegral_const, measure_univ, mul_one,
      Set.indicator_of_notMem (show z ∉ activeStates from hm), add_zero]

end Rhone.Coalescent.IntervalProcess
