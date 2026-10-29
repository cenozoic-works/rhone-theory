/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.TwoParameterMarkovFlow
public import Rhone.Statistics.Identifiability.TimeVaryingPairFlow
public import Rhone.Statistics.Identifiability.ConditionalClockLaw
public import Mathlib.Probability.Kernel.WithDensity

/-! # Proper conditional exit laws for the continuous time-dependent pair chain -/

@[expose] public section

open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology ENNReal
namespace Rhone.Statistics.Identifiability

noncomputable def timeVaryingPairTransition (k : ℕ) (c q : ℝ → ℝ)
    (s t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  inhomogeneousTransition (fun t => MarkovChain.Identifiability.pairGenerator k (c t) (q t)) s t

noncomputable def timeVaryingPairSurvival (k : ℕ) (c q : ℝ → ℝ)
    (s : ℝ) (i : Fin 2) (t : ℝ) : ℝ :=
  ∑ j, timeVaryingPairTransition k c q s t i j

noncomputable def timeVaryingPairExitDensity (k : ℕ) (c q : ℝ → ℝ)
    (s : ℝ) (i : Fin 2) (t : ℝ) : ℝ :=
  timeVaryingPairTransition k c q s t i 0 * c t

@[simp] theorem timeVaryingPairTransition_self (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (s : ℝ) :
    timeVaryingPairTransition k c q s s = 1 :=
  inhomogeneousTransition_self _ (timeVaryingPairGenerator_continuous k c q hc hq) s

@[simp] theorem timeVaryingPairSurvival_self (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (s : ℝ) (i : Fin 2) :
    timeVaryingPairSurvival k c q s i s = 1 := by
  simp [timeVaryingPairSurvival, timeVaryingPairTransition_self k c q hc hq,
    Matrix.one_apply]

theorem timeVaryingPairTransition_continuous (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) :
    Continuous (fun p : ℝ × ℝ => timeVaryingPairTransition k c q p.1 p.2) :=
  inhomogeneousTransition_continuous _ (timeVaryingPairGenerator_continuous k c q hc hq)

theorem timeVaryingPairExitDensity_continuous (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (i : Fin 2) :
    Continuous (fun p : ℝ × ℝ => timeVaryingPairExitDensity k c q p.1 i p.2) := by
  exact (((continuous_apply 0).comp ((continuous_apply i).comp
    (timeVaryingPairTransition_continuous k c q hc hq)))).mul (hc.comp continuous_snd)

theorem timeVaryingPairTransition_nonneg (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q)
    (hqn : ∀ t, 0 ≤ t → 0 ≤ q t) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (i j : Fin 2) :
    0 ≤ timeVaryingPairTransition k c q s t i j :=
  inhomogeneousTransition_nonneg _ (timeVaryingPairGenerator_continuous k c q hc hq)
    (fun t ht => pairGenerator_metzler k (hqn t ht)) hs hst i j

theorem timeVaryingPairExitDensity_nonneg (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (i : Fin 2) :
    0 ≤ timeVaryingPairExitDensity k c q s i t :=
  mul_nonneg (timeVaryingPairTransition_nonneg k c q hc hq hqn hs hst i 0)
    (hcn t (hs.trans hst))

theorem timeVaryingPairSurvival_hasDerivAt (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (s t : ℝ) (i : Fin 2) :
    HasDerivAt (timeVaryingPairSurvival k c q s i)
      (-timeVaryingPairExitDensity k c q s i t) t := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
    inhomogeneousTransition_hasDerivAt_right _
      (timeVaryingPairGenerator_continuous k c q hc hq) s t i j)
  convert! h using 1
  change -(inhomogeneousTransition
      (fun t => MarkovChain.Identifiability.pairGenerator k (c t) (q t)) s t i 0 * c t) =
    ∑ j, ∑ l, inhomogeneousTransition
        (fun t => MarkovChain.Identifiability.pairGenerator k (c t) (q t)) s t i l *
      MarkovChain.Identifiability.pairGenerator k (c t) (q t) l j
  simp [MarkovChain.Identifiability.pairGenerator, Fin.sum_univ_two]
  ring

theorem timeVaryingPairExitCDF_hasDerivAt (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (s t : ℝ) (i : Fin 2) :
    HasDerivAt (fun u => 1 - timeVaryingPairSurvival k c q s i u)
      (timeVaryingPairExitDensity k c q s i t) t := by
  simpa only [neg_neg] using
    (timeVaryingPairSurvival_hasDerivAt k c q hc hq s t i).const_sub 1

theorem timeVaryingPairExitDensity_integrable (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    {s : ℝ} (hs : 0 ≤ s) (i : Fin 2)
    (htail : Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0)) :
    IntegrableOn (timeVaryingPairExitDensity k c q s i) (Ioi s) := by
  exact integrableOn_Ioi_deriv_of_nonneg'
    (fun t _ => timeVaryingPairExitCDF_hasDerivAt k c q hc hq s t i)
    (fun t ht => timeVaryingPairExitDensity_nonneg k c q hc hq hcn hqn hs ht.le i)
    (htail.const_sub 1)

theorem timeVaryingPairExitDensity_integral_one (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    {s : ℝ} (hs : 0 ≤ s) (i : Fin 2)
    (htail : Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0)) :
    (∫ t in Ioi s, timeVaryingPairExitDensity k c q s i t) = 1 := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun t _ => timeVaryingPairExitCDF_hasDerivAt k c q hc hq s t i)
    (fun t ht => timeVaryingPairExitDensity_nonneg k c q hc hq hcn hqn hs ht.le i)
    (htail.const_sub 1)
  simpa only [sub_zero, timeVaryingPairSurvival_self k c q hc hq, sub_self] using h

theorem timeVaryingPairExitDensity_lintegral_one (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    {s : ℝ} (hs : 0 ≤ s) (i : Fin 2)
    (htail : Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0)) :
    (∫⁻ t in Ioi s, ENNReal.ofReal (timeVaryingPairExitDensity k c q s i t)) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (timeVaryingPairExitDensity_integrable k c q hc hq hcn hqn hs i htail)]
  · rw [timeVaryingPairExitDensity_integral_one k c q hc hq hcn hqn hs i htail,
      ENNReal.ofReal_one]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact timeVaryingPairExitDensity_nonneg k c q hc hq hcn hqn hs ht.le i

noncomputable def timeVaryingPairExitLaw (k : ℕ) (c q : ℝ → ℝ)
    (s : ℝ) (i : Fin 2) : Measure ℝ :=
  (volume.restrict (Ioi s)).withDensity
    (fun t => ENNReal.ofReal (timeVaryingPairExitDensity k c q s i t))

theorem timeVaryingPairExitLaw_probability (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    {s : ℝ} (hs : 0 ≤ s) (i : Fin 2)
    (htail : Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0)) :
    IsProbabilityMeasure (timeVaryingPairExitLaw k c q s i) := by
  constructor
  rw [timeVaryingPairExitLaw, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  exact timeVaryingPairExitDensity_lintegral_one k c q hc hq hcn hqn hs i htail

theorem timeVaryingPairExitDensity_integral_tail (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    {s u : ℝ} (hs : 0 ≤ s) (hsu : s ≤ u) (i : Fin 2)
    (htail : Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0)) :
    (∫ t in Ioi u, timeVaryingPairExitDensity k c q s i t) =
      timeVaryingPairSurvival k c q s i u := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun t _ => timeVaryingPairExitCDF_hasDerivAt k c q hc hq s t i)
    (fun t ht => timeVaryingPairExitDensity_nonneg k c q hc hq hcn hqn hs
      (hsu.trans ht.le) i) (htail.const_sub 1)
  convert h using 1
  ring

theorem timeVaryingPairExitDensity_lintegral_tail (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    {s u : ℝ} (hs : 0 ≤ s) (hsu : s ≤ u) (i : Fin 2)
    (htail : Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0)) :
    (∫⁻ t in Ioi u, ENNReal.ofReal (timeVaryingPairExitDensity k c q s i t)) =
      ENNReal.ofReal (timeVaryingPairSurvival k c q s i u) := by
  have hi := (timeVaryingPairExitDensity_integrable k c q hc hq hcn hqn hs i htail).mono_set
    (Ioi_subset_Ioi hsu)
  rw [← ofReal_integral_eq_lintegral_ofReal hi]
  · rw [timeVaryingPairExitDensity_integral_tail k c q hc hq hcn hqn hs hsu i htail]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact timeVaryingPairExitDensity_nonneg k c q hc hq hcn hqn hs (hsu.trans ht.le) i

theorem timeVaryingPairExitLaw_tail (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    {s u : ℝ} (hs : 0 ≤ s) (hsu : s ≤ u) (i : Fin 2)
    (htail : Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0)) :
    timeVaryingPairExitLaw k c q s i (Ioi u) =
      ENNReal.ofReal (timeVaryingPairSurvival k c q s i u) := by
  rw [timeVaryingPairExitLaw, withDensity_apply _ measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi, inter_eq_left.mpr (Ioi_subset_Ioi hsu)]
  exact timeVaryingPairExitDensity_lintegral_tail k c q hc hq hcn hqn hs hsu i htail

theorem timeVaryingPairSurvival_pos (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (i : Fin 2) :
    0 < timeVaryingPairSurvival k c q s i t := by
  have h := finiteRowODE_mass_lower_integral
    (fun u => MarkovChain.Identifiability.pairGenerator k (c (s + u)) (q (s + u)))
    (fun u => timeVaryingPairTransition k c q s (s + u) i)
    (fun u => c (s + u)) (hc.comp (continuous_const.add continuous_id))
    (fun u _ j => inhomogeneousTransition_shift_hasDerivAt _
      (timeVaryingPairGenerator_continuous k c q hc hq) s u i j)
    (fun u hu j => timeVaryingPairTransition_nonneg k c q hc hq hqn hs
      (le_add_of_nonneg_right hu) i j)
    (fun u hu j => (timeVaryingPairGenerator_row_bounds k (hcn (s + u) (add_nonneg hs hu)) j).1)
    (sub_nonneg.mpr hst)
  have h' : Real.exp (-(∫ v in (0 : ℝ)..(t-s), c (s+v))) ≤
      timeVaryingPairSurvival k c q s i t := by
    simpa only [add_zero, add_sub_cancel, timeVaryingPairTransition_self k c q hc hq,
      Matrix.one_apply, Finset.sum_ite_eq, Finset.mem_univ, ite_true, one_mul,
      timeVaryingPairSurvival] using h
  exact (Real.exp_pos _).trans_le h'

theorem timeVaryingPairExitDensity_cocycle (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (s u t : ℝ) (i : Fin 2) :
    timeVaryingPairExitDensity k c q s i t =
      ∑ j, timeVaryingPairTransition k c q s u i j *
        timeVaryingPairExitDensity k c q u j t := by
  unfold timeVaryingPairExitDensity timeVaryingPairTransition
  rw [inhomogeneousTransition_cocycle _ (timeVaryingPairGenerator_continuous k c q hc hq) s u t]
  change (∑ j, inhomogeneousTransition
      (fun t => MarkovChain.Identifiability.pairGenerator k (c t) (q t)) s u i j *
    inhomogeneousTransition (fun t => MarkovChain.Identifiability.pairGenerator k (c t) (q t)) u t j
        0) * c t = _
  simp only [Finset.sum_mul, mul_assoc]

noncomputable def timeVaryingPairExitKernelDensity (k : ℕ) (c q : ℝ → ℝ)
    (i : Fin 2) (s : Ici (0 : ℝ)) (t : ℝ) : ℝ≥0∞ :=
  (Ioi (s : ℝ)).indicator
    (fun t => ENNReal.ofReal (timeVaryingPairExitDensity k c q s i t)) t

theorem timeVaryingPairExitKernelDensity_measurable (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (i : Fin 2) :
    Measurable (Function.uncurry (timeVaryingPairExitKernelDensity k c q i)) := by
  have hd : Measurable (fun p : Ici (0 : ℝ) × ℝ =>
      ENNReal.ofReal (timeVaryingPairExitDensity k c q p.1 i p.2)) :=
    ((timeVaryingPairExitDensity_continuous k c q hc hq i).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        continuous_snd)).measurable.ennreal_ofReal
  exact hd.indicator (measurableSet_lt (measurable_subtype_coe.comp measurable_fst) measurable_snd)

noncomputable def timeVaryingPairExitKernel (k : ℕ) (c q : ℝ → ℝ)
    (i : Fin 2) : Kernel (Ici (0 : ℝ)) ℝ :=
  (Kernel.const (Ici (0 : ℝ)) volume).withDensity (timeVaryingPairExitKernelDensity k c q i)

theorem timeVaryingPairExitKernel_apply (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (i : Fin 2) (s : Ici (0 : ℝ)) :
    timeVaryingPairExitKernel k c q i s = timeVaryingPairExitLaw k c q s i := by
  rw [timeVaryingPairExitKernel, Kernel.withDensity_apply _
    (timeVaryingPairExitKernelDensity_measurable k c q hc hq i), Kernel.const_apply]
  exact withDensity_indicator measurableSet_Ioi _

theorem timeVaryingPairExitKernel_markov (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t) (i : Fin 2)
    (htail : ∀ s, 0 ≤ s → Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0)) :
    IsMarkovKernel (timeVaryingPairExitKernel k c q i) := by
  constructor
  intro s
  rw [timeVaryingPairExitKernel_apply k c q hc hq]
  exact timeVaryingPairExitLaw_probability k c q hc hq hcn hqn s.property i (htail s s.property)

noncomputable def timeVaryingPairConditionalExitLaw (k : ℕ) (c q : ℝ → ℝ)
    (s : ℝ) (i : Fin 2) (u : ℝ) : Measure ℝ :=
  (ENNReal.ofReal (timeVaryingPairSurvival k c q s i u))⁻¹ •
    (timeVaryingPairExitLaw k c q s i).restrict (Ioi u)

theorem timeVaryingPairConditionalExitLaw_probability (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    {s u : ℝ} (hs : 0 ≤ s) (hsu : s ≤ u) (i : Fin 2)
    (htail : Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0)) :
    IsProbabilityMeasure (timeVaryingPairConditionalExitLaw k c q s i u) := by
  constructor
  rw [timeVaryingPairConditionalExitLaw, Measure.smul_apply,
    Measure.restrict_apply MeasurableSet.univ, univ_inter, smul_eq_mul,
    timeVaryingPairExitLaw_tail k c q hc hq hcn hqn hs hsu i htail]
  exact ENNReal.inv_mul_cancel
    (ne_of_gt (ENNReal.ofReal_pos.mpr (timeVaryingPairSurvival_pos k c q hc hq hcn hqn hs hsu i)))
    ENNReal.ofReal_ne_top

noncomputable def timeVaryingPairRemainingLaw (k : ℕ) (c q : ℝ → ℝ)
    (s : ℝ) (i : Fin 2) (u : ℝ) : Measure ℝ :=
  (timeVaryingPairConditionalExitLaw k c q s i u).map (fun t => t - u)

theorem timeVaryingPairRemainingLaw_probability (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    {s u : ℝ} (hs : 0 ≤ s) (hsu : s ≤ u) (i : Fin 2)
    (htail : Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0)) :
    IsProbabilityMeasure (timeVaryingPairRemainingLaw k c q s i u) := by
  let := timeVaryingPairConditionalExitLaw_probability k c q hc hq hcn hqn hs hsu i htail
  unfold timeVaryingPairRemainingLaw
  infer_instance

theorem timeVaryingPairRemainingLaw_tail (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    {s u v : ℝ} (hs : 0 ≤ s) (hsu : s ≤ u) (hv : 0 ≤ v) (i : Fin 2)
    (htail : Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0)) :
    timeVaryingPairRemainingLaw k c q s i u (Ioi v) =
      ENNReal.ofReal (timeVaryingPairSurvival k c q s i (u + v)) /
        ENNReal.ofReal (timeVaryingPairSurvival k c q s i u) := by
  have hpre : (fun t : ℝ => t - u) ⁻¹' Ioi v = Ioi (u + v) := by
    ext t
    simp only [mem_preimage, mem_Ioi]
    constructor <;> intro h <;> linarith
  rw [timeVaryingPairRemainingLaw,
    Measure.map_apply (f := fun t : ℝ => t - u) (by fun_prop) measurableSet_Ioi, hpre,
    timeVaryingPairConditionalExitLaw, Measure.smul_apply,
    Measure.restrict_apply measurableSet_Ioi,
    inter_eq_left.mpr (Ioi_subset_Ioi (le_add_of_nonneg_right hv)), smul_eq_mul,
    timeVaryingPairExitLaw_tail k c q hc hq hcn hqn hs
      (hsu.trans (le_add_of_nonneg_right hv)) i htail, div_eq_mul_inv, mul_comm]

theorem timeVaryingPair_conditional_weights_sum (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    {s u : ℝ} (hs : 0 ≤ s) (hsu : s ≤ u) (i : Fin 2) :
    (∑ j, timeVaryingPairTransition k c q s u i j /
      timeVaryingPairSurvival k c q s i u) = 1 := by
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (timeVaryingPairSurvival_pos k c q hc hq hcn hqn hs hsu i))

theorem timeVaryingPair_conditional_density_mixture (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (s u t : ℝ) (i : Fin 2) :
    timeVaryingPairExitDensity k c q s i t / timeVaryingPairSurvival k c q s i u =
      ∑ j, (timeVaryingPairTransition k c q s u i j / timeVaryingPairSurvival k c q s i u) *
        timeVaryingPairExitDensity k c q u j t := by
  rw [timeVaryingPairExitDensity_cocycle k c q hc hq s u t i, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem timeVaryingPairConditionalExitLaw_withDensity (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    {s u : ℝ} (hs : 0 ≤ s) (hsu : s ≤ u) (i : Fin 2) :
    timeVaryingPairConditionalExitLaw k c q s i u =
      (volume.restrict (Ioi u)).withDensity (fun t =>
        ENNReal.ofReal (timeVaryingPairExitDensity k c q s i t /
          timeVaryingPairSurvival k c q s i u)) := by
  have hf : Measurable (fun t => ENNReal.ofReal (timeVaryingPairExitDensity k c q s i t)) :=
    ((timeVaryingPairExitDensity_continuous k c q hc hq i).comp
      (continuous_const.prodMk continuous_id)).measurable.ennreal_ofReal
  rw [timeVaryingPairConditionalExitLaw, timeVaryingPairExitLaw,
    restrict_withDensity measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_left.mpr (Ioi_subset_Ioi hsu), ← withDensity_smul _ hf]
  congr 1
  funext t
  rw [ENNReal.ofReal_div_of_pos (timeVaryingPairSurvival_pos k c q hc hq hcn hqn hs hsu i)]
  simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem timeVaryingPair_conditional_weight_nonneg (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    {s u : ℝ} (hs : 0 ≤ s) (hsu : s ≤ u) (i j : Fin 2) :
    0 ≤ timeVaryingPairTransition k c q s u i j /
      timeVaryingPairSurvival k c q s i u :=
  div_nonneg (timeVaryingPairTransition_nonneg k c q hc hq hqn hs hsu i j)
    (timeVaryingPairSurvival_pos k c q hc hq hcn hqn hs hsu i).le

theorem timeVaryingPairRemainingLaw_positive (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    {s u : ℝ} (hs : 0 ≤ s) (hsu : s ≤ u) (i : Fin 2)
    (htail : Tendsto (timeVaryingPairSurvival k c q s i) atTop (𝓝 0)) :
    timeVaryingPairRemainingLaw k c q s i u (Ioi 0) = 1 := by
  rw [timeVaryingPairRemainingLaw_tail k c q hc hq hcn hqn hs hsu (le_refl 0) i htail,
    add_zero]
  exact ENNReal.div_self
    (ne_of_gt (ENNReal.ofReal_pos.mpr (timeVaryingPairSurvival_pos k c q hc hq hcn hqn hs hsu i)))
    ENNReal.ofReal_ne_top

end Rhone.Statistics.Identifiability
