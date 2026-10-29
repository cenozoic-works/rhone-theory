/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.Process
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Distributions.Poisson.Basic

/-!
# Muller's ratchet in a finite Wright-Fisher population

Source: haigh1978, eq. (1), p. 252; etheridge_etal2007, sec. 2, eq. (2.1). -/

@[expose] public section

namespace Rhone.MarkovChain.MullerRatchet

open MeasureTheory ProbabilityTheory Finset Filter
open scoped ENNReal NNReal Topology

variable {N : ℕ}

noncomputable def minLoad (x : Fin N → ℕ) : ℕ := ⨅ i, x i

theorem minLoad_le (x : Fin N → ℕ) (i : Fin N) : minLoad x ≤ x i :=
  ciInf_le (OrderBot.bddBelow _) i

theorem le_minLoad_iff [NeZero N] {m : ℕ} {x : Fin N → ℕ} : m ≤ minLoad x ↔ ∀ i, m ≤ x i :=
  haveI : Nonempty (Fin N) := ⟨0⟩
  le_ciInf_iff (OrderBot.bddBelow _)

theorem lt_minLoad_iff [NeZero N] {m : ℕ} {x : Fin N → ℕ} : m < minLoad x ↔ ∀ i, m < x i :=
  le_minLoad_iff (m := m + 1)

noncomputable def parentProb (s : ℝ) (x : Fin N → ℕ) (p : Fin N) : ℝ :=
  (1 - s) ^ x p / ∑ q, (1 - s) ^ x q

/-- Source: etheridge_etal2007, sec. 2, eq. (2.1). -/
theorem parentProb_nonneg {s : ℝ} (hs : s < 1) (x : Fin N → ℕ) (p : Fin N) :
    0 ≤ parentProb s x p := by
  have hpos : 0 < 1 - s := by linarith
  exact div_nonneg (pow_nonneg hpos.le _) (sum_nonneg fun q _ => pow_nonneg hpos.le _)

/-- Source: etheridge_etal2007, sec. 2, eq. (2.1). -/
theorem sum_parentProb [NeZero N] {s : ℝ} (hs : s < 1) (x : Fin N → ℕ) :
    ∑ p, parentProb s x p = 1 := by
  have hpos : 0 < 1 - s := by linarith
  have hsum : 0 < ∑ q : Fin N, (1 - s) ^ x q :=
    sum_pos (fun q _ => pow_pos hpos _) ⟨0, mem_univ _⟩
  simp only [parentProb]
  rw [← sum_div, div_self hsum.ne']

noncomputable def offspringLaw (s : ℝ) (U : ℝ≥0) (x : Fin N → ℕ) : Measure ℕ :=
  ∑ p, ENNReal.ofReal (parentProb s x p) • (poissonMeasure U).map (fun k => x p + k)

noncomputable def stepLaw (s : ℝ) (U : ℝ≥0) (x : Fin N → ℕ) : Measure (Fin N → ℕ) :=
  Measure.pi fun _ : Fin N => offspringLaw s U x

/-- Source: etheridge_etal2007, sec. 2, eq. (2.1). -/
theorem offspringLaw_apply (s : ℝ) (U : ℝ≥0) (x : Fin N → ℕ) (A : Set ℕ) :
    offspringLaw s U x A =
      ∑ p, ENNReal.ofReal (parentProb s x p) * poissonMeasure U ((fun k => x p + k) ⁻¹' A) := by
  simp [offspringLaw, Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]

/-- Source: etheridge_etal2007, sec. 2, eq. (2.1). -/
theorem isProbabilityMeasure_offspringLaw [NeZero N] {s : ℝ} (hs : s < 1) (U : ℝ≥0)
    (x : Fin N → ℕ) : IsProbabilityMeasure (offspringLaw s U x) := by
  refine ⟨?_⟩
  rw [offspringLaw_apply]
  simp only [Set.preimage_univ, measure_univ, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun p _ => parentProb_nonneg hs x p, sum_parentProb hs,
    ENNReal.ofReal_one]

/-- Source: etheridge_etal2007, sec. 2, eq. (2.1). -/
theorem isProbabilityMeasure_stepLaw [NeZero N] {s : ℝ} (hs : s < 1) (U : ℝ≥0)
    (x : Fin N → ℕ) : IsProbabilityMeasure (stepLaw s U x) := by
  have := isProbabilityMeasure_offspringLaw hs U x
  unfold stepLaw
  infer_instance

/-- Source: muller1964, p. 8; gordo_charlesworth2000, p. 1379; haigh1978, p. 251. -/
theorem minLoad_le_of_stepLaw_ne_zero [NeZero N] {s : ℝ} (hs : s < 1) (U : ℝ≥0)
    (x y : Fin N → ℕ) (h : stepLaw s U x {y} ≠ 0) : minLoad x ≤ minLoad y := by
  have := isProbabilityMeasure_offspringLaw hs U x
  by_contra hlt
  obtain ⟨i, hi⟩ : ∃ i, y i < minLoad x := by
    by_contra hall
    exact hlt (le_minLoad_iff.2 fun i => not_lt.1 fun hi => hall ⟨i, hi⟩)
  apply h
  rw [stepLaw, Measure.pi_singleton]
  refine prod_eq_zero (mem_univ i) ?_
  rw [offspringLaw_apply]
  refine sum_eq_zero fun p _ => ?_
  have hempty : (fun k => x p + k) ⁻¹' {y i} = ∅ := by
    ext k
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    have := minLoad_le x p
    omega
  rw [hempty, measure_empty, mul_zero]

/-- Source: muller1964, p. 8; haigh1978, p. 251. -/
theorem ae_minLoad_le [NeZero N] {s : ℝ} (hs : s < 1) (U : ℝ≥0) (x : Fin N → ℕ) :
    ∀ᵐ y ∂stepLaw s U x, minLoad x ≤ minLoad y := by
  rw [ae_iff, measure_null_iff_singleton (Set.to_countable _)]
  intro y hy
  by_contra hne
  exact hy (minLoad_le_of_stepLaw_ne_zero hs U x y hne)

theorem poissonMeasure_compl_zero (U : ℝ≥0) :
    poissonMeasure U {0}ᶜ = ENNReal.ofReal (1 - Real.exp (-(U : ℝ))) := by
  rw [prob_compl_eq_one_sub (MeasurableSet.singleton 0), poissonMeasure_singleton,
    ENNReal.ofReal_sub _ (Real.exp_pos _).le, ENNReal.ofReal_one]
  simp

theorem ofReal_le_offspringLaw_Ioi [NeZero N] {s : ℝ} (hs : s < 1) (U : ℝ≥0) (x : Fin N → ℕ) :
    ENNReal.ofReal (1 - Real.exp (-(U : ℝ))) ≤ offspringLaw s U x (Set.Ioi (minLoad x)) := by
  rw [offspringLaw_apply]
  calc ENNReal.ofReal (1 - Real.exp (-(U : ℝ)))
      = ∑ p, ENNReal.ofReal (parentProb s x p) * ENNReal.ofReal (1 - Real.exp (-(U : ℝ))) := by
        rw [← sum_mul, ← ENNReal.ofReal_sum_of_nonneg fun p _ => parentProb_nonneg hs x p,
          sum_parentProb hs, ENNReal.ofReal_one, one_mul]
    _ ≤ ∑ p, ENNReal.ofReal (parentProb s x p) *
          poissonMeasure U ((fun k => x p + k) ⁻¹' Set.Ioi (minLoad x)) := by
        refine sum_le_sum fun p _ => mul_le_mul_right ?_ _
        rw [← poissonMeasure_compl_zero]
        refine measure_mono fun k hk => ?_
        have hk0 : k ≠ 0 := hk
        have := minLoad_le x p
        simp only [Set.mem_preimage, Set.mem_Ioi]
        omega

theorem ofReal_le_stepLaw_click [NeZero N] {s : ℝ} (hs : s < 1) (U : ℝ≥0) (x : Fin N → ℕ) :
    ENNReal.ofReal ((1 - Real.exp (-(U : ℝ))) ^ N) ≤
      stepLaw s U x {y | minLoad x < minLoad y} := by
  have := isProbabilityMeasure_offspringLaw hs U x
  have hset : {y : Fin N → ℕ | minLoad x < minLoad y} =
      Set.pi Set.univ fun _ : Fin N => Set.Ioi (minLoad x) := by
    ext y
    simp [lt_minLoad_iff]
  have hnn : 0 ≤ 1 - Real.exp (-(U : ℝ)) :=
    sub_nonneg.2 (Real.exp_le_one_iff.2 (neg_nonpos.2 U.coe_nonneg))
  rw [hset, stepLaw, Measure.pi_pi, prod_const, card_univ, Fintype.card_fin,
    ENNReal.ofReal_pow hnn]
  exact pow_le_pow_left' (ofReal_le_offspringLaw_Ioi hs U x) N

theorem noClickBound_nonneg (N : ℕ) (U : ℝ≥0) : 0 ≤ 1 - (1 - Real.exp (-(U : ℝ))) ^ N := by
  have h0 : 0 ≤ 1 - Real.exp (-(U : ℝ)) :=
    sub_nonneg.2 (Real.exp_le_one_iff.2 (neg_nonpos.2 U.coe_nonneg))
  have h1 : 1 - Real.exp (-(U : ℝ)) ≤ 1 := sub_le_self _ (Real.exp_pos _).le
  exact sub_nonneg.2 (pow_le_one₀ h0 h1)

theorem stepLaw_noClick_le [NeZero N] {s : ℝ} (hs : s < 1) (U : ℝ≥0) (x : Fin N → ℕ) :
    stepLaw s U x {y | minLoad y ≤ minLoad x} ≤
      ENNReal.ofReal (1 - (1 - Real.exp (-(U : ℝ))) ^ N) := by
  have := isProbabilityMeasure_stepLaw hs U x
  have hset : {y : Fin N → ℕ | minLoad y ≤ minLoad x} = {y | minLoad x < minLoad y}ᶜ := by
    ext y
    simp
  have hp : 0 ≤ (1 - Real.exp (-(U : ℝ))) ^ N :=
    pow_nonneg (sub_nonneg.2 (Real.exp_le_one_iff.2 (neg_nonpos.2 U.coe_nonneg))) N
  rw [hset, prob_compl_eq_one_sub MeasurableSet.of_discrete, ENNReal.ofReal_sub _ hp,
    ENNReal.ofReal_one]
  exact tsub_le_tsub_left (ofReal_le_stepLaw_click hs U x) 1

noncomputable def kernel (s : ℝ) (U : ℝ≥0) : Kernel (Fin N → ℕ) (Fin N → ℕ) where
  toFun := stepLaw s U
  measurable' := Measurable.of_discrete

/-- Source: etheridge_etal2007, sec. 2, eq. (2.1). -/
theorem isMarkovKernel_kernel [NeZero N] {s : ℝ} (hs : s < 1) (U : ℝ≥0) :
    IsMarkovKernel (kernel (N := N) s U) :=
  ⟨fun x => isProbabilityMeasure_stepLaw hs U x⟩

noncomputable def process [NeZero N] (s : ℝ) (hs : s < 1) (U : ℝ≥0) :
    Rhone.MarkovChain.DiscreteProcess (Fin N → ℕ) :=
  haveI := isMarkovKernel_kernel (N := N) hs U
  ⟨kernel s U⟩

/-- Source: etheridge_etal2007, sec. 2, eq. (2.1). -/
theorem process_step [NeZero N] {s : ℝ} (hs : s < 1) (U : ℝ≥0) (x : Fin N → ℕ) :
    (process s hs U).step x = stepLaw s U x := rfl

/-- Source: muller1964, p. 8; haigh1978, p. 251. -/
theorem pathLaw_minLoad_lt [NeZero N] {s : ℝ} (hs : s < 1) (U : ℝ≥0) (x : Fin N → ℕ) (t : ℕ) :
    (process s hs U).pathLaw x {ω | minLoad (ω t) < minLoad x} = 0 := by
  have key : ((process s hs U).pathLaw x).map (fun ω => ω t) {y | minLoad y < minLoad x} = 0 := by
    induction t with
    | zero =>
      rw [Rhone.MarkovChain.DiscreteProcess.map_eval_zero,
        Measure.dirac_apply' _ MeasurableSet.of_discrete]
      simp
    | succ t ih =>
      rw [Rhone.MarkovChain.DiscreteProcess.map_eval_succ,
        Measure.bind_apply MeasurableSet.of_discrete (Kernel.aemeasurable _)]
      have hae : ∀ᵐ y ∂((process s hs U).pathLaw x).map (fun ω => ω t),
          (process s hs U).step y {y' | minLoad y' < minLoad x} = 0 := by
        filter_upwards [measure_eq_zero_iff_ae_notMem.1 ih] with y hy
        have hyx : minLoad x ≤ minLoad y := not_lt.1 hy
        refine measure_mono_null (fun y' hy' => ?_)
          (ae_iff.1 (ae_minLoad_le hs U y))
        exact not_le.2 (lt_of_lt_of_le hy' hyx)
      rw [lintegral_congr_ae hae, lintegral_zero]
  rwa [Measure.map_apply (measurable_pi_apply t) MeasurableSet.of_discrete] at key

/-- Source: gordo_charlesworth2000, p. 1379. -/
theorem pathLaw_minLoad_le [NeZero N] {s : ℝ} (hs : s < 1) (U : ℝ≥0) (x : Fin N → ℕ) (t : ℕ) :
    (process s hs U).pathLaw x {ω | minLoad (ω t) ≤ minLoad x} ≤
      ENNReal.ofReal ((1 - (1 - Real.exp (-(U : ℝ))) ^ N) ^ t) := by
  have key : ((process s hs U).pathLaw x).map (fun ω => ω t) {y | minLoad y ≤ minLoad x} ≤
      ENNReal.ofReal ((1 - (1 - Real.exp (-(U : ℝ))) ^ N) ^ t) := by
    induction t with
    | zero => simpa using prob_le_one
    | succ t ih =>
      have hlt : ((process s hs U).pathLaw x).map (fun ω => ω t)
          {y | minLoad y < minLoad x} = 0 := by
        rw [Measure.map_apply (measurable_pi_apply t) MeasurableSet.of_discrete]
        exact pathLaw_minLoad_lt hs U x t
      rw [Rhone.MarkovChain.DiscreteProcess.map_eval_succ,
        Measure.bind_apply MeasurableSet.of_discrete (Kernel.aemeasurable _)]
      have hae : ∀ᵐ y ∂((process s hs U).pathLaw x).map (fun ω => ω t),
          (process s hs U).step y {y' | minLoad y' ≤ minLoad x} ≤
            Set.indicator {y | minLoad y ≤ minLoad x}
              (fun _ => ENNReal.ofReal (1 - (1 - Real.exp (-(U : ℝ))) ^ N)) y := by
        filter_upwards [measure_eq_zero_iff_ae_notMem.1 hlt] with y hy
        have hyx : minLoad x ≤ minLoad y := not_lt.1 hy
        by_cases hmem : minLoad y ≤ minLoad x
        · rw [Set.indicator_of_mem (by exact hmem)]
          have heq : minLoad y = minLoad x := le_antisymm hmem hyx
          rw [← heq]
          exact stepLaw_noClick_le hs U y
        · rw [Set.indicator_of_notMem (by exact hmem)]
          refine le_of_eq (measure_mono_null (fun y' hy' => ?_)
            (ae_iff.1 (ae_minLoad_le hs U y)))
          exact not_le.2 (lt_of_le_of_lt hy' (not_le.1 hmem))
      refine (lintegral_mono_ae hae).trans ?_
      rw [lintegral_indicator_const MeasurableSet.of_discrete, pow_succ,
        ENNReal.ofReal_mul (pow_nonneg (noClickBound_nonneg N U) t), mul_comm]
      gcongr
  rwa [Measure.map_apply (measurable_pi_apply t) MeasurableSet.of_discrete] at key

theorem noClickBound_lt_one (N : ℕ) {U : ℝ≥0} (hU : 0 < U) :
    1 - (1 - Real.exp (-(U : ℝ))) ^ N < 1 := by
  have hU' : (0 : ℝ) < U := by exact_mod_cast hU
  have hexp : Real.exp (-(U : ℝ)) < Real.exp 0 := Real.exp_lt_exp.2 (by linarith)
  rw [Real.exp_zero] at hexp
  have h : 0 < 1 - Real.exp (-(U : ℝ)) := sub_pos.2 hexp
  linarith [pow_pos h N]

theorem ae_exists_minLoad_lt [NeZero N] {s : ℝ} (hs : s < 1) {U : ℝ≥0} (hU : 0 < U)
    (x : Fin N → ℕ) :
    ∀ᵐ ω ∂(process s hs U).pathLaw x, ∃ t, minLoad x < minLoad (ω t) := by
  rw [ae_iff]
  have htend : Tendsto (fun t : ℕ => ENNReal.ofReal ((1 - (1 - Real.exp (-(U : ℝ))) ^ N) ^ t))
      atTop (𝓝 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one (noClickBound_nonneg N U)
      (noClickBound_lt_one N hU)
    have h2 := (ENNReal.continuous_ofReal.tendsto 0).comp h
    rw [ENNReal.ofReal_zero] at h2
    exact h2
  refine le_antisymm (ge_of_tendsto' htend fun t => ?_) zero_le
  refine (measure_mono fun ω hω => ?_).trans (pathLaw_minLoad_le hs U x t)
  simp only [Set.mem_ofPred_eq, not_exists, not_lt] at hω ⊢
  exact hω t

open Classical in
noncomputable def clickTime (m : ℕ) (ω : ℕ → Fin N → ℕ) : ℕ∞ :=
  if h : ∃ t, m < minLoad (ω t) then (Nat.find h : ℕ∞) else ⊤

theorem clickTime_le_tsum (m : ℕ) (ω : ℕ → Fin N → ℕ) :
    (clickTime m ω : ℝ≥0∞) ≤
      ∑' t, Set.indicator {ω' : ℕ → Fin N → ℕ | minLoad (ω' t) ≤ m} (fun _ => (1 : ℝ≥0∞)) ω := by
  classical
  unfold clickTime
  split_ifs with h
  · have hlt : ∀ t ∈ range (Nat.find h),
        Set.indicator {ω' : ℕ → Fin N → ℕ | minLoad (ω' t) ≤ m} (fun _ => (1 : ℝ≥0∞)) ω = 1 :=
      fun t ht => Set.indicator_of_mem
        (show ω ∈ {ω' : ℕ → Fin N → ℕ | minLoad (ω' t) ≤ m} from
          not_lt.1 (Nat.find_min h (mem_range.1 ht))) _
    calc ((Nat.find h : ℕ∞) : ℝ≥0∞) = ∑ t ∈ range (Nat.find h), (1 : ℝ≥0∞) := by simp
      _ = ∑ t ∈ range (Nat.find h),
            Set.indicator {ω' : ℕ → Fin N → ℕ | minLoad (ω' t) ≤ m} (fun _ => (1 : ℝ≥0∞)) ω :=
          (sum_congr rfl hlt).symm
      _ ≤ _ := ENNReal.sum_le_tsum _
  · have hall : ∀ t, minLoad (ω t) ≤ m := fun t => not_lt.1 fun ht => h ⟨t, ht⟩
    have hone : ∀ t,
        Set.indicator {ω' : ℕ → Fin N → ℕ | minLoad (ω' t) ≤ m} (fun _ => (1 : ℝ≥0∞)) ω = 1 :=
      fun t => Set.indicator_of_mem
        (show ω ∈ {ω' : ℕ → Fin N → ℕ | minLoad (ω' t) ≤ m} from hall t) _
    simp only [hone]
    rw [ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero]
    exact le_top

theorem lintegral_clickTime_le [NeZero N] {s : ℝ} (hs : s < 1) (U : ℝ≥0) (x : Fin N → ℕ) :
    ∫⁻ ω, (clickTime (minLoad x) ω : ℝ≥0∞) ∂(process s hs U).pathLaw x ≤
      (ENNReal.ofReal ((1 - Real.exp (-(U : ℝ))) ^ N))⁻¹ := by
  have hmeas : ∀ t, MeasurableSet {ω : ℕ → Fin N → ℕ | minLoad (ω t) ≤ minLoad x} := fun t =>
    (MeasurableSet.of_discrete (s := {y : Fin N → ℕ | minLoad y ≤ minLoad x})).preimage
      (measurable_pi_apply t)
  calc ∫⁻ ω, (clickTime (minLoad x) ω : ℝ≥0∞) ∂(process s hs U).pathLaw x
      ≤ ∫⁻ ω, ∑' t, Set.indicator {ω' : ℕ → Fin N → ℕ | minLoad (ω' t) ≤ minLoad x}
          (fun _ => (1 : ℝ≥0∞)) ω ∂(process s hs U).pathLaw x :=
        lintegral_mono (clickTime_le_tsum _)
    _ = ∑' t, ∫⁻ ω, Set.indicator {ω' : ℕ → Fin N → ℕ | minLoad (ω' t) ≤ minLoad x}
          (fun _ => (1 : ℝ≥0∞)) ω ∂(process s hs U).pathLaw x :=
        lintegral_tsum fun t => (measurable_const.indicator (hmeas t)).aemeasurable
    _ = ∑' t, (process s hs U).pathLaw x {ω | minLoad (ω t) ≤ minLoad x} := by
        refine tsum_congr fun t => ?_
        rw [lintegral_indicator_const (hmeas t), one_mul]
    _ ≤ ∑' t : ℕ, ENNReal.ofReal (1 - (1 - Real.exp (-(U : ℝ))) ^ N) ^ t := by
        refine ENNReal.tsum_le_tsum fun t => ?_
        rw [← ENNReal.ofReal_pow (noClickBound_nonneg N U)]
        exact pathLaw_minLoad_le hs U x t
    _ = (1 - ENNReal.ofReal (1 - (1 - Real.exp (-(U : ℝ))) ^ N))⁻¹ := ENNReal.tsum_geometric _
    _ = (ENNReal.ofReal ((1 - Real.exp (-(U : ℝ))) ^ N))⁻¹ := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (noClickBound_nonneg N U)]
        congr 2
        ring

private theorem map_eval_succ_le [NeZero N] {s : ℝ} (hs : s < 1) (U : ℝ≥0) (x : Fin N → ℕ)
    (t K : ℕ) :
    ((process s hs U).pathLaw x).map (fun ω => ω (t + 1)) {y | minLoad y ≤ K} ≤
      ENNReal.ofReal (1 - (1 - Real.exp (-(U : ℝ))) ^ N) *
          ((process s hs U).pathLaw x).map (fun ω => ω t) {y | minLoad y ≤ K} +
        ((process s hs U).pathLaw x).map (fun ω => ω t) {y | minLoad y < K} := by
  rw [Rhone.MarkovChain.DiscreteProcess.map_eval_succ,
    Measure.bind_apply MeasurableSet.of_discrete (Kernel.aemeasurable _)]
  have hpt : ∀ y, (process s hs U).step y {y' | minLoad y' ≤ K} ≤
      Set.indicator {y : Fin N → ℕ | minLoad y ≤ K}
          (fun _ => ENNReal.ofReal (1 - (1 - Real.exp (-(U : ℝ))) ^ N)) y +
        Set.indicator {y : Fin N → ℕ | minLoad y < K} (fun _ => (1 : ℝ≥0∞)) y := by
    intro y
    rcases lt_trichotomy (minLoad y) K with h | h | h
    · rw [Set.indicator_of_mem (show y ∈ {y : Fin N → ℕ | minLoad y < K} from h)]
      exact prob_le_one.trans le_add_self
    · rw [Set.indicator_of_mem (show y ∈ {y : Fin N → ℕ | minLoad y ≤ K} from h.le),
        Set.indicator_of_notMem (show y ∉ {y : Fin N → ℕ | minLoad y < K} from h.not_lt),
        add_zero, ← h]
      exact stepLaw_noClick_le hs U y
    · have hzero : (process s hs U).step y {y' | minLoad y' ≤ K} = 0 :=
        measure_mono_null (fun y' hy' => not_le.2 (lt_of_le_of_lt hy' h))
          (ae_iff.1 (ae_minLoad_le hs U y))
      rw [hzero]
      exact zero_le
  refine (lintegral_mono hpt).trans_eq ?_
  rw [lintegral_add_left (measurable_const.indicator MeasurableSet.of_discrete),
    lintegral_indicator_const MeasurableSet.of_discrete,
    lintegral_indicator_const MeasurableSet.of_discrete, one_mul]

private theorem map_eval_succ_le_self [NeZero N] {s : ℝ} (hs : s < 1) (U : ℝ≥0) (x : Fin N → ℕ)
    (t K : ℕ) :
    ((process s hs U).pathLaw x).map (fun ω => ω (t + 1)) {y | minLoad y ≤ K} ≤
      ((process s hs U).pathLaw x).map (fun ω => ω t) {y | minLoad y ≤ K} := by
  rw [Rhone.MarkovChain.DiscreteProcess.map_eval_succ,
    Measure.bind_apply MeasurableSet.of_discrete (Kernel.aemeasurable _)]
  have hpt : ∀ y, (process s hs U).step y {y' | minLoad y' ≤ K} ≤
      Set.indicator {y : Fin N → ℕ | minLoad y ≤ K} (fun _ => (1 : ℝ≥0∞)) y := by
    intro y
    by_cases h : minLoad y ≤ K
    · rw [Set.indicator_of_mem (show y ∈ {y : Fin N → ℕ | minLoad y ≤ K} from h)]
      exact prob_le_one
    · have hzero : (process s hs U).step y {y' | minLoad y' ≤ K} = 0 :=
        measure_mono_null (fun y' hy' => not_le.2 (lt_of_le_of_lt hy' (not_le.1 h)))
          (ae_iff.1 (ae_minLoad_le hs U y))
      rw [hzero]
      exact zero_le
  refine (lintegral_mono hpt).trans_eq ?_
  rw [lintegral_indicator_const MeasurableSet.of_discrete, one_mul]

private theorem tendsto_map_eval_minLoad_lt [NeZero N] {s : ℝ} (hs : s < 1) {U : ℝ≥0}
    (hU : 0 < U) (x : Fin N → ℕ) (K : ℕ) :
    Tendsto (fun t => ((process s hs U).pathLaw x).map (fun ω => ω t) {y | minLoad y < K})
      atTop (𝓝 0) := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hset : {y : Fin N → ℕ | minLoad y < K + 1} = {y | minLoad y ≤ K} := by
      ext y
      exact Nat.lt_succ_iff
    rw [hset]
    set a : ℕ → ℝ≥0∞ := fun t =>
      ((process s hs U).pathLaw x).map (fun ω => ω t) {y | minLoad y ≤ K} with ha
    set q : ℝ := 1 - (1 - Real.exp (-(U : ℝ))) ^ N with hq
    have hanti : Antitone a := antitone_nat_of_succ_le fun t => map_eval_succ_le_self hs U x t K
    have hlim : Tendsto a atTop (𝓝 (⨅ t, a t)) := tendsto_atTop_iInf hanti
    have hlim1 : Tendsto (fun t => a (t + 1)) atTop (𝓝 (⨅ t, a t)) :=
      hlim.comp (tendsto_add_atTop_nat 1)
    have hrhs : Tendsto (fun t => ENNReal.ofReal q * a t +
        ((process s hs U).pathLaw x).map (fun ω => ω t) {y | minLoad y < K}) atTop
        (𝓝 (ENNReal.ofReal q * (⨅ t, a t) + 0)) :=
      (ENNReal.Tendsto.const_mul hlim (Or.inr ENNReal.ofReal_ne_top)).add ih
    have hle : (⨅ t, a t) ≤ ENNReal.ofReal q * (⨅ t, a t) + 0 :=
      le_of_tendsto_of_tendsto' hlim1 hrhs fun t => map_eval_succ_le hs U x t K
    have hfin : (⨅ t, a t) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
      ((iInf_le a 0).trans prob_le_one)
    have hzero : (⨅ t, a t) = 0 := by
      rw [add_zero] at hle
      have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hle
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (noClickBound_nonneg N U)] at hreal
      have hq1 : q < 1 := noClickBound_lt_one N hU
      have hnn : 0 ≤ (⨅ t, a t).toReal := ENNReal.toReal_nonneg
      have h0 : (⨅ t, a t).toReal = 0 := by nlinarith
      exact ((ENNReal.toReal_eq_zero_iff _).1 h0).resolve_right hfin
    rw [hzero] at hlim
    exact hlim

theorem tendsto_pathLaw_minLoad_le [NeZero N] {s : ℝ} (hs : s < 1) {U : ℝ≥0} (hU : 0 < U)
    (x : Fin N → ℕ) (K : ℕ) :
    Tendsto (fun t => (process s hs U).pathLaw x {ω | minLoad (ω t) ≤ K}) atTop (𝓝 0) := by
  have h := tendsto_map_eval_minLoad_lt hs hU x (K + 1)
  refine h.congr fun t => ?_
  rw [Measure.map_apply (measurable_pi_apply t) MeasurableSet.of_discrete]
  congr 1
  ext ω
  exact Nat.lt_succ_iff

/-- Source: muller1964, p. 8; haigh1978, p. 251. -/
theorem ae_minLoad_le_succ [NeZero N] {s : ℝ} (hs : s < 1) (U : ℝ≥0) (x : Fin N → ℕ) :
    ∀ᵐ ω ∂(process s hs U).pathLaw x, ∀ n, minLoad (ω n) ≤ minLoad (ω (n + 1)) := by
  rw [ae_all_iff]
  intro n
  rw [ae_iff]
  have hset : {ω : ℕ → Fin N → ℕ | ¬ minLoad (ω n) ≤ minLoad (ω (n + 1))} =
      ⋃ m : ℕ, ({ω | minLoad (ω n) = m} ∩ {ω | minLoad (ω (n + 1)) < m}) := by
    ext ω
    simp
  rw [hset, measure_iUnion_null_iff]
  intro m
  have hBpi : MeasurableSet[Filtration.piLE (X := fun _ : ℕ => Fin N → ℕ) n]
      {ω : ℕ → Fin N → ℕ | minLoad (ω n) = m} :=
    (Rhone.MarkovChain.DiscreteProcess.measurable_eval_piLE (S := Fin N → ℕ) n)
      (MeasurableSet.of_discrete (s := {y : Fin N → ℕ | minLoad y = m}))
  have hE : MeasurableSet {ω : ℕ → Fin N → ℕ | minLoad (ω (n + 1)) < m} :=
    (MeasurableSet.of_discrete (s := {y : Fin N → ℕ | minLoad y < m})).preimage
      (measurable_pi_apply (n + 1))
  set g : (Fin N → ℕ) → ℝ := Set.indicator {y | minLoad y < m} (fun _ => 1) with hg
  have hM : ∀ y, |g y| ≤ 1 := by
    intro y
    by_cases h : minLoad y < m <;> simp [hg, h]
  have hmark := (process s hs U).setIntegral_eval_succ x n (Measurable.of_discrete (f := g)) hM
    hBpi
  have hlhs : ∫ ω in {ω : ℕ → Fin N → ℕ | minLoad (ω n) = m}, g (ω (n + 1))
      ∂(process s hs U).pathLaw x =
      ((process s hs U).pathLaw x).real
        ({ω | minLoad (ω n) = m} ∩ {ω | minLoad (ω (n + 1)) < m}) := by
    have hfun : (fun ω : ℕ → Fin N → ℕ => g (ω (n + 1))) =
        Set.indicator {ω : ℕ → Fin N → ℕ | minLoad (ω (n + 1)) < m} (fun _ => (1 : ℝ)) := by
      ext ω
      rfl
    rw [hfun, setIntegral_indicator hE, setIntegral_const, smul_eq_mul, mul_one]
  have hrhs : ∫ ω in {ω : ℕ → Fin N → ℕ | minLoad (ω n) = m},
      ∫ y, g y ∂(process s hs U).step (ω n) ∂(process s hs U).pathLaw x = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun ω hω => ?_
    have hm : minLoad (ω n) = m := hω
    have hzero : (process s hs U).step (ω n) {y | minLoad y < m} = 0 := by
      rw [← hm]
      exact measure_mono_null (fun y' hy' => not_le.2 hy') (ae_iff.1 (ae_minLoad_le hs U (ω n)))
    rw [hg, integral_indicator_const _ MeasurableSet.of_discrete, measureReal_def, hzero]
    simp
  rw [hlhs, hrhs] at hmark
  exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1 hmark

/-- Source: muller1964, pp. 2, 8; gordo_charlesworth2000, p. 1379; haigh1978, p. 251. -/
theorem ae_tendsto_minLoad_atTop [NeZero N] {s : ℝ} (hs : s < 1) {U : ℝ≥0} (hU : 0 < U)
    (x : Fin N → ℕ) :
    ∀ᵐ ω ∂(process s hs U).pathLaw x, Tendsto (fun t => minLoad (ω t)) atTop atTop := by
  have hlevel : ∀ᵐ ω ∂(process s hs U).pathLaw x, ∀ K, ∃ t, K < minLoad (ω t) := by
    rw [ae_all_iff]
    intro K
    rw [ae_iff]
    refine le_antisymm (ge_of_tendsto' (tendsto_pathLaw_minLoad_le hs hU x K) fun t => ?_)
      zero_le
    refine measure_mono fun ω hω => ?_
    simp only [Set.mem_ofPred_eq, not_exists, not_lt] at hω ⊢
    exact hω t
  filter_upwards [hlevel, ae_minLoad_le_succ hs U x] with ω hω hmono
  exact tendsto_atTop_atTop_of_monotone (monotone_nat_of_le_succ hmono) fun K =>
    (hω K).imp fun t ht => ht.le

end Rhone.MarkovChain.MullerRatchet
