/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcSupport.SampledBarrier
public import Rhone.Coalescent.SmcSupport.PathSupport
public import Mathlib.Probability.Kernel.MeasurableIntegral
public import Mathlib.MeasureTheory.Measure.Continuity

/-! # The barrier inequality bounds the probability of a second split along sampler paths -/
@[expose] public section
namespace Rhone.Coalescent.SmcSupport
open IntervalProcess SmcBound MeasureTheory ProbabilityTheory

theorem barrier_expectation_le (mode : Mode) (R : ℝ) (hR : 0 ≤ R)
    (n : ℕ) (hn : 0 < n) (k : ℕ) :
    (∫ ω, barrier R (ω k) ∂(samplerProcess mode R).pathLaw (trackedInitial n)) ≤
      doubleBound R (n - 1) := by
  let P := samplerProcess mode R
  let x := trackedInitial n
  have hb (y : TrackedState) : |barrier R y| ≤ 1 := by
    rw [abs_of_nonneg (barrier_bounds R hR y).1]
    exact (barrier_bounds R hR y).2
  have hi (j : ℕ) : Integrable (fun ω => barrier R (ω j)) (P.pathLaw x) :=
    Integrable.of_bound ((barrier_measurable R).comp
      (measurable_pi_apply j)).aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun ω => hb (ω j)))
  induction k with
  | zero =>
    rw [← integral_map (measurable_pi_apply 0).aemeasurable
      (barrier_measurable R).aestronglyMeasurable, P.map_eval_zero]
    rw [integral_dirac' _ _ (barrier_measurable R).stronglyMeasurable]
    exact le_rfl
  | succ k ih =>
    have he := P.setIntegral_eval_succ x k (barrier_measurable R) hb
      (B := Set.univ) MeasurableSet.univ
    simp only [Measure.restrict_univ] at he
    rw [he]
    have hkernel : StronglyMeasurable
        (fun z => ∫ y, barrier R y ∂P.step z) :=
      (barrier_measurable R).stronglyMeasurable.integral_kernel
    have hbound (z : TrackedState) : |∫ y, barrier R y ∂P.step z| ≤ 1 := by
      have h := norm_integral_le_of_norm_le_const
        (μ := P.step z) (f := barrier R) (C := (1 : ℝ))
        (Filter.Eventually.of_forall (fun y => by simpa only [Real.norm_eq_abs] using hb y))
      simpa only [Real.norm_eq_abs, measureReal_def, measure_univ,
        ENNReal.toReal_one, mul_one] using h
    have hint : Integrable (fun ω => ∫ y, barrier R y ∂P.step (ω k)) (P.pathLaw x) :=
      Integrable.of_bound (hkernel.comp_measurable
        (measurable_pi_apply k)).aestronglyMeasurable 1
        (Filter.Eventually.of_forall (fun ω => hbound (ω k)))
    refine (integral_mono_ae hint (hi k) ?_).trans ih
    exact (samplerProcess_good mode R hR n hn k).mono
      (fun ω hgood => barrier_step_le mode R hR (ω k) hgood)

private theorem process_absorbing {S : Type*} [MeasurableSpace S]
    (P : Rhone.MarkovChain.DiscreteProcess S) (A : Set S) (hA : MeasurableSet A)
    (hstep : ∀ z ∈ A, ∀ᵐ y ∂P.step z, y ∈ A) (x : S) :
    ∀ᵐ ω ∂P.pathLaw x, ∀ k, ω k ∈ A → ω (k + 1) ∈ A := by
  classical
  apply ae_all_iff.mpr
  intro k
  let g : S → ℝ := Aᶜ.indicator (fun _ => 1)
  have hg : Measurable g := measurable_const.indicator hA.compl
  have hb (z : S) : |g z| ≤ 1 := by
    by_cases hz : z ∈ A <;> simp [g, hz]
  let B : Set (ℕ → S) := {ω | ω k ∈ A}
  have hB : MeasurableSet B := hA.preimage (measurable_pi_apply k)
  have hBF : MeasurableSet[Filtration.piLE (X := fun _ : ℕ => S) k] B :=
    hA.preimage (Rhone.MarkovChain.DiscreteProcess.measurable_eval_piLE k)
  have he := P.setIntegral_eval_succ x k hg hb hBF
  have hr : (∫ ω in B, ∫ y, g y ∂P.step (ω k) ∂P.pathLaw x) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem hB] with ω hω
    apply integral_eq_zero_of_ae
    exact (hstep (ω k) hω).mono (fun y hy => by simp [g, hy])
  rw [hr] at he
  have hi : Integrable (fun ω => g (ω (k + 1))) ((P.pathLaw x).restrict B) :=
    Integrable.of_bound (hg.comp (measurable_pi_apply _)).aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun ω => hb _))
  have hnon : 0 ≤ (fun ω : ℕ → S => g (ω (k + 1))) := by
    intro ω
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hz := (integral_eq_zero_iff_of_nonneg hnon hi).mp he
  have hz' : ∀ᵐ ω ∂P.pathLaw x, ω ∈ B → g (ω (k + 1)) = 0 :=
    (ae_restrict_iff' hB).mp hz
  filter_upwards [hz'] with ω hω hk
  have hv := hω hk
  by_contra hn
  simp [g, hn] at hv

theorem second_split_by_le (mode : Mode) (R : ℝ) (hR : 0 ≤ R)
    (n : ℕ) (hn : 0 < n) (k : ℕ) :
    ((samplerProcess mode R).pathLaw (trackedInitial n)).real
      {ω | ∃ j ≤ k, (ω j).2.1 = .two} ≤ doubleBound R (n - 1) := by
  classical
  let P := samplerProcess mode R
  let x := trackedInitial n
  let A : Set TrackedState := {z | z.2.1 = .two}
  have hA : MeasurableSet A :=
    measurableSet_eq_fun measurable_snd.fst measurable_const
  have hstep : ∀ z ∈ A, ∀ᵐ y ∂P.step z, y ∈ A := by
    intro z hz
    change ∀ᵐ y ∂samplerKernel mode R z, y.2.1 = .two
    rw [samplerKernel_apply]
    apply (ae_map_iff
      (show Measurable (trackedSampleStep mode R z) from
        (trackedSampleStep_measurable mode R).comp
          (measurable_const.prodMk measurable_id)).aemeasurable hA).mpr
    exact Filter.Eventually.of_forall (fun u => trackedSampleStep_two mode R z hz u)
  have ha := process_absorbing P A hA hstep x
  have he : {ω : ℕ → TrackedState | ∃ j ≤ k, (ω j).2.1 = .two} =ᵐ[P.pathLaw x]
      {ω | (ω k).2.1 = .two} := by
    filter_upwards [ha] with ω hω
    apply propext
    constructor
    · rintro ⟨j, hj, hphase⟩
      have hstay : ∀ l, j ≤ l → (ω l).2.1 = .two := by
        intro l hl
        induction l, hl using Nat.le_induction with
        | base => exact hphase
        | succ l hl ih => exact hω l ih
      exact hstay k hj
    · intro hk
      exact ⟨k, le_rfl, hk⟩
  rw [measureReal_congr he]
  let B : Set (ℕ → TrackedState) := {ω | (ω k).2.1 = .two}
  have hB : MeasurableSet B := hA.preimage (measurable_pi_apply k)
  have hb (ω : ℕ → TrackedState) : |barrier R (ω k)| ≤ 1 := by
    rw [abs_of_nonneg (barrier_bounds R hR (ω k)).1]
    exact (barrier_bounds R hR (ω k)).2
  have hi : Integrable (fun ω => barrier R (ω k)) (P.pathLaw x) :=
    Integrable.of_bound ((barrier_measurable R).comp
      (measurable_pi_apply k)).aestronglyMeasurable 1
      (Filter.Eventually.of_forall hb)
  have hind : Integrable (B.indicator (fun _ => (1 : ℝ))) (P.pathLaw x) :=
    (integrable_const 1).indicator hB
  have hle : (∫ ω, B.indicator (fun _ => (1 : ℝ)) ω ∂P.pathLaw x) ≤
      ∫ ω, barrier R (ω k) ∂P.pathLaw x := by
    apply integral_mono hind hi
    intro ω
    simpa only [B, Set.indicator, Set.mem_ofPred_eq] using barrier_flag R hR (ω k)
  rw [integral_indicator_const 1 hB, smul_eq_mul, mul_one] at hle
  exact hle.trans (barrier_expectation_le mode R hR n hn k)

theorem ever_second_split_le (mode : Mode) (R : ℝ) (hR : 0 ≤ R)
    (n : ℕ) (hn : 0 < n) :
    ((samplerProcess mode R).pathLaw (trackedInitial n)).real
      {ω | ∃ k, (ω k).2.1 = .two} ≤ doubleBound R (n - 1) := by
  let μ := (samplerProcess mode R).pathLaw (trackedInitial n)
  let E : ℕ → Set (ℕ → TrackedState) := fun k => {ω | ∃ j ≤ k, (ω j).2.1 = .two}
  have hmono : Monotone E := by
    intro k l hkl ω hω
    obtain ⟨j, hj, hp⟩ := hω
    exact ⟨j, hj.trans hkl, hp⟩
  have he : {ω : ℕ → TrackedState | ∃ k, (ω k).2.1 = .two} = ⋃ k, E k := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, E]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, k, le_rfl, hk⟩
    · rintro ⟨k, j, _, hj⟩
      exact ⟨j, hj⟩
  have hC := doubleBound_nonneg R hR (n - 1)
  apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _) hC).mp
  rw [he, hmono.measure_iUnion]
  apply iSup_le
  intro k
  exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ (E k)) hC).mpr
    (second_split_by_le mode R hR n hn k)

end Rhone.Coalescent.SmcSupport
