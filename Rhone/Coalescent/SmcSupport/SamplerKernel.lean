/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcSupport.TrackedMeasurable
public import Rhone.Coalescent.SmcSupport.GoodMeasurable
public import Rhone.Coalescent.FiniteIntervalMaterialKernel

/-! # Markov kernel and process of the tracked sampler, preserving the good-state invariant -/
@[expose] public section
namespace Rhone.Coalescent.SmcSupport
open IntervalProcess MeasureTheory ProbabilityTheory

noncomputable def samplerKernel (mode : Mode) (R : ℝ) :
    Kernel TrackedState TrackedState :=
  (Kernel.id.prod (Kernel.const TrackedState noiseLaw)).map
    (fun p => trackedSampleStep mode R p.1 p.2)

instance samplerKernel_markov (mode : Mode) (R : ℝ) :
    IsMarkovKernel (samplerKernel mode R) := by
  unfold samplerKernel
  exact Kernel.IsMarkovKernel.map _ (trackedSampleStep_measurable mode R)

theorem samplerKernel_apply (mode : Mode) (R : ℝ) (z : TrackedState) :
    samplerKernel mode R z = noiseLaw.map (trackedSampleStep mode R z) := by
  rw [samplerKernel, Kernel.map_apply _ (trackedSampleStep_measurable mode R),
    Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (trackedSampleStep_measurable mode R) measurable_prodMk_left]
  rfl

noncomputable def samplerProcess (mode : Mode) (R : ℝ) :
    Rhone.MarkovChain.DiscreteProcess TrackedState := ⟨samplerKernel mode R⟩

theorem noiseLaw_interior : ∀ᵐ u ∂noiseLaw, ∀ i, 0 < u i ∧ u i < 1 := by
  have h : ∀ᵐ x ∂unitUniform, 0 < x ∧ x < 1 :=
    ae_restrict_mem measurableSet_Ioo
  apply Filter.eventually_all.mpr
  intro i
  exact (Measure.tendsto_eval_ae_ae
    (μ := fun _ : Fin 3 => unitUniform) (i := i)).eventually h

theorem samplerKernel_good (mode : Mode) (R : ℝ) (hR : 0 ≤ R)
    (z : TrackedState) (hz : Good z) :
    ∀ᵐ z' ∂samplerKernel mode R z, Good z' := by
  have _ := hR
  rw [samplerKernel_apply]
  apply (ae_map_iff
    ((trackedSampleStep_measurable mode R).comp measurable_prodMk_left).aemeasurable
    good_measurable).mpr
  exact noiseLaw_interior.mono (fun u hu => trackedSampleStep_good mode R z hz u
    (hu 0).1.le (hu 0).2 (hu 1).1.le (hu 1).2.le (hu 2).1 (hu 2).2)

end Rhone.Coalescent.SmcSupport
