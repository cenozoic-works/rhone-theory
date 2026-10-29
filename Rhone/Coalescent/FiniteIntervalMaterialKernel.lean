/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.Process
public import Rhone.Coalescent.FiniteIntervalMaterialSamplerMeas
public import Mathlib.MeasureTheory.Constructions.Pi

/-! # The concrete finite-interval marked sampler as a Core discrete process -/
@[expose] public section

namespace Rhone.Coalescent.IntervalProcess
open MeasureTheory ProbabilityTheory

abbrev AugmentedState := State × EventRecord

noncomputable def noiseLaw : Measure Noise := Measure.pi (fun _ : Fin 3 => unitUniform)

instance noiseLaw_probability : IsProbabilityMeasure noiseLaw := by
  unfold noiseLaw
  infer_instance

noncomputable def augmentedStep (mode : Mode) (R : ℝ) :
    AugmentedState × Noise → AugmentedState :=
  fun p => sampleStep mode R p.1.1 p.2

theorem augmentedStep_measurable (mode : Mode) (R : ℝ) :
    Measurable (augmentedStep mode R) :=
  (sampleStep_measurable mode R).comp (measurable_fst.fst.prodMk measurable_snd)

noncomputable def eventKernel (mode : Mode) (R : ℝ) : Kernel AugmentedState AugmentedState :=
  (Kernel.id.prod (Kernel.const AugmentedState noiseLaw)).map (augmentedStep mode R)

instance eventKernel_markov (mode : Mode) (R : ℝ) : IsMarkovKernel (eventKernel mode R) := by
  unfold eventKernel
  exact Kernel.IsMarkovKernel.map _ (augmentedStep_measurable mode R)

theorem eventKernel_apply (mode : Mode) (R : ℝ) (s : AugmentedState) :
    eventKernel mode R s = noiseLaw.map (fun u => sampleStep mode R s.1 u) := by
  rw [eventKernel, Kernel.map_apply _ (augmentedStep_measurable mode R),
    Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (augmentedStep_measurable mode R) measurable_prodMk_left]
  rfl

noncomputable def eventProcess (mode : Mode) (R : ℝ) :
    Rhone.MarkovChain.DiscreteProcess AugmentedState := ⟨eventKernel mode R⟩

end Rhone.Coalescent.IntervalProcess
