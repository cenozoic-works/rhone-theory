/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.FiniteIntervalMaterialSelectionMass
public import Rhone.Coalescent.FiniteIntervalMaterialSampler

/-! # Probabilities of individual actions under the sampler selector -/
@[expose] public section
namespace Rhone.Coalescent.SmcSupport
open IntervalProcess MeasureTheory

noncomputable def selectorScalar (mode : Mode) (R : ℝ) (s : State)
    (v : ℝ) : Option (ActionIndex s) := by
  classical
  exact chooseByRate (fun a => (candidateRate mode R s a : ℝ))
    Finset.univ.toList (v * (totalRate mode R s : ℝ))

theorem selectorScalar_mass (mode : Mode) (R : ℝ) (s : State)
    (ht : 0 < totalRate mode R s) (a : ActionIndex s) :
    unitUniform {v | selectorScalar mode R s v = some a} =
      ENNReal.ofReal ((candidateRate mode R s a : ℝ) / (totalRate mode R s : ℝ)) := by
  classical
  have hsum : (Finset.univ.toList.map
      (fun b : ActionIndex s => (candidateRate mode R s b : ℝ))).sum =
      (totalRate mode R s : ℝ) := by
    simp [totalRate]
  have ht' : 0 < (Finset.univ.toList.map
      (fun b : ActionIndex s => (candidateRate mode R s b : ℝ))).sum := by
    rw [hsum]
    exact_mod_cast ht
  have h := chooseByRate_uniform_mass_general
    (fun b : ActionIndex s => (candidateRate mode R s b : ℝ)) Finset.univ.toList
    Finset.univ.nodup_toList (fun b _ => (candidateRate mode R s b).property)
    ht' a (by simp)
  simpa only [selectorScalar, hsum] using h

theorem selectedAction_scalar (mode : Mode) (R : ℝ) (s : State) (u : Noise) :
    selectedAction mode R s u = selectorScalar mode R s (u 0) := rfl

end Rhone.Coalescent.SmcSupport
