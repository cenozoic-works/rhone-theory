/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.FiniteIntervalMaterialKernel
public import Rhone.Coalescent.SmcSupport.SelectorMass

/-! # Coordinate and candidate-selection laws of the independent real-valued marks -/
@[expose] public section

namespace Rhone.Coalescent.IntervalProcess
open MeasureTheory
open scoped ENNReal

theorem noiseLaw_eval (i : Fin 3) :
    noiseLaw.map (fun u => u i) = unitUniform :=
  (measurePreserving_eval (fun _ : Fin 3 => unitUniform) i).map_eq

theorem noiseLaw_ae_marks :
    ∀ᵐ u ∂noiseLaw, ∀ i : Fin 3, 0 < u i ∧ u i < 1 := by
  have hu : ∀ᵐ v ∂unitUniform, v ∈ Set.Ioo (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Ioo
  apply ae_all_iff.mpr
  intro i
  exact (measurePreserving_eval (fun _ : Fin 3 => unitUniform) i).quasiMeasurePreserving.ae hu

theorem noiseLaw_selectedAction_mass (mode : Mode) (R : ℝ) (s : State)
    (ht : 0 < totalRate mode R s) (a : ActionIndex s) :
    noiseLaw {u | selectedAction mode R s u = some a} =
      ENNReal.ofReal ((candidateRate mode R s a : ℝ) / (totalRate mode R s : ℝ)) := by
  classical
  let : MeasurableSpace (Option (ActionIndex s)) := ⊤
  have hm : Measurable (Rhone.Coalescent.SmcSupport.selectorScalar mode R s) :=
    chooseByRate_measurable (fun b _ => (candidateRate mode R s b : ℝ))
      (fun _ => measurable_const) Finset.univ.toList
      (fun v => v * (totalRate mode R s : ℝ)) (measurable_id.mul_const _)
  have hs : MeasurableSet {v : ℝ |
      Rhone.Coalescent.SmcSupport.selectorScalar mode R s v = some a} :=
    hm (show MeasurableSet ({some a} : Set (Option (ActionIndex s))) from by trivial)
  have hmass := Rhone.Coalescent.SmcSupport.selectorScalar_mass mode R s ht a
  rw [← noiseLaw_eval (0 : Fin 3), Measure.map_apply (measurable_pi_apply 0) hs] at hmass
  simpa only [Set.preimage_ofPred_eq, Rhone.Coalescent.SmcSupport.selectedAction_scalar] using hmass

end Rhone.Coalescent.IntervalProcess
