/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcSupport.ARGEventDensity

/-! # Finite histories of the unrestricted event process and their iteration -/
@[expose] public section
namespace Rhone.Coalescent.SmcSupport
open MeasureTheory ProbabilityTheory IntervalProcess
open scoped ENNReal

abbrev ARGPrefix (n : ℕ) := Finset.Iic n → AugmentedState

noncomputable def argPrefixLaw (R : ℝ) (z : AugmentedState) (n : ℕ) :
    Measure (ARGPrefix n) :=
  ((eventProcess false R).pathLaw z).map (fun ω k => ω k.val)

instance argPrefixLaw_probability (R : ℝ) (z : AugmentedState) (n : ℕ) :
    IsProbabilityMeasure (argPrefixLaw R z n) := by
  unfold argPrefixLaw
  infer_instance

noncomputable def argEventTransition (R : ℝ) (z : AugmentedState) :
    Measure AugmentedState := by
  classical
  exact if 1 < z.1.2.2.1 then
    (∑ i, ∑ j, if i.val < j.val then argPairTransition R z i j else 0) +
      ∑ i, argSplitTransition R z i
  else Measure.dirac (z.1, (z.1.1, .inl ()))

theorem eventKernel_ARG_eq_argEventTransition (R : ℝ) (hR : 0 ≤ R) (z : AugmentedState) :
    eventKernel false R z = argEventTransition R z := by
  classical
  by_cases hm : 1 < z.1.2.2.1
  · simp only [argEventTransition, ite_eq_left hm]
    exact eventKernel_ARG_density R hR z hm
  · rw [eventKernel_apply]
    have hle : z.1.2.2.1 ≤ 1 := Nat.le_of_not_gt hm
    simp [sampleStep, hle, argEventTransition, hm]

theorem argPrefixLaw_next (R : ℝ) (z : AugmentedState) (n : ℕ) :
    ((eventProcess false R).pathLaw z).map
      (fun ω => ((fun k : Finset.Iic n => ω k.val), ω (n + 1))) =
    (argPrefixLaw R z n).compProd ((eventProcess false R).stepSeq n) := by
  have hprefix : argPrefixLaw R z n =
      Kernel.partialTraj (X := fun _ : ℕ => AugmentedState)
        (eventProcess false R).stepSeq 0 n (fun _ => z) := by
    exact Kernel.traj_map_frestrictLe_apply
      (X := fun _ : ℕ => AugmentedState) (κ := (eventProcess false R).stepSeq)
      0 n (fun _ => z)
  rw [hprefix]
  exact (Kernel.partialTraj_compProd_eq_map_traj
    (X := fun _ : ℕ => AugmentedState)
    (κ := (eventProcess false R).stepSeq) (x₀ := fun _ => z) (Nat.zero_le n)).symm

theorem argPrefixLaw_lintegral_next (R : ℝ) (hR : 0 ≤ R)
    (z : AugmentedState) (n : ℕ)
    (f : ARGPrefix n × AugmentedState → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ ω, f ((fun k : Finset.Iic n => ω k.val), ω (n + 1))
      ∂(eventProcess false R).pathLaw z =
    ∫⁻ h, ∫⁻ y, f (h, y)
      ∂argEventTransition R (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
      ∂argPrefixLaw R z n := by
  rw [← lintegral_map hf (by fun_prop), argPrefixLaw_next,
    Measure.lintegral_compProd hf]
  congr 1
  funext h
  rw [Rhone.MarkovChain.DiscreteProcess.stepSeq, Kernel.comap_apply]
  change (∫⁻ y, f (h, y) ∂eventKernel false R (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩)) = _
  rw [eventKernel_ARG_eq_argEventTransition R hR]

end Rhone.Coalescent.SmcSupport
