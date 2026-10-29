/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegrableExposureOnset
public import Rhone.Statistics.Identifiability.IntegrableClockCalculus

/-! # Exact scalar survival for AC solutions with a locally L1 hazard -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability

lemma scalar_ac_survival_identity (a g : ℝ → ℝ) (ha : LocallyIntegrable a volume)
    (s t : ℝ) (hg : AbsolutelyContinuousOnInterval g s t)
    (hd : ∀ᵐ u, u ∈ uIcc s t → HasDerivAt g (-a u * g u) u) :
    g t = g s * Real.exp (-(∫ u in s..t, a u)) := by
  let H := fun u => ∫ v in s..u, a v
  have hHac : AbsolutelyContinuousOnInterval H s t :=
    (locallyIntegrable_interval a ha s t).absolutelyContinuousOnInterval_intervalIntegral
      (c := s) (by simp)
  have hac : AbsolutelyContinuousOnInterval (fun u => Real.exp (H u) * g u) s t :=
    (ac_exp hHac).fun_mul hg
  have hzero : ∀ᵐ u, u ∈ uIcc s t →
      HasDerivAt (fun v => Real.exp (H v) * g v) 0 u := by
    filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral ha, hd] with u hu hgu hmem
    have hH : HasDerivAt H (a u) u := hu s
    exact ((hH.exp).mul (hgu hmem)).congr_deriv (by ring)
  obtain ⟨C, hC⟩ := hac.const_of_ae_hasDerivAt_zero hzero
  have he := (hC t (by simp)).trans (hC s (by simp)).symm
  have hExp : Real.exp (H t) * Real.exp (-H t) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  apply mul_left_cancel₀ (Real.exp_ne_zero (H t))
  calc
    _ = g s := by simpa [H] using he
    _ = _ := by
      change g s = Real.exp (H t) * (g s * Real.exp (-H t))
      rw [mul_left_comm, hExp, mul_one]

end Rhone.Statistics.Identifiability
