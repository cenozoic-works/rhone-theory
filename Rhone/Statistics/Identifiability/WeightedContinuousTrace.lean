/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegrableExposureOnset
public import Rhone.Statistics.Identifiability.RegularJointLaw
public import Mathlib.Analysis.Calculus.TangentCone.Real

/-! # Identify a continuous diagonal trace from an L1-weighted upper-wedge density -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability

theorem weighted_continuous_upper_trace_ae (f : ℝ → ℝ) (hf : LocallyIntegrable f volume)
    (K L : ℝ × ℝ → ℝ) (hK : Continuous K) (hL : Continuous L)
    (hraw : ∀ᵐ p ∂planeVolume, 0 < p.1 → p.1 < p.2 →
      f p.1 * f p.2 * (K p - L p) = 0) :
    ∀ᵐ s, 0 < s → f s ≠ 0 → K (s,s) = L (s,s) := by
  have hrows := Measure.ae_ae_of_ae_prod hraw
  filter_upwards [hrows, LocallyIntegrable.ae_hasDerivAt_integral hf] with s hsrow hsder hs hfs
  by_contra htrace
  have hcont : Continuous (fun t => K (s,t) - L (s,t)) :=
    (hK.comp (continuous_const.prodMk continuous_id)).sub
      (hL.comp (continuous_const.prodMk continuous_id))
  have hnear : ∀ᶠ t in 𝓝 s, K (s,t) - L (s,t) ≠ 0 :=
    hcont.continuousAt.eventually (eventually_ne_nhds (sub_ne_zero.mpr htrace))
  obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.mp hnear
  let b := s + δ / 2
  have hsb : s < b := by dsimp [b]; linarith
  have hdiff (t : ℝ) (ht : t ∈ Ioc s b) : K (s,t) - L (s,t) ≠ 0 := by
    apply hnear
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr ht.1)]
    dsimp [b] at ht
    linarith [ht.2]
  have hzero : ∀ᵐ t, t ∈ Ioc s b → f t = 0 := by
    filter_upwards [hsrow] with t ht hmem
    have hp := (mul_eq_zero.mp (ht hs hmem.1)).resolve_right (hdiff t hmem)
    exact (mul_eq_zero.mp hp).resolve_left hfs
  have hconstant : EqOn (integratedClock f) (fun _ => integratedClock f s) (Icc s b) := by
    intro t ht
    have hi : (∫ u in s..t, f u) = 0 := by
      apply intervalIntegral.integral_zero_ae
      filter_upwards [hzero] with u hu hmem
      rw [uIoc_of_le ht.1] at hmem
      exact hu ⟨hmem.1, hmem.2.trans ht.2⟩
    rw [IntegrableExposure.interval_eq_clock_sub f hf] at hi
    exact sub_eq_zero.mp hi
  have hsMem : s ∈ Icc s b := ⟨le_rfl, hsb.le⟩
  have hz : HasDerivWithinAt (integratedClock f) 0 (Icc s b) s :=
    (hasDerivAt_const s (integratedClock f s)).hasDerivWithinAt.congr_of_mem hconstant hsMem
  have hud := uniqueDiffOn_Icc hsb s hsMem
  have hd := (hsder 0).hasDerivWithinAt.derivWithin hud
  have hd0 := hz.derivWithin hud
  exact hfs (hd.symm.trans hd0)

end Rhone.Statistics.Identifiability
