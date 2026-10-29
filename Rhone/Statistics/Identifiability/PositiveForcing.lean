/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.InhomogeneousMarkovFlow
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Positive forcing remains detectable after multiplication by an integrating factor -/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability

lemma intervalIntegral_positive_weight (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    {t : ℝ} (ht : 0 ≤ t) (hfn : ∀ u ∈ Icc 0 t, 0 ≤ f u)
    (hgp : ∀ u ∈ Icc 0 t, 0 < g u) (hint : 0 < ∫ u in (0 : ℝ)..t, f u) :
    0 < ∫ u in (0 : ℝ)..t, g u * f u := by
  have hn := intervalIntegral.integral_nonneg (μ := volume) ht
    (fun u hu => mul_nonneg (hgp u hu).le (hfn u hu))
  by_contra h
  have hz : (∫ u in (0 : ℝ)..t, g u * f u) = 0 := le_antisymm (le_of_not_gt h) hn
  have haen : ∀ᵐ u ∂volume.restrict (Ioc 0 t), 0 ≤ g u * f u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact mul_nonneg (hgp u ⟨hu.1.le, hu.2⟩).le (hfn u ⟨hu.1.le, hu.2⟩)
  have haez := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae ht haen
    ((hg.mul hf).intervalIntegrable 0 t)).mp hz
  have haef : ∀ᵐ u ∂volume.restrict (Ioc 0 t), f u = 0 := by
    filter_upwards [haez, ae_restrict_mem measurableSet_Ioc] with u hu humem
    exact (mul_eq_zero.mp hu).resolve_left (ne_of_gt (hgp u ⟨humem.1.le, humem.2⟩))
  have hz' : (∫ u in (0 : ℝ)..t, f u) = 0 := by
    apply intervalIntegral.integral_zero_ae
    rw [uIoc_of_le ht]
    exact (ae_restrict_iff' measurableSet_Ioc).mp haef
  exact (ne_of_gt hint) hz'

theorem linear_forcing_positive (a b z : ℝ → ℝ)
    (ha : Continuous a) (hb : Continuous b)
    (hz : ∀ u, HasDerivAt z (a u * z u + b u) u)
    {t : ℝ} (ht : 0 ≤ t) (hzero : 0 ≤ z 0)
    (hbn : ∀ u ∈ Icc 0 t, 0 ≤ b u) (hbint : 0 < ∫ u in (0 : ℝ)..t, b u) :
    0 < z t := by
  let H : ℝ → ℝ := fun u => ∫ v in (0 : ℝ)..u, a v
  have hH (u : ℝ) : HasDerivAt H (a u) u :=
    intervalIntegral.integral_hasDerivAt_right (ha.intervalIntegrable 0 u)
      ha.aestronglyMeasurable.stronglyMeasurableAtFilter ha.continuousAt
  have hHc : Continuous H := continuous_iff_continuousAt.mpr fun u => (hH u).continuousAt
  have hd (u : ℝ) : HasDerivAt (fun v => Real.exp (-H v) * z v)
      (Real.exp (-H u) * b u) u := by
    have hh : HasDerivAt (fun v => -H v) (-a u) u := (hH u).neg
    have hreal : HasDerivAt Real.exp (Real.exp (-H u)) (-H u) := Real.hasDerivAt_exp _
    have hexp : HasDerivAt (fun v => Real.exp (-H v))
        (Real.exp (-H u) * (-a u)) u := by
      simpa only [Function.comp_def] using hreal.comp u hh
    exact (hexp.mul (hz u)).congr_deriv (by ring)
  have hbpos := intervalIntegral_positive_weight b (fun u => Real.exp (-H u))
    hb (Real.continuous_exp.comp hHc.neg) ht hbn (fun _ _ => Real.exp_pos _) hbint
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    (((Real.continuous_exp.comp hHc.neg).mul hb).intervalIntegrable 0 t)
  have hH0 : H 0 = 0 := by simp [H]
  rw [hH0, neg_zero, Real.exp_zero, one_mul] at he
  have hp : 0 < Real.exp (-H t) * z t := by linarith
  exact (mul_pos_iff_of_pos_left (Real.exp_pos _)).mp hp

end Rhone.Statistics.Identifiability
