/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ContractiveDuhamel
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Noncommutative scalar-parameter derivative of the exponential -/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency false

namespace Rhone.Statistics.Identifiability.ContractiveDuhamel

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄]

noncomputable def expInsertion (X H : 𝔄) : 𝔄 :=
  ∫ s in (0 : ℝ)..1, NormedSpace.exp ((1-s) • X) * H * NormedSpace.exp (s • X)

theorem continuous_expInsertion (H : 𝔄) : Continuous (fun X : 𝔄 => expInsertion X H) := by
  have hexp : Continuous (NormedSpace.exp : 𝔄 → 𝔄) :=
    continuous_iff_continuousAt.mpr fun x =>
      (NormedSpace.exp_analytic (𝕂 := ℝ) x).continuousAt
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact ((hexp.comp ((continuous_const.sub continuous_snd).smul continuous_fst)).mul
    continuous_const).mul (hexp.comp (continuous_snd.smul continuous_fst))

theorem hasDerivAt_exp_affine (C Q : 𝔄) (a : ℝ) :
    HasDerivAt (fun x : ℝ => NormedSpace.exp (x • C + Q))
      (expInsertion (a • C + Q) C) a := by
  let J : ℝ → 𝔄 := fun x => ∫ s in (0 : ℝ)..1,
    NormedSpace.exp ((1-s) • (x • C + Q)) * C *
      NormedSpace.exp (s • (a • C + Q))
  have hexp : Continuous (NormedSpace.exp : 𝔄 → 𝔄) :=
    continuous_iff_continuousAt.mpr fun x =>
      (NormedSpace.exp_analytic (𝕂 := ℝ) x).continuousAt
  have hJ : Continuous J := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact ((hexp.comp
      ((continuous_const.sub continuous_snd).smul
        ((continuous_fst.smul continuous_const).add continuous_const))).mul
      continuous_const).mul (hexp.comp
        (continuous_snd.smul continuous_const))
  apply hasDerivAt_iff_tendsto_slope.mpr
  have heq : ∀ x : ℝ, x ≠ a →
      slope (fun y : ℝ => NormedSpace.exp (y • C + Q)) a x = J x := by
    intro x hxa
    have hid : (a • C + Q) + (x-a) • C = x • C + Q := by
      simp only [sub_smul]
      abel
    have hd := exp_add_sub_exp_one (a • C + Q) ((x-a) • C)
    rw [hid] at hd
    have hfactor : (∫ s in (0 : ℝ)..1,
        NormedSpace.exp ((1-s) • (x • C+Q)) * ((x-a) • C) *
          NormedSpace.exp (s • (a • C+Q))) = (x-a) • J x := by
      simp only [mul_smul_comm, smul_mul_assoc, intervalIntegral.integral_smul, J]
    rw [hfactor] at hd
    rw [slope_def_module, hd, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hxa), one_smul]
  have ht : Tendsto J (𝓝[≠] a) (𝓝 (J a)) :=
    hJ.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  exact (ht.congr' (eventually_mem_nhdsWithin.mono (fun x hx => (heq x hx).symm)))

theorem contDiff_one_exp_affine (C Q : 𝔄) :
    ContDiff ℝ 1 (fun x : ℝ => NormedSpace.exp (x • C + Q)) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun x => (hasDerivAt_exp_affine C Q x).differentiableAt, ?_⟩
  have heq : deriv (fun x : ℝ => NormedSpace.exp (x • C + Q)) =
      (fun x : ℝ => expInsertion (x • C+Q) C) := by
    funext x
    exact (hasDerivAt_exp_affine C Q x).deriv
  rw [heq]
  exact (continuous_expInsertion C).comp
    ((continuous_id.smul continuous_const).add continuous_const)

end Rhone.Statistics.Identifiability.ContractiveDuhamel
