/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Diffusion.GeneratorC2
public import Rhone.Diffusion.KimuraBoundaryProblem
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The neutral absorption-time function as the solution of a boundary value problem

Source: kimura_ohta1969, p. 765, eq. (14). -/

@[expose] public section

namespace Rhone.Diffusion

open MarkovChain Set Filter Topology

noncomputable def neutralAbsorptionTime (x : ℝ) : ℝ :=
  -2 * (x * Real.log x + (1 - x) * Real.log (1 - x))

private theorem hasDerivAt_neutralAbsorptionTime {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) :
    HasDerivAt neutralAbsorptionTime (-2 * (Real.log y - Real.log (1 - y))) y := by
  have h1 : HasDerivAt (fun x : ℝ => x * Real.log x) (Real.log y + 1) y :=
    Real.hasDerivAt_mul_log hy0.ne'
  have hs : HasDerivAt (fun x : ℝ => 1 - x) (-1) y := by
    simpa using (hasDerivAt_id y).const_sub 1
  have h2 : HasDerivAt (fun x : ℝ => x * Real.log x)
      (Real.log (1 - y) + 1) (1 - y) := Real.hasDerivAt_mul_log (by linarith)
  have h3 : HasDerivAt (fun x : ℝ => (1 - x) * Real.log (1 - x))
      ((Real.log (1 - y) + 1) * -1) y := h2.comp y hs
  have h4 := (h1.add h3).const_mul (-2)
  exact h4.congr_deriv (by ring)

private theorem hasDerivAt_deriv_neutralAbsorptionTime {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) :
    HasDerivAt (deriv neutralAbsorptionTime) (-2 * (1 / y + 1 / (1 - y))) y := by
  have hs : HasDerivAt (fun x : ℝ => 1 - x) (-1) y := by
    simpa using (hasDerivAt_id y).const_sub 1
  have h1 : HasDerivAt (fun x : ℝ => Real.log x) (1 / y) y := by
    simpa using (Real.hasDerivAt_log hy0.ne')
  have h2 : HasDerivAt (fun x : ℝ => Real.log (1 - x)) (-1 / (1 - y)) y :=
    hs.log (by linarith)
  have h3 := (h1.sub h2).const_mul (-2)
  have hev : deriv neutralAbsorptionTime =ᶠ[𝓝 y]
      fun x => -2 * (Real.log x - Real.log (1 - x)) := by
    filter_upwards [Ioo_mem_nhds hy0 hy1] with x hx
    exact (hasDerivAt_neutralAbsorptionTime hx.1 hx.2).deriv
  refine (h3.congr_of_eventuallyEq hev).congr_deriv ?_
  ring

/-- Source: kimura_ohta1969, p. 765, eq. (14). -/
theorem wfGenerator_neutralAbsorptionTime {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    wfGenerator neutralAbsorptionTime x = -1 := by
  have h1 : (1 - x) ≠ 0 := by linarith
  rw [wfGenerator, (hasDerivAt_deriv_neutralAbsorptionTime hx0 hx1).deriv]
  field_simp
  ring

theorem continuous_neutralAbsorptionTime : Continuous neutralAbsorptionTime := by
  unfold neutralAbsorptionTime
  have h1 : Continuous fun x : ℝ => x * Real.log x := Real.continuous_mul_log
  have h2 : Continuous fun x : ℝ => (1 - x) * Real.log (1 - x) :=
    Real.continuous_mul_log.comp (continuous_const.sub continuous_id)
  exact continuous_const.mul (h1.add h2)

theorem neutralAbsorptionTime_zero : neutralAbsorptionTime 0 = 0 := by
  simp [neutralAbsorptionTime]

theorem neutralAbsorptionTime_one : neutralAbsorptionTime 1 = 0 := by
  simp [neutralAbsorptionTime]

theorem tendsto_neutralAbsorptionTime_zero :
    Tendsto neutralAbsorptionTime (𝓝[>] 0) (𝓝 0) := by
  have := continuous_neutralAbsorptionTime.tendsto 0
  rw [neutralAbsorptionTime_zero] at this
  exact this.mono_left nhdsWithin_le_nhds

theorem tendsto_neutralAbsorptionTime_one :
    Tendsto neutralAbsorptionTime (𝓝[<] 1) (𝓝 0) := by
  have := continuous_neutralAbsorptionTime.tendsto 1
  rw [neutralAbsorptionTime_one] at this
  exact this.mono_left nhdsWithin_le_nhds

/-- Source: kimura_ohta1969, pp. 764–765. -/
theorem neutralAbsorptionTime_unique {f : ℝ → ℝ}
    (hc : ContinuousOn f (Icc 0 1)) (hd : ContDiffOn ℝ 2 f (Ioo 0 1))
    (hL : ∀ x ∈ Ioo (0 : ℝ) 1, wfGenerator f x = -1) (h0 : f 0 = 0) (h1 : f 1 = 0) :
    ∀ x ∈ Icc (0 : ℝ) 1, f x = neutralAbsorptionTime x := by
  have hd' := (contDiffOn_succ_iff_deriv_of_isOpen (n := 1) isOpen_Ioo).1
    (show ContDiffOn ℝ (1 + 1) f (Ioo 0 1) from hd)
  have hf : ∀ y ∈ Ioo (0 : ℝ) 1, HasDerivAt f (deriv f y) y := fun y hy =>
    ((hd'.1.differentiableAt (isOpen_Ioo.mem_nhds hy))).hasDerivAt
  have hf' : ∀ y ∈ Ioo (0 : ℝ) 1, HasDerivAt (deriv f) (deriv (deriv f) y) y := fun y hy =>
    ((hd'.2.2.differentiableOn one_ne_zero).differentiableAt (isOpen_Ioo.mem_nhds hy)).hasDerivAt
  have key := eq_affine_of_hasDerivAt_zero
    (w := fun t => f t - neutralAbsorptionTime t)
    (w' := fun t => deriv f t - deriv neutralAbsorptionTime t)
    (hc.sub continuous_neutralAbsorptionTime.continuousOn)
    (fun y hy => (hf y hy).sub
      (hasDerivAt_neutralAbsorptionTime hy.1 hy.2).differentiableAt.hasDerivAt)
    (fun y hy => by
      have h := (hf' y hy).sub (hasDerivAt_deriv_neutralAbsorptionTime hy.1 hy.2)
      have hy0 : y ≠ 0 := hy.1.ne'
      have hy1 : 1 - y ≠ 0 := by linarith [hy.2]
      have hLy := hL y hy
      unfold wfGenerator at hLy
      have hD : deriv (deriv f) y = -2 * (1 / y + 1 / (1 - y)) := by
        field_simp
        linarith
      rwa [hD, sub_self] at h)
  intro x hx
  have h := key x hx
  simp only [h0, h1, neutralAbsorptionTime_zero, neutralAbsorptionTime_one, sub_self,
    zero_mul, add_zero] at h
  linarith

end Rhone.Diffusion
