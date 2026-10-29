/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.TimeOrderedDuhamel

/-! # Exact two-mark time-ordered Duhamel identity -/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators Topology Matrix.Norms.Operator

namespace Rhone.Statistics.Identifiability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem finiteMatrix_intervalIntegral_mul_left
    (M : Matrix ι ι ℝ) (f : ℝ → Matrix ι ι ℝ) (s t : ℝ)
    (hf : Continuous f) :
    (∫ u in s..t, M * f u) = M * ∫ u in s..t, f u := by
  exact (ContinuousLinearMap.mul ℝ (Matrix ι ι ℝ) M).intervalIntegral_comp_comm
    (hf.intervalIntegrable s t)

omit [DecidableEq ι] in
theorem finiteMatrix_intervalIntegral_mul_right
    (M : Matrix ι ι ℝ) (f : ℝ → Matrix ι ι ℝ) (s t : ℝ)
    (hf : Continuous f) :
    (∫ u in s..t, f u * M) = (∫ u in s..t, f u) * M := by
  exact ((ContinuousLinearMap.mul ℝ (Matrix ι ι ℝ)).flip M).intervalIntegral_comp_comm
    (hf.intervalIntegrable s t)

theorem inhomogeneousTransition_mixed_sub_eq_integral
    (C P R : ℝ → Matrix ι ι ℝ)
    (hC : ∀ i j, Continuous (fun t => C t i j))
    (hP : ∀ i j, Continuous (fun t => P t i j))
    (hR : ∀ i j, Continuous (fun t => R t i j)) (s t : ℝ) :
    inhomogeneousTransition (C + P + R) s t -
        inhomogeneousTransition (C + P) s t -
        inhomogeneousTransition (C + R) s t +
        inhomogeneousTransition C s t =
      (∫ u in s..t, ∫ v in u..t,
        inhomogeneousTransition (C + P + R) s u * P u *
          inhomogeneousTransition (C + R) u v * R v *
          inhomogeneousTransition C v t) +
      (∫ u in s..t, ∫ v in s..u,
        inhomogeneousTransition (C + P + R) s v * R v *
          inhomogeneousTransition (C + P) v u * P u *
          inhomogeneousTransition C u t) := by
  have hCP : ∀ i j, Continuous (fun u => (C + P) u i j) :=
    fun i j => (hC i j).add (hP i j)
  have hCR : ∀ i j, Continuous (fun u => (C + R) u i j) :=
    fun i j => (hC i j).add (hR i j)
  have hD : ∀ i j, Continuous (fun u => (C + P + R) u i j) :=
    fun i j => (hCP i j).add (hR i j)
  have hPc : Continuous P := continuous_pi fun i => continuous_pi (hP i)
  have hRc : Continuous R := continuous_pi fun i => continuous_pi (hR i)
  have hDs : Continuous (inhomogeneousTransition (C + P + R) s) :=
    (inhomogeneousTransition_continuous _ hD).comp
      (continuous_const.prodMk continuous_id)
  have hCPs : Continuous (inhomogeneousTransition (C + P) s) :=
    (inhomogeneousTransition_continuous _ hCP).comp
      (continuous_const.prodMk continuous_id)
  have hCRt : Continuous (fun u => inhomogeneousTransition (C + R) u t) :=
    (inhomogeneousTransition_continuous _ hCR).comp
      (continuous_id.prodMk continuous_const)
  have hCt : Continuous (fun u => inhomogeneousTransition C u t) :=
    (inhomogeneousTransition_continuous _ hC).comp
      (continuous_id.prodMk continuous_const)
  have hPDR : inhomogeneousTransition (C + P + R) s t -
      inhomogeneousTransition (C + R) s t =
      ∫ u in s..t, inhomogeneousTransition (C + P + R) s u * P u *
        inhomogeneousTransition (C + R) u t := by
    rw [inhomogeneousTransition_sub_eq_integral _ _ hD hCR]
    apply intervalIntegral.integral_congr
    intro u _
    have hm : (C + P + R) u - (C + R) u = P u := by
      simp only [Pi.add_apply]
      abel
    dsimp only
    rw [hm]
  have hPC : inhomogeneousTransition (C + P) s t -
      inhomogeneousTransition C s t =
      ∫ u in s..t, inhomogeneousTransition (C + P) s u * P u *
        inhomogeneousTransition C u t := by
    simpa only [Pi.add_apply, add_sub_cancel_left] using
      inhomogeneousTransition_sub_eq_integral (C + P) C hCP hC s t
  have hsplit : inhomogeneousTransition (C + P + R) s t -
      inhomogeneousTransition (C + P) s t -
      inhomogeneousTransition (C + R) s t + inhomogeneousTransition C s t =
      (∫ u in s..t, inhomogeneousTransition (C + P + R) s u * P u *
        (inhomogeneousTransition (C + R) u t - inhomogeneousTransition C u t)) +
      (∫ u in s..t,
        (inhomogeneousTransition (C + P + R) s u -
          inhomogeneousTransition (C + P) s u) * P u *
          inhomogeneousTransition C u t) := by
    calc
      _ = (inhomogeneousTransition (C + P + R) s t -
            inhomogeneousTransition (C + R) s t) -
          (inhomogeneousTransition (C + P) s t -
            inhomogeneousTransition C s t) := by abel
      _ = _ := by
        rw [hPDR, hPC, ← intervalIntegral.integral_sub
          (f := fun u => inhomogeneousTransition (C + P + R) s u * P u *
            inhomogeneousTransition (C + R) u t)
          (g := fun u => inhomogeneousTransition (C + P) s u * P u *
            inhomogeneousTransition C u t)
          (((hDs.mul hPc).mul hCRt).intervalIntegrable s t)
          (((hCPs.mul hPc).mul hCt).intervalIntegrable s t),
          ← intervalIntegral.integral_add
          (f := fun u => inhomogeneousTransition (C + P + R) s u * P u *
            (inhomogeneousTransition (C + R) u t - inhomogeneousTransition C u t))
          (g := fun u => (inhomogeneousTransition (C + P + R) s u -
            inhomogeneousTransition (C + P) s u) * P u *
            inhomogeneousTransition C u t)
          (((hDs.mul hPc).mul (hCRt.sub hCt)).intervalIntegrable s t)
          ((((hDs.sub hCPs).mul hPc).mul hCt).intervalIntegrable s t)]
        apply intervalIntegral.integral_congr
        intro u _
        noncomm_ring
  rw [hsplit]
  congr 1
  · apply intervalIntegral.integral_congr
    intro u _
    have hinner : inhomogeneousTransition (C + R) u t -
        inhomogeneousTransition C u t =
        ∫ v in u..t, inhomogeneousTransition (C + R) u v * R v *
          inhomogeneousTransition C v t := by
      simpa only [Pi.add_apply, add_sub_cancel_left] using
        inhomogeneousTransition_sub_eq_integral (C + R) C hCR hC u t
    dsimp only
    rw [hinner]
    have hCRu : Continuous (inhomogeneousTransition (C + R) u) :=
      (inhomogeneousTransition_continuous _ hCR).comp
        (continuous_const.prodMk continuous_id)
    rw [← finiteMatrix_intervalIntegral_mul_left _
      (fun v => inhomogeneousTransition (C + R) u v * R v *
        inhomogeneousTransition C v t) u t
      ((hCRu.mul hRc).mul hCt)]
    apply intervalIntegral.integral_congr
    intro v _
    simp only [Matrix.mul_assoc]
  · apply intervalIntegral.integral_congr
    intro u _
    have hinner : inhomogeneousTransition (C + P + R) s u -
        inhomogeneousTransition (C + P) s u =
        ∫ v in s..u, inhomogeneousTransition (C + P + R) s v * R v *
          inhomogeneousTransition (C + P) v u := by
      simpa only [Pi.add_apply, add_sub_cancel_left] using
        inhomogeneousTransition_sub_eq_integral (C + P + R) (C + P) hD hCP s u
    dsimp only
    rw [hinner]
    have hCPu : Continuous (fun v => inhomogeneousTransition (C + P) v u) :=
      (inhomogeneousTransition_continuous _ hCP).comp
        (continuous_id.prodMk continuous_const)
    rw [← finiteMatrix_intervalIntegral_mul_right (P u)
      (fun v => inhomogeneousTransition (C + P + R) s v * R v *
        inhomogeneousTransition (C + P) v u) s u
      ((hDs.mul hRc).mul hCPu)]
    rw [← finiteMatrix_intervalIntegral_mul_right (inhomogeneousTransition C u t)
      (fun v => inhomogeneousTransition (C + P + R) s v * R v *
        inhomogeneousTransition (C + P) v u * P u) s u
      (((hDs.mul hRc).mul hCPu).mul continuous_const)]

end Rhone.Statistics.Identifiability
