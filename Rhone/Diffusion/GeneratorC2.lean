/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Diffusion.Generator
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # The Wright–Fisher generator on twice continuously differentiable functions -/

@[expose] public section

namespace Rhone.Diffusion

open Polynomial

theorem continuous_deriv_deriv_of_contDiff_two {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (deriv (deriv f)) := by
  have h1 : ContDiff ℝ 1 (deriv f) :=
    (contDiff_succ_iff_deriv (n := 1)).1 (show ContDiff ℝ (1 + 1) f from hf) |>.2.2
  exact (contDiff_one_iff_deriv.1 h1).2

private theorem differentiable_deriv_of_contDiff_two {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    Differentiable ℝ (deriv f) := by
  have h1 : ContDiff ℝ 1 (deriv f) :=
    (contDiff_succ_iff_deriv (n := 1)).1 (show ContDiff ℝ (1 + 1) f from hf) |>.2.2
  exact (contDiff_one_iff_deriv.1 h1).1

theorem wfGenerator_add {f g : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : ℝ) :
    wfGenerator (fun y => f y + g y) x = wfGenerator f x + wfGenerator g x := by
  have h1 : deriv (fun y => f y + g y) = fun y => deriv f y + deriv g y :=
    funext fun y => deriv_add (hf.differentiable (by norm_num) y)
      (hg.differentiable (by norm_num) y)
  have h2 : deriv (fun y => deriv f y + deriv g y) x = deriv (deriv f) x + deriv (deriv g) x :=
    deriv_add (differentiable_deriv_of_contDiff_two hf x)
      (differentiable_deriv_of_contDiff_two hg x)
  rw [wfGenerator, h1, h2, wfGenerator, wfGenerator]
  ring

theorem wfGenerator_const_mul (c : ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (x : ℝ) :
    wfGenerator (fun y => c * f y) x = c * wfGenerator f x := by
  have h1 : deriv (fun y => c * f y) = fun y => c * deriv f y :=
    funext fun y => deriv_const_mul c (hf.differentiable (by norm_num) y)
  have h2 : deriv (fun y => c * deriv f y) x = c * deriv (deriv f) x :=
    deriv_const_mul c (differentiable_deriv_of_contDiff_two hf x)
  rw [wfGenerator, h1, h2, wfGenerator]
  ring

theorem wfGenerator_sub {f g : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : ℝ) :
    wfGenerator (fun y => f y - g y) x = wfGenerator f x - wfGenerator g x := by
  have hg' : ContDiff ℝ 2 (fun y => (-1 : ℝ) * g y) := contDiff_const.mul hg
  have h := wfGenerator_add hf hg' x
  have h3 := wfGenerator_const_mul (-1) hg x
  have e : (fun y => f y - g y) = fun y => f y + (-1 : ℝ) * g y := funext fun y => by ring
  rw [e, h, h3]
  ring

theorem wfGenerator_const (c x : ℝ) : wfGenerator (fun _ => c) x = 0 := by
  simp [wfGenerator]

theorem wfGenerator_id (x : ℝ) : wfGenerator (fun y => y) x = 0 := by
  have h : deriv (fun y : ℝ => y) = fun _ => 1 := funext fun y => deriv_id y
  simp [wfGenerator, h]

theorem wfGenerator_sq (x : ℝ) : wfGenerator (fun y => y ^ 2) x = x * (1 - x) := by
  have h : deriv (fun y : ℝ => y ^ 2) = fun y => 2 * y := funext fun y => by
    simp [deriv_fun_pow]
  have h2 : deriv (fun y : ℝ => 2 * y) x = 2 := by simp
  rw [wfGenerator, h, h2]
  ring

theorem wfGenerator_mul_one_sub (x : ℝ) :
    wfGenerator (fun y => y * (1 - y)) x = -(x * (1 - x)) := by
  have h : (fun y : ℝ => y * (1 - y)) = fun y => y - y ^ 2 := funext fun y => by ring
  have hid : ContDiff ℝ 2 (fun y : ℝ => y) := contDiff_id
  have hsq : ContDiff ℝ 2 (fun y : ℝ => y ^ 2) := contDiff_id.pow 2
  rw [h, wfGenerator_sub hid hsq, wfGenerator_id, wfGenerator_sq]
  ring

theorem wfGenerator_polynomial (p : ℝ[X]) :
    ∃ q : ℝ[X], ∀ x, wfGenerator (fun y => p.eval y) x = q.eval x :=
  ⟨C (1 / 2) * (X * (1 - X)) * derivative (derivative p), fun x => by
    rw [wfGenerator_eval]
    simp only [eval_mul, eval_C, eval_X, eval_sub, eval_one]
    ring⟩

theorem continuous_wfGenerator {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (wfGenerator f) := by
  have := continuous_deriv_deriv_of_contDiff_two hf
  unfold wfGenerator
  fun_prop

theorem continuousOn_wfGenerator_Icc {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    ContinuousOn (wfGenerator f) (Set.Icc 0 1) :=
  (continuous_wfGenerator hf).continuousOn

noncomputable def wfGeneratorSel (σ : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  wfGenerator f x + σ * (x * (1 - x)) * deriv f x

noncomputable def wfGeneratorMut (θ₁ θ₂ : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  wfGenerator f x + (θ₁ * (1 - x) - θ₂ * x) / 2 * deriv f x

noncomputable def wfGeneratorForces (σ θ₁ θ₂ : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  wfGenerator f x + σ * (x * (1 - x)) * deriv f x + (θ₁ * (1 - x) - θ₂ * x) / 2 * deriv f x

theorem wfGeneratorSel_eq_forces (σ : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    wfGeneratorSel σ f x = wfGeneratorForces σ 0 0 f x := by
  simp [wfGeneratorSel, wfGeneratorForces]

theorem wfGeneratorMut_eq_forces (θ₁ θ₂ : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    wfGeneratorMut θ₁ θ₂ f x = wfGeneratorForces 0 θ₁ θ₂ f x := by
  simp [wfGeneratorMut, wfGeneratorForces]

theorem wfGeneratorForces_zero (f : ℝ → ℝ) (x : ℝ) :
    wfGeneratorForces 0 0 0 f x = wfGenerator f x := by
  simp [wfGeneratorForces]

theorem wfGeneratorSel_const (σ c x : ℝ) : wfGeneratorSel σ (fun _ => c) x = 0 := by
  simp [wfGeneratorSel, wfGenerator]

theorem wfGeneratorMut_const (θ₁ θ₂ c x : ℝ) : wfGeneratorMut θ₁ θ₂ (fun _ => c) x = 0 := by
  simp [wfGeneratorMut, wfGenerator]

theorem wfGeneratorSel_id (σ x : ℝ) : wfGeneratorSel σ (fun y => y) x = σ * (x * (1 - x)) := by
  simp [wfGeneratorSel, wfGenerator_id]

theorem wfGeneratorMut_id (θ₁ θ₂ x : ℝ) :
    wfGeneratorMut θ₁ θ₂ (fun y => y) x = (θ₁ * (1 - x) - θ₂ * x) / 2 := by
  simp [wfGeneratorMut, wfGenerator_id]

end Rhone.Diffusion
