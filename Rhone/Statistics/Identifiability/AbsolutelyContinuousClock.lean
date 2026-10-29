/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.PanPostPair
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-! # Deterministic-clock survival from absolutely continuous forward equations -/

@[expose] public section

open scoped NNReal Topology
open Set Filter MeasureTheory Finset
namespace Rhone.Statistics.Identifiability

set_option backward.isDefEq.respectTransparency false

theorem ac_comp_lipschitzOn (f g : ℝ → ℝ) {a b : ℝ} (D : Set ℝ) {K : ℝ≥0}
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : LipschitzOnWith K g D)
    (hm : ∀ x ∈ uIcc a b, f x ∈ D) :
    AbsolutelyContinuousOnInterval (fun x => g (f x)) a b :=
  hg.comp_absolutelyContinuousOnInterval hm hf

theorem ac_exp {H : ℝ → ℝ} {a b : ℝ} (hH : AbsolutelyContinuousOnInterval H a b) :
    AbsolutelyContinuousOnInterval (fun x => Real.exp (H x)) a b := by
  obtain ⟨C,hC⟩ := hH.exists_bound
  have hdiff : ContDiffOn ℝ 1 Real.exp (Icc (-C) C) := Real.contDiff_exp.contDiffOn
  obtain ⟨K,hK⟩ := hdiff.exists_lipschitzOnWith (by decide) (convex_Icc _ _) isCompact_Icc
  apply ac_comp_lipschitzOn H Real.exp (Icc (-C) C) hH hK
  intro x hx
  simpa only [Real.norm_eq_abs, abs_le, Set.mem_Icc] using hC x hx

theorem survival_clock_of_ac_forward_equation (S rate H : ℝ → ℝ) (a b : ℝ)
    (hSac : AbsolutelyContinuousOnInterval S a b)
    (hHac : AbsolutelyContinuousOnInterval H a b)
    (hS : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt S (-rate x * S x) x)
    (hH : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt H (rate x) x) :
    S b = S a * Real.exp (H a - H b) := by
  have hac : AbsolutelyContinuousOnInterval (fun x => S x * Real.exp (H x)) a b :=
    hSac.mul (ac_exp hHac)
  have hg : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt (fun y => S y * Real.exp (H y)) 0 x := by
    filter_upwards [hS,hH] with x hx hHx
    intro hmem
    convert! (hx hmem).mul (hHx hmem).exp using 1
    ring
  obtain ⟨C,hC⟩ := hac.const_of_ae_hasDerivAt_zero hg
  have h : S b * Real.exp (H b) = S a * Real.exp (H a) :=
    (hC b (by simp)).trans (hC a (by simp)).symm
  apply mul_right_cancel₀ (Real.exp_pos (H b)).ne'
  rw [mul_assoc, ← Real.exp_add, sub_add_cancel]
  exact h

theorem panPost_survival_clock_ae (rate recomb H : ℝ → ℝ) (p : ℝ → Fin 2 → ℝ) (a b : ℝ)
    (hpac : ∀ i, AbsolutelyContinuousOnInterval (fun x => p x i) a b)
    (hHac : AbsolutelyContinuousOnInterval H a b)
    (hp : ∀ᵐ x, x ∈ uIcc a b → ∀ i, HasDerivAt (fun y => p y i)
      (∑ j, p x j * panPostGenerator (rate x) (recomb x) j i) x)
    (hH : ∀ᵐ x, x ∈ uIcc a b → HasDerivAt H (rate x) x) :
    (∑ i, p b i) = (∑ i, p a i) * Real.exp (H a - H b) := by
  apply survival_clock_of_ac_forward_equation _ rate H a b _ hHac _ hH
  · convert! (hpac 0).add (hpac 1) using 1
    funext x
    simp only [Fin.sum_univ_two, Pi.add_apply]
  · filter_upwards [hp] with x hx
    intro hmem
    exact panPost_total_derivative rate recomb p x (hx hmem)

end Rhone.Statistics.Identifiability
