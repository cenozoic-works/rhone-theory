/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.Witness
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! # Derivative certificates for rank two on separated time intervals -/

@[expose] public section

open Set
namespace Rhone.Statistics.Identifiability

theorem derivative_zero_on_interval (f : ℝ → ℝ) {a b x d : ℝ}
    (hab : a < b) (hx : x ∈ Icc a b) (hf : HasDerivAt f d x)
    (hz : ∀ t ∈ Icc a b, f t = 0) : d = 0 := by
  have hconst : HasDerivWithinAt f 0 (Icc a b) x :=
    (hasDerivWithinAt_const x (Icc a b) (0 : ℝ)).congr hz (hz x hx)
  exact (uniqueDiffOn_Icc hab x hx).eq_deriv _ hf.hasDerivWithinAt hconst

theorem second_derivative_zero_on_interval (f f' f'' : ℝ → ℝ) {e : ℝ}
    (he : 0 < e) (hf : ∀ t, HasDerivAt f (f' t) t)
    (hf' : HasDerivAt f' (f'' 0) 0)
    (hz : ∀ t ∈ Icc 0 e, f t = 0) : f'' 0 = 0 := by
  apply derivative_zero_on_interval f' he ⟨le_refl 0, he.le⟩ hf'
  intro t ht
  exact derivative_zero_on_interval f he ht (hf t) hz

theorem row_rank_two_of_jets (a b a' b' b'' : ℝ → ℝ) {e : ℝ} (he : 0 < e)
    (ha : ∀ t, HasDerivAt a (a' t) t) (hb : ∀ t, HasDerivAt b (b' t) t)
    (hb' : HasDerivAt b' (b'' 0) 0)
    (ha' : a' 0 ≠ 0) (hb'zero : b' 0 = 0) (hb'' : b'' 0 ≠ 0) :
    ∃ s₁ ∈ Icc 0 e, ∃ s₂ ∈ Icc 0 e, a s₁ * b s₂ - b s₁ * a s₂ ≠ 0 := by
  by_contra hn
  push Not at hn
  have hzero : ∀ s ∈ Icc 0 e, b s = 0 := by
    intro s hs
    have hd := derivative_zero_on_interval (fun x => a x * b s - b x * a s)
      he (show (0 : ℝ) ∈ Icc 0 e from ⟨le_refl 0, he.le⟩)
      (((ha 0).mul_const (b s)).sub ((hb 0).mul_const (a s)))
      (fun t ht => hn t ht s hs)
    rw [hb'zero, zero_mul, sub_zero] at hd
    exact (mul_eq_zero.mp hd).resolve_left ha'
  exact hb'' (second_derivative_zero_on_interval b b' b'' he hb hb' hzero)

theorem column_rank_two_of_wronskian (f g : ℝ → ℝ) {u v f' g' : ℝ}
    (huv : u < v) (hf : HasDerivAt f f' u) (hg : HasDerivAt g g' u)
    (hw : f u * g' - g u * f' ≠ 0) :
    ∃ t ∈ Icc u v, f u * g t - g u * f t ≠ 0 := by
  by_contra hn
  push Not at hn
  exact hw (derivative_zero_on_interval (fun t => f u * g t - g u * f t)
    huv ⟨le_refl u, huv.le⟩
    ((hg.const_mul (f u)).sub (hf.const_mul (g u))) hn)

theorem rank_product_determinant (a b f g : ℝ → ℝ) (s₁ s₂ t₁ t₂ : ℝ) :
    (a s₁*f t₁ + b s₁*g t₁) * (a s₂*f t₂ + b s₂*g t₂) -
    (a s₁*f t₂ + b s₁*g t₂) * (a s₂*f t₁ + b s₂*g t₁) =
    (a s₁*b s₂ - b s₁*a s₂) * (f t₁*g t₂ - g t₁*f t₂) := by ring

end Rhone.Statistics.Identifiability
