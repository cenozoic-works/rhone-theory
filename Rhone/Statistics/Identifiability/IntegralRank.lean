/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.RankFactorization
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Integration over intervals preserves a rank-two function pair -/

@[expose] public section

open Set MeasureTheory
namespace Rhone.Statistics.Identifiability

noncomputable def primitiveFrom (f : ℝ → ℝ) (a t : ℝ) : ℝ := ∫ x in a..t, f x

theorem primitiveFrom_hasDerivAt (f : ℝ → ℝ) (hf : Continuous f) (a t : ℝ) :
    HasDerivAt (primitiveFrom f a) (f t) t :=
  intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable a t)
    hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt

theorem integrated_rank_two (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    {a b : ℝ} (hab : a < b)
    (hrank : ∃ x ∈ Icc a b, ∃ y ∈ Icc a b, f x * g y - g x * f y ≠ 0) :
    ∃ x ∈ Icc a b, ∃ y ∈ Icc a b,
      primitiveFrom f a x * primitiveFrom g a y -
      primitiveFrom g a x * primitiveFrom f a y ≠ 0 := by
  by_contra hn
  push Not at hn
  obtain ⟨x,hx,y,hy,hne⟩ := hrank
  have hz : ∀ s ∈ Icc a b, f x * primitiveFrom g a s - g x * primitiveFrom f a s = 0 := by
    intro s hs
    exact derivative_zero_on_interval _ hab hx
      (((primitiveFrom_hasDerivAt f hf a x).mul_const (primitiveFrom g a s)).sub
        ((primitiveFrom_hasDerivAt g hg a x).mul_const (primitiveFrom f a s)))
      (fun z hz => hn z hz s hs)
  exact hne (derivative_zero_on_interval _ hab hy
    (((primitiveFrom_hasDerivAt g hg a y).const_mul (f x)).sub
      ((primitiveFrom_hasDerivAt f hf a y).const_mul (g x))) hz)

theorem backwardFlux_continuous (k : Nat) (c q r : ℝ) (i : Fin 2) :
    Continuous (backwardFlux k c q r i) :=
  continuous_iff_continuousAt.mpr (fun t => (backwardFlux_hasDerivAt k c q r i t).continuousAt)

theorem forwardDensity_continuous (k : Nat) (c q : ℝ) (i : Fin 2) :
    Continuous (forwardDensity k c q i) :=
  continuous_iff_continuousAt.mpr (fun t => (forwardDensity_hasDerivAt k c q i t).continuousAt)

theorem integrated_backward_rank_two (k : Nat) {c q r : ℝ}
    (hc : 0 < c) (hq : 0 < q) (hr : 0 < r) :
    ∃ s₁ ∈ Icc (0 : ℝ) (1/2), ∃ s₂ ∈ Icc (0 : ℝ) (1/2),
      primitiveFrom (backwardFlux k c q r 0) 0 s₁ *
        primitiveFrom (backwardFlux k c q r 1) 0 s₂ -
      primitiveFrom (backwardFlux k c q r 1) 0 s₁ *
        primitiveFrom (backwardFlux k c q r 0) 0 s₂ ≠ 0 :=
  integrated_rank_two _ _ (backwardFlux_continuous k c q r 0)
    (backwardFlux_continuous k c q r 1) (by norm_num) (backward_rank_two k hc hq hr)

theorem integrated_forward_rank_two (k : Nat) {c q : ℝ} (hc : c ≠ 0) (hq : q ≠ 0) :
    ∃ t₁ ∈ Icc (1 : ℝ) 4, ∃ t₂ ∈ Icc (1 : ℝ) 4,
      primitiveFrom (forwardDensity k c q 0) 1 t₁ *
        primitiveFrom (forwardDensity k c q 1) 1 t₂ -
      primitiveFrom (forwardDensity k c q 1) 1 t₁ *
        primitiveFrom (forwardDensity k c q 0) 1 t₂ ≠ 0 := by
  apply integrated_rank_two _ _ (forwardDensity_continuous k c q 0)
    (forwardDensity_continuous k c q 1) (by norm_num)
  obtain ⟨t,ht,hne⟩ := column_rank_two_of_wronskian _ _ (show (2 : ℝ) < 3 by norm_num)
    (forwardDensity_hasDerivAt k c q 0 2) (forwardDensity_hasDerivAt k c q 1 2)
    (forward_wronskian_ne_zero k hc hq 2)
  exact ⟨2,by norm_num,t,⟨by linarith [ht.1],by linarith [ht.2]⟩,hne⟩

end Rhone.Statistics.Identifiability
