/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.RankSeparator
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Tactic.FunProp

/-! # Almost-everywhere rank-one densities have vanishing continuous minors -/

@[expose] public section

open MeasureTheory Set Filter
namespace Rhone.Statistics.Identifiability

theorem continuous_zero_of_ae_rows (F : ℝ → ℝ → ℝ) (I J : Set ℝ)
    (hI : IsOpen I) (hJ : IsOpen J)
    (hF : Continuous (fun p : ℝ × ℝ => F p.1 p.2))
    (h : ∀ᵐ x ∂(volume : Measure ℝ).restrict I,
      ∀ᵐ y ∂(volume : Measure ℝ).restrict J, F x y = 0) :
    ∀ x ∈ I, ∀ y ∈ J, F x y = 0 := by
  have hrows : ∀ᵐ x ∂(volume : Measure ℝ).restrict I, ∀ y ∈ J, F x y = 0 := by
    filter_upwards [h] with x hx
    exact Measure.eqOn_open_of_ae_eq hx hJ
      (hF.comp (continuous_const.prodMk continuous_id)).continuousOn continuous_const.continuousOn
  intro x hx y hy
  have hcol : (fun z => F z y) =ᵐ[(volume : Measure ℝ).restrict I] fun _ => 0 := by
    filter_upwards [hrows] with z hz
    exact hz y hy
  exact Measure.eqOn_open_of_ae_eq hcol hI
    (hF.comp (continuous_id.prodMk continuous_const)).continuousOn continuous_const.continuousOn hx

theorem continuous_minors_zero_of_ae_rank_one (F : ℝ → ℝ → ℝ)
    (I J : Set ℝ) (hI : IsOpen I) (hJ : IsOpen J)
    (hF : Continuous (fun p : ℝ × ℝ => F p.1 p.2)) (a b : ℝ → ℝ)
    (h : ∀ᵐ p ∂((volume : Measure ℝ).restrict I).prod ((volume : Measure ℝ).restrict J),
      F p.1 p.2 = a p.1 * b p.2) :
    ∀ s₁ ∈ I, ∀ s₂ ∈ I, ∀ t₁ ∈ J, ∀ t₂ ∈ J,
      F s₁ t₁ * F s₂ t₂ - F s₁ t₂ * F s₂ t₁ = 0 := by
  have hrows := Measure.ae_ae_of_ae_prod h
  have hgood : ∀ᵐ s₁ ∂(volume : Measure ℝ).restrict I,
      ∀ᵐ s₂ ∂(volume : Measure ℝ).restrict I,
      ∀ t₁ ∈ J, ∀ t₂ ∈ J, F s₁ t₁ * F s₂ t₂ - F s₁ t₂ * F s₂ t₁ = 0 := by
    filter_upwards [hrows] with s₁ hs₁
    filter_upwards [hrows] with s₂ hs₂
    apply continuous_zero_of_ae_rows _ J J hJ hJ
    · exact (((hF.comp (continuous_const.prodMk continuous_fst)).mul
        (hF.comp (continuous_const.prodMk continuous_snd))).sub
        ((hF.comp (continuous_const.prodMk continuous_snd)).mul
          (hF.comp (continuous_const.prodMk continuous_fst))))
    · filter_upwards [hs₁, hs₂] with t₁ h₁ h₂
      filter_upwards [hs₁, hs₂] with t₂ h₃ h₄
      rw [h₁, h₂, h₃, h₄]
      ring
  intro s₁ hs₁ s₂ hs₂ t₁ ht₁ t₂ ht₂
  apply continuous_zero_of_ae_rows (fun x y => F x t₁ * F y t₂ - F x t₂ * F y t₁)
    I I hI hI _ _ s₁ hs₁ s₂ hs₂
  · exact (((hF.comp (continuous_fst.prodMk continuous_const)).mul
      (hF.comp (continuous_snd.prodMk continuous_const))).sub
      ((hF.comp (continuous_fst.prodMk continuous_const)).mul
        (hF.comp (continuous_snd.prodMk continuous_const))))
  · filter_upwards [hgood] with x hx
    filter_upwards [hx] with y hy
    exact hy t₁ ht₁ t₂ ht₂

theorem no_ae_rank_one_density (k : Nat) {c q r : ℝ}
    (hc : 0 < c) (hq : 0 < q) (hr : 0 < r) :
    ¬ ∃ a b : ℝ → ℝ,
      ∀ᵐ p ∂((volume : Measure ℝ).restrict (Ioo 0 1)).prod
        ((volume : Measure ℝ).restrict (Ioi 1)),
        upperDensity k c q r p.1 p.2 = a p.1 * b p.2 := by
  rintro ⟨a,b,h⟩
  have hz := continuous_minors_zero_of_ae_rank_one (upperDensity k c q r)
    (Ioo 0 1) (Ioi 1) isOpen_Ioo isOpen_Ioi (upperDensity_continuous k c q r) a b h
  obtain ⟨s₁,hs₁,s₂,hs₂,t,ht,hne⟩ := densityDeterminant_nonzero k hc hq hr
  exact hne (hz s₁ hs₁ s₂ hs₂ 2 (by norm_num) t (by change 1 < t; linarith [ht.1]))

end Rhone.Statistics.Identifiability
