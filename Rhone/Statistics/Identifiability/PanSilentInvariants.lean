/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.FullPanLaw
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Observable invariants remain identifiable across zero-clock intervals -/

@[expose] public section

open Set
namespace Rhone.Statistics.Identifiability

set_option backward.isDefEq.respectTransparency false

noncomputable def PanPreModel.G {rate : ℝ → ℝ} (P : PanPreModel rate) : ℝ → ℝ :=
  fun t => P.D t + P.R t + P.U t

noncomputable def PanPreModel.Z {rate : ℝ → ℝ} (P : PanPreModel rate) : ℝ → ℝ :=
  fun t => (P.R t + 2 * P.D t) / Real.sqrt (P.D t)

noncomputable def PanPreModel.clockA {rate : ℝ → ℝ} (P : PanPreModel rate) : ℝ → ℝ :=
  fun t => rate t / Real.sqrt (P.D t)

noncomputable def PanPreModel.clockB {rate : ℝ → ℝ} (P : PanPreModel rate) : ℝ → ℝ :=
  fun t => rate t * Real.sqrt (P.D t)

theorem PanPreModel.G_initial {rate : ℝ → ℝ} (P : PanPreModel rate) : P.G 0 = 1 := by
  simp [G, P.initial]

theorem PanPreModel.Z_initial {rate : ℝ → ℝ} (P : PanPreModel rate) : P.Z 0 = 2 := by
  simp [Z, P.initial]

theorem PanPreModel.Z_nonneg {rate : ℝ → ℝ} (P : PanPreModel rate)
    {t : ℝ} (ht : 0 ≤ t) : 0 ≤ P.Z t := by
  exact div_nonneg (add_nonneg (P.R_nonneg t ht)
    (mul_nonneg (by norm_num) (P.D_positive t ht).le)) (Real.sqrt_nonneg _)

theorem PanPreModel.clockA_nonneg {rate : ℝ → ℝ} (P : PanPreModel rate)
    {t : ℝ} (hr : 0 ≤ rate t) : 0 ≤ P.clockA t := by
  exact div_nonneg hr (Real.sqrt_nonneg _)

theorem PanPreModel.G_derivative {rate : ℝ → ℝ} (P : PanPreModel rate)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt P.G (rate t * P.D t - 2 * rate t * P.G t) t := by
  rcases P.equations t ht with ⟨hd, hr, hu⟩
  convert! (hd.add hr).add hu using 1
  dsimp [G]
  ring

theorem PanPreModel.Z_derivative {rate : ℝ → ℝ} (P : PanPreModel rate)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt P.Z (-(7 / 2 : ℝ) * rate t * P.Z t +
      4 * P.clockA t * P.G t + 4 * P.clockB t - (1 / 2 : ℝ) * P.clockA t * (P.Z t)^2) t := by
  rcases P.equations t ht with ⟨hd, hr, _⟩
  have hs : Real.sqrt (P.D t) ≠ 0 := (Real.sqrt_pos.2 (P.D_positive t ht)).ne'
  have hs2 := Real.sq_sqrt (P.D_positive t ht).le
  convert! (hr.add (hd.const_mul 2)).div (hd.sqrt (P.D_positive t ht).ne') hs using 1
  dsimp [Z, clockA, clockB, G]
  generalize hsdef : Real.sqrt (P.D t) = s at *
  rw [← hs2]
  field_simp
  ring

theorem PanPreModel.logD_derivative {rate : ℝ → ℝ} (P : PanPreModel rate)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun x => Real.log (P.D x))
      (P.clockA t * P.Z t - 3 * rate t - 2 * P.recomb t) t := by
  have hs : Real.sqrt (P.D t) ≠ 0 := (Real.sqrt_pos.2 (P.D_positive t ht)).ne'
  have hs2 := Real.sq_sqrt (P.D_positive t ht).le
  convert! (P.equations t ht).1.log (P.D_positive t ht).ne' using 1
  dsimp [clockA, Z]
  generalize hsdef : Real.sqrt (P.D t) = s at *
  rw [← hs2]
  field_simp
  ring

theorem eqOn_halfline_of_difference_contracts (f g df dg : ℝ → ℝ)
    (hzero : f 0 = g 0)
    (hf : ∀ t, 0 ≤ t → HasDerivAt f (df t) t)
    (hg : ∀ t, 0 ≤ t → HasDerivAt g (dg t) t)
    (hcontract : ∀ t, 0 ≤ t → 2 * (f t - g t) * (df t - dg t) ≤ 0) :
    EqOn f g (Ici 0) := by
  have hderiv : ∀ t, 0 ≤ t →
      HasDerivAt (fun x => (f x - g x)^2) (2 * (f t - g t) * (df t - dg t)) t := by
    intro t ht
    convert! ((hf t ht).sub (hg t ht)).pow 2 using 1
    simp only [Pi.sub_apply]
    ring
  have ha : AntitoneOn (fun x => (f x - g x)^2) (Ici 0) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
      (fun t ht => (hderiv t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hderiv t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => hcontract t (interior_subset ht))
  intro t ht
  have hh := ha self_mem_Ici ht ht
  change (f t - g t)^2 ≤ (f 0 - g 0)^2 at hh
  rw [hzero, sub_self] at hh
  nlinarith

theorem pan_diagonal_flux_identifies_G (rate : ℝ → ℝ) (P Q : PanPreModel rate)
    (hr : ∀ t, 0 ≤ t → 0 ≤ rate t)
    (he : EqOn (fun t => rate t * P.D t) (fun t => rate t * Q.D t) (Ici 0)) :
    EqOn P.G Q.G (Ici 0) := by
  apply eqOn_halfline_of_difference_contracts P.G Q.G
    (fun t => rate t * P.D t - 2 * rate t * P.G t)
    (fun t => rate t * Q.D t - 2 * rate t * Q.G t)
    (P.G_initial.trans Q.G_initial.symm)
    (fun _ ht => P.G_derivative ht) (fun _ ht => Q.G_derivative ht)
  intro t ht
  have het : rate t * P.D t = rate t * Q.D t := he ht
  rw [het]
  have hnonneg := mul_nonneg (hr t ht) (sq_nonneg (P.G t - Q.G t))
  nlinarith

theorem pan_diagonal_flux_identifies_coefficients (rate : ℝ → ℝ) (P Q : PanPreModel rate)
    (he : EqOn (fun t => rate t * P.D t) (fun t => rate t * Q.D t) (Ici 0)) :
    EqOn P.clockA Q.clockA (Ici 0) ∧ EqOn P.clockB Q.clockB (Ici 0) := by
  have hpoint : ∀ t, 0 ≤ t → P.clockA t = Q.clockA t ∧ P.clockB t = Q.clockB t := by
    intro t ht
    by_cases hz : rate t = 0
    · simp [PanPreModel.clockA, PanPreModel.clockB, hz]
    · have hd := mul_left_cancel₀ hz (he ht)
      simp [PanPreModel.clockA, PanPreModel.clockB, hd]
  exact ⟨fun t ht => (hpoint t ht).1, fun t ht => (hpoint t ht).2⟩

theorem pan_diagonal_flux_identifies_G_Z (rate : ℝ → ℝ) (P Q : PanPreModel rate)
    (hr : ∀ t, 0 ≤ t → 0 ≤ rate t)
    (he : EqOn (fun t => rate t * P.D t) (fun t => rate t * Q.D t) (Ici 0)) :
    EqOn P.G Q.G (Ici 0) ∧ EqOn P.Z Q.Z (Ici 0) := by
  have hG := pan_diagonal_flux_identifies_G rate P Q hr he
  obtain ⟨hA, hB⟩ := pan_diagonal_flux_identifies_coefficients rate P Q he
  refine ⟨hG, ?_⟩
  apply eqOn_halfline_of_difference_contracts P.Z Q.Z
    (fun t => -(7 / 2 : ℝ) * rate t * P.Z t + 4 * P.clockA t * P.G t +
      4 * P.clockB t - (1 / 2 : ℝ) * P.clockA t * (P.Z t)^2)
    (fun t => -(7 / 2 : ℝ) * rate t * Q.Z t + 4 * Q.clockA t * Q.G t +
      4 * Q.clockB t - (1 / 2 : ℝ) * Q.clockA t * (Q.Z t)^2)
    (P.Z_initial.trans Q.Z_initial.symm)
    (fun _ ht => P.Z_derivative ht) (fun _ ht => Q.Z_derivative ht)
  intro t ht
  rw [hG ht, hA ht, hB ht]
  have hnonneg : 0 ≤ (7 * rate t + Q.clockA t * (P.Z t + Q.Z t)) * (P.Z t - Q.Z t)^2 :=
    mul_nonneg (add_nonneg (mul_nonneg (by norm_num) (hr t ht))
      (mul_nonneg (Q.clockA_nonneg (hr t ht))
        (add_nonneg (P.Z_nonneg ht) (Q.Z_nonneg ht)))) (sq_nonneg _)
  nlinarith

end Rhone.Statistics.Identifiability
