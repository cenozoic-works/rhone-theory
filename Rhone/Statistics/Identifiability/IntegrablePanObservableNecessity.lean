/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegrablePanObservables
public import Rhone.Statistics.Identifiability.IntegrablePanLaw
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Observable necessity for locally integrable panmictic models -/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability

set_option backward.isDefEq.respectTransparency false

theorem ac_sqrt_of_positive_lower_bound {f : ℝ → ℝ} {a b c : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hc : 0 < c)
    (hlower : ∀ t ∈ uIcc a b, c ≤ f t) :
    AbsolutelyContinuousOnInterval (fun t => Real.sqrt (f t)) a b := by
  obtain ⟨C, hC⟩ := hf.exists_bound
  have hdiff : ContDiffOn ℝ 1 Real.sqrt (Icc c C) :=
    contDiffOn_id.sqrt (fun x hx => ne_of_gt (hc.trans_le hx.1))
  obtain ⟨K, hK⟩ := hdiff.exists_lipschitzOnWith (by decide) (convex_Icc _ _) isCompact_Icc
  apply ac_comp_lipschitzOn f Real.sqrt (Icc c C) hf hK
  intro t ht
  exact ⟨hlower t ht, (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hC t ht)⟩

theorem ac_log_of_positive_lower_bound {f : ℝ → ℝ} {a b c : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hc : 0 < c)
    (hlower : ∀ t ∈ uIcc a b, c ≤ f t) :
    AbsolutelyContinuousOnInterval (fun t => Real.log (f t)) a b := by
  obtain ⟨C, hC⟩ := hf.exists_bound
  have hdiff : ContDiffOn ℝ 1 Real.log (Icc c C) :=
    contDiffOn_id.log (fun x hx => ne_of_gt (hc.trans_le hx.1))
  obtain ⟨K, hK⟩ := hdiff.exists_lipschitzOnWith (by decide) (convex_Icc _ _) isCompact_Icc
  apply ac_comp_lipschitzOn f Real.log (Icc c C) hf hK
  intro t ht
  exact ⟨hlower t ht, (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hC t ht)⟩

noncomputable def integrablePanObservableA (rate delta : ℝ → ℝ) (t : ℝ) : ℝ :=
  if rate t = 0 then 0 else rate t / Real.sqrt (delta t / rate t)

namespace IntegrablePanPreModel
variable {rate : ℝ → ℝ} (P : IntegrablePanPreModel rate)

noncomputable def Z (t : ℝ) : ℝ := (P.R t + 2 * P.D t) / Real.sqrt (P.D t)

noncomputable def clockA (t : ℝ) : ℝ := rate t / Real.sqrt (P.D t)

noncomputable def clockB (t : ℝ) : ℝ := rate t * Real.sqrt (P.D t)

noncomputable def exposure : ℝ → ℝ := integrablePanClock P.recomb

noncomputable def correction : ℝ → ℝ :=
  integrablePanClock (fun t => P.clockA t * P.Z t - 3 * rate t)

@[simp] theorem Z_zero : P.Z 0 = 2 := by simp [Z, P.initial]
@[simp] theorem exposure_zero : P.exposure 0 = 0 := by simp [exposure]
@[simp] theorem correction_zero : P.correction 0 = 0 := by simp [correction]

theorem D_continuousOn : ContinuousOn P.D (Ici 0) := halfLineAC_continuousOn P.D_ac

theorem sqrtD_ac {T : ℝ} (hT : 0 ≤ T) :
    AbsolutelyContinuousOnInterval (fun t => Real.sqrt (P.D t)) 0 T := by
  obtain ⟨c, hc, hl⟩ := P.D_compact_lower_bound T
  exact ac_sqrt_of_positive_lower_bound (P.D_ac T hT) hc
    (by simpa only [uIcc_of_le hT] using hl)

theorem logD_ac {T : ℝ} (hT : 0 ≤ T) :
    AbsolutelyContinuousOnInterval (fun t => Real.log (P.D t)) 0 T := by
  obtain ⟨c, hc, hl⟩ := P.D_compact_lower_bound T
  exact ac_log_of_positive_lower_bound (P.D_ac T hT) hc
    (by simpa only [uIcc_of_le hT] using hl)

theorem Z_ac {T : ℝ} (hT : 0 ≤ T) : AbsolutelyContinuousOnInterval P.Z 0 T := by
  obtain ⟨c, hc, hl⟩ := P.D_compact_lower_bound T
  have hi := ac_inv_of_positive_lower_bound (P.sqrtD_ac hT) (Real.sqrt_pos.mpr hc)
    (fun t ht => Real.sqrt_le_sqrt (hl t (by simpa only [uIcc_of_le hT] using ht)))
  change AbsolutelyContinuousOnInterval (fun t => (P.R t + 2 * P.D t) / Real.sqrt (P.D t)) 0 T
  simpa only [div_eq_mul_inv] using
    ((P.R_ac T hT).fun_add ((P.D_ac T hT).const_mul 2)).fun_mul hi

theorem Z_continuousOn : ContinuousOn P.Z (Ici 0) :=
  halfLineAC_continuousOn (fun _ hT => P.Z_ac hT)

theorem Z_positive {t : ℝ} (ht : 0 ≤ t) : 0 < P.Z t :=
  div_pos (add_pos_of_nonneg_of_pos (P.R_nonneg t ht)
    (mul_pos (by norm_num) (P.D_positive t ht))) (Real.sqrt_pos.mpr (P.D_positive t ht))

theorem diagonalDensity_locallyIntegrable :
    LocallyIntegrableOn P.diagonalDensity (Ici 0) volume :=
  P.rate_integrable.mul_continuousOn P.D_continuousOn isClosed_Ici.isLocallyClosed

theorem clockA_locallyIntegrable : LocallyIntegrableOn P.clockA (Ici 0) volume := by
  have hi : ContinuousOn (fun t => (Real.sqrt (P.D t))⁻¹) (Ici 0) :=
    P.D_continuousOn.sqrt.inv₀ (fun t ht => (Real.sqrt_pos.mpr (P.D_positive t ht)).ne')
  change LocallyIntegrableOn (fun t => rate t / Real.sqrt (P.D t)) (Ici 0) volume
  simpa only [div_eq_mul_inv] using
    P.rate_integrable.mul_continuousOn hi isClosed_Ici.isLocallyClosed

theorem clockB_locallyIntegrable : LocallyIntegrableOn P.clockB (Ici 0) volume :=
  P.rate_integrable.mul_continuousOn P.D_continuousOn.sqrt isClosed_Ici.isLocallyClosed

theorem correction_integrand_locallyIntegrable :
    LocallyIntegrableOn (fun t => P.clockA t * P.Z t - 3 * rate t) (Ici 0) volume :=
  (P.clockA_locallyIntegrable.mul_continuousOn P.Z_continuousOn
    isClosed_Ici.isLocallyClosed).sub (P.rate_integrable.smul (3 : ℝ))

theorem exposure_ac (a b : ℝ) : AbsolutelyContinuousOnInterval P.exposure a b :=
  integrablePanClock_ac P.recomb_integrable a b

theorem exposure_monotoneOn : MonotoneOn P.exposure (Ici 0) :=
  integrablePanClock_monotoneOn P.recomb_integrable P.recomb_nonneg

theorem correction_ac (a b : ℝ) : AbsolutelyContinuousOnInterval P.correction a b :=
  integrablePanClock_ac P.correction_integrand_locallyIntegrable a b

theorem G_ae_hasDerivAt :
    ∀ᵐ t, 0 ≤ t → HasDerivAt P.total (P.diagonalDensity t - 2 * rate t * P.total t) t := by
  filter_upwards [P.total_ae_hasDerivAt] with t ht ht0
  convert! ht ht0 using 1
  dsimp [total, diagonalDensity]
  ring

theorem Z_ae_hasDerivAt :
    ∀ᵐ t, 0 ≤ t → HasDerivAt P.Z
      (4 * P.clockA t * P.total t + 4 * P.clockB t -
        (7 / 2) * rate t * P.Z t - (P.clockA t / 2) * (P.Z t) ^ 2) t := by
  filter_upwards [P.equations] with t ht ht0
  obtain ⟨hd, hr, _⟩ := ht ht0
  have hs : Real.sqrt (P.D t) ≠ 0 := (Real.sqrt_pos.mpr (P.D_positive t ht0)).ne'
  have hs2 := Real.sq_sqrt (P.D_positive t ht0).le
  convert! (hr.add (hd.const_mul 2)).div (hd.sqrt (P.D_positive t ht0).ne') hs using 1
  dsimp [Z, clockA, clockB, total]
  generalize hsdef : Real.sqrt (P.D t) = s at *
  rw [← hs2]
  field_simp
  ring

theorem logD_ae_hasDerivAt :
    ∀ᵐ t, 0 ≤ t → HasDerivAt (fun x => Real.log (P.D x))
      (P.clockA t * P.Z t - 3 * rate t - 2 * P.recomb t) t := by
  filter_upwards [P.equations] with t ht ht0
  have hs : Real.sqrt (P.D t) ≠ 0 := (Real.sqrt_pos.mpr (P.D_positive t ht0)).ne'
  have hs2 := Real.sq_sqrt (P.D_positive t ht0).le
  convert! (ht ht0).1.log (P.D_positive t ht0).ne' using 1
  dsimp [clockA, Z]
  generalize hsdef : Real.sqrt (P.D t) = s at *
  rw [← hs2]
  field_simp
  ring

theorem correctedLogD_ae_hasDerivAt :
    ∀ᵐ t, 0 ≤ t → HasDerivAt (fun x => Real.log (P.D x) + 2 * P.exposure x)
      (P.clockA t * P.Z t - 3 * rate t) t := by
  filter_upwards [P.logD_ae_hasDerivAt,
    integrablePanClock_ae_hasDerivAt P.recomb_integrable] with t hd hA ht0
  convert! (hd ht0).add ((hA ht0).const_mul 2) using 1
  ring

theorem correction_eq_logD_add_exposure {t : ℝ} (ht : 0 ≤ t) :
    P.correction t = Real.log (P.D t) + 2 * P.exposure t := by
  have he := ac_integral_eq_sub_ae ((P.logD_ac ht).fun_add ((P.exposure_ac 0 t).const_mul 2))
    (show ∀ᵐ s, s ∈ uIcc 0 t → HasDerivAt
      (fun x => Real.log (P.D x) + 2 * P.exposure x)
      (P.clockA s * P.Z s - 3 * rate s) s from by
        filter_upwards [P.correctedLogD_ae_hasDerivAt] with s hs hmem
        exact hs ((by simpa only [uIcc_of_le ht] using hmem : s ∈ Icc 0 t).1))
  rw [show P.correction t = ∫ s in (0 : ℝ)..t, P.clockA s * P.Z s - 3 * rate s from
    integrablePanClock_eq_integral _ ht]
  simpa only [P.initial.1, Real.log_one, P.exposure_zero, mul_zero, add_zero, sub_zero] using he

theorem observableA_eq_clockA_ae {delta : ℝ → ℝ}
    (hd : ∀ᵐ t, 0 ≤ t → delta t = P.diagonalDensity t) :
    ∀ᵐ t, 0 ≤ t → integrablePanObservableA rate delta t = P.clockA t := by
  filter_upwards [hd] with t hdt ht
  by_cases hr : rate t = 0
  · simp [integrablePanObservableA, clockA, hr]
  · have he : delta t / rate t = P.D t := by
      rw [hdt ht]
      dsimp [diagonalDensity]
      exact mul_div_cancel_left₀ (P.D t) hr
    simp only [integrablePanObservableA, ite_eq_right hr, he, clockA]

theorem sqrt_flux_eq_clockB_ae {delta : ℝ → ℝ}
    (hd : ∀ᵐ t, 0 ≤ t → delta t = P.diagonalDensity t) :
    ∀ᵐ t, 0 ≤ t → Real.sqrt (rate t * delta t) = P.clockB t := by
  filter_upwards [hd, P.rate_nonneg] with t hdt hrt ht
  rw [hdt ht]
  change Real.sqrt (rate t * (rate t * P.D t)) = rate t * Real.sqrt (P.D t)
  rw [show rate t * (rate t * P.D t) = (rate t) ^ 2 * P.D t by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (hrt ht)]

theorem diagonal_constraints_ae {delta : ℝ → ℝ}
    (hd : ∀ᵐ t, 0 ≤ t → delta t = P.diagonalDensity t) :
    ∀ᵐ t, 0 ≤ t → 0 ≤ delta t ∧ (delta t = 0 ↔ rate t = 0) := by
  filter_upwards [hd, P.rate_nonneg] with t hdt hrt ht
  rw [hdt ht]
  change 0 ≤ rate t * P.D t ∧ (rate t * P.D t = 0 ↔ rate t = 0)
  exact ⟨mul_nonneg (hrt ht) (P.D_positive t ht).le,
    mul_eq_zero.trans (or_iff_left (P.D_positive t ht).ne')⟩

theorem observable_coefficients_locallyIntegrable {delta : ℝ → ℝ}
    (hd : ∀ᵐ t, 0 ≤ t → delta t = P.diagonalDensity t) :
    LocallyIntegrableOn delta (Ici 0) volume ∧
    LocallyIntegrableOn (integrablePanObservableA rate delta) (Ici 0) volume ∧
    LocallyIntegrableOn (fun t => Real.sqrt (rate t * delta t)) (Ici 0) volume := by
  have hdi : LocallyIntegrableOn delta (Ici 0) volume := by
    apply LocallyIntegrableOn.congr _ P.diagonalDensity_locallyIntegrable
    change ∀ᵐ t ∂volume.restrict (Ici 0), _
    rw [ae_restrict_iff' measurableSet_Ici]
    exact hd.mono (fun _ h ht => (h ht).symm)
  have hai : LocallyIntegrableOn (integrablePanObservableA rate delta) (Ici 0) volume := by
    apply LocallyIntegrableOn.congr _ P.clockA_locallyIntegrable
    change ∀ᵐ t ∂volume.restrict (Ici 0), _
    rw [ae_restrict_iff' measurableSet_Ici]
    exact (P.observableA_eq_clockA_ae hd).mono (fun _ h ht => (h ht).symm)
  exact ⟨hdi, hai, sqrt_mul_locallyIntegrableOn P.rate_integrable hdi⟩

theorem observableA_nonneg_ae {delta : ℝ → ℝ}
    (hd : ∀ᵐ t, 0 ≤ t → delta t = P.diagonalDensity t) :
    ∀ᵐ t, 0 ≤ t → 0 ≤ integrablePanObservableA rate delta t := by
  filter_upwards [P.observableA_eq_clockA_ae hd, P.rate_nonneg] with t hat hrt ht
  rw [hat ht]
  exact div_nonneg (hrt ht) (Real.sqrt_nonneg _)

theorem G_observable_ae_hasDerivAt {delta : ℝ → ℝ}
    (hd : ∀ᵐ t, 0 ≤ t → delta t = P.diagonalDensity t) :
    ∀ᵐ t, 0 ≤ t → HasDerivAt P.total (delta t - 2 * rate t * P.total t) t := by
  filter_upwards [P.G_ae_hasDerivAt, hd] with t ht hdt ht0
  simpa only [hdt ht0] using ht ht0

theorem Z_observable_ae_hasDerivAt {delta : ℝ → ℝ}
    (hd : ∀ᵐ t, 0 ≤ t → delta t = P.diagonalDensity t) :
    ∀ᵐ t, 0 ≤ t → HasDerivAt P.Z
      (4 * integrablePanObservableA rate delta t * P.total t +
        4 * Real.sqrt (rate t * delta t) - (7 / 2) * rate t * P.Z t -
        (integrablePanObservableA rate delta t / 2) * (P.Z t) ^ 2) t := by
  filter_upwards [P.Z_ae_hasDerivAt, P.observableA_eq_clockA_ae hd,
    P.sqrt_flux_eq_clockB_ae hd] with t ht hat hbt ht0
  simpa only [hat ht0, hbt ht0] using ht ht0

theorem observable_integral_eq_logD_add_exposure {delta : ℝ → ℝ}
    (hd : ∀ᵐ t, 0 ≤ t → delta t = P.diagonalDensity t) {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t, integrablePanObservableA rate delta s * P.Z s - 3 * rate s) =
      Real.log (P.D t) + 2 * P.exposure t := by
  rw [← P.correction_eq_logD_add_exposure ht]
  change _ = integrablePanClock (fun s => P.clockA s * P.Z s - 3 * rate s) t
  rw [integrablePanClock_eq_integral _ ht]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [P.observableA_eq_clockA_ae hd] with s hs hmem
  rw [hs ((by simpa only [uIoc_of_le ht] using hmem : s ∈ Ioc 0 t).1.le)]

theorem observables_unique {delta G Z : ℝ → ℝ}
    (hd : ∀ᵐ t, 0 ≤ t → delta t = P.diagonalDensity t)
    (hGa : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval G 0 T)
    (hZa : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval Z 0 T)
    (hG0 : G 0 = 1) (hZ0 : Z 0 = 2)
    (hGd : ∀ᵐ t, 0 ≤ t → HasDerivAt G (delta t - 2 * rate t * G t) t)
    (hZd : ∀ᵐ t, 0 ≤ t → HasDerivAt Z
      (4 * integrablePanObservableA rate delta t * G t +
        4 * Real.sqrt (rate t * delta t) - (7 / 2) * rate t * Z t -
        (integrablePanObservableA rate delta t / 2) * (Z t) ^ 2) t) :
    EqOn G P.total (Ici 0) ∧ EqOn Z P.Z (Ici 0) := by
  have hG : ∀ t, 0 ≤ t → G t = P.total t :=
    integrable_observable_G_unique rate delta G P.total P.rate_integrable
      (halfLineAC_continuousOn hGa) (halfLineAC_continuousOn (fun _ ht => P.total_ac ht))
      hGa (fun _ ht => P.total_ac ht) hGd (P.G_observable_ae_hasDerivAt hd)
      (hG0.trans P.total_zero.symm)
  refine ⟨fun _ ht => hG _ ht, ?_⟩
  apply integrable_observable_Z_unique rate delta (integrablePanObservableA rate delta)
    P.total Z P.Z P.rate_integrable (P.observable_coefficients_locallyIntegrable hd).2.1
    (halfLineAC_continuousOn hZa) P.Z_continuousOn hZa (fun _ ht => P.Z_ac ht)
    _ (P.Z_observable_ae_hasDerivAt hd) (hZ0.trans P.Z_zero.symm)
  filter_upwards [hZd] with t ht ht0
  simpa only [hG t ht0] using ht ht0

theorem observable_solution_exposure_identity {delta G Z : ℝ → ℝ}
    (hd : ∀ᵐ t, 0 ≤ t → delta t = P.diagonalDensity t)
    (hGa : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval G 0 T)
    (hZa : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval Z 0 T)
    (hG0 : G 0 = 1) (hZ0 : Z 0 = 2)
    (hGd : ∀ᵐ t, 0 ≤ t → HasDerivAt G (delta t - 2 * rate t * G t) t)
    (hZd : ∀ᵐ t, 0 ≤ t → HasDerivAt Z
      (4 * integrablePanObservableA rate delta t * G t +
        4 * Real.sqrt (rate t * delta t) - (7 / 2) * rate t * Z t -
        (integrablePanObservableA rate delta t / 2) * (Z t) ^ 2) t)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t, integrablePanObservableA rate delta s * Z s - 3 * rate s) -
      2 * P.exposure t = Real.log (P.D t) := by
  have hZ := (P.observables_unique hd hGa hZa hG0 hZ0 hGd hZd).2
  have he : (∫ s in (0 : ℝ)..t, integrablePanObservableA rate delta s * Z s - 3 * rate s) =
      ∫ s in (0 : ℝ)..t, integrablePanObservableA rate delta s * P.Z s - 3 * rate s := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [] with s hs
    rw [hZ ((by simpa only [uIoc_of_le ht] using hs : s ∈ Ioc 0 t).1.le)]
  rw [he, P.observable_integral_eq_logD_add_exposure hd ht]
  ring

theorem observable_exposure_prescribed_ae {delta : ℝ → ℝ}
    (hd : ∀ᵐ t, 0 ≤ t → delta t = P.diagonalDensity t) :
    ∀ᵐ t, 0 ≤ t → 0 < rate t → P.exposure t =
      ((∫ s in (0 : ℝ)..t, integrablePanObservableA rate delta s * P.Z s - 3 * rate s) -
        Real.log (delta t / rate t)) / 2 := by
  filter_upwards [hd] with t hdt ht hr
  have he : delta t / rate t = P.D t := by
    rw [hdt ht]
    exact mul_div_cancel_left₀ (P.D t) hr.ne'
  rw [he, P.observable_integral_eq_logD_add_exposure hd ht]
  ring

theorem observable_necessity {delta : ℝ → ℝ}
    (hd : ∀ᵐ t, 0 ≤ t → delta t = P.diagonalDensity t) :
    LocallyIntegrableOn delta (Ici 0) volume ∧
    LocallyIntegrableOn (integrablePanObservableA rate delta) (Ici 0) volume ∧
    (∀ᵐ t, 0 ≤ t → 0 ≤ delta t ∧ (delta t = 0 ↔ rate t = 0)) ∧
    (∀ᵐ t, 0 ≤ t → 0 ≤ integrablePanObservableA rate delta t) ∧
    ∃ G Z : ℝ → ℝ, G 0 = 1 ∧ Z 0 = 2 ∧
      (∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval G 0 T) ∧
      (∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval Z 0 T) ∧
      (∀ t, 0 ≤ t → 0 < G t) ∧ (∀ t, 0 ≤ t → 0 < Z t) ∧
      (∀ᵐ t, 0 ≤ t → HasDerivAt G (delta t - 2 * rate t * G t) t) ∧
      (∀ᵐ t, 0 ≤ t → HasDerivAt Z
        (4 * integrablePanObservableA rate delta t * G t +
          4 * Real.sqrt (rate t * delta t) - (7 / 2) * rate t * Z t -
          (integrablePanObservableA rate delta t / 2) * (Z t) ^ 2) t) ∧
      (∀ t, 0 ≤ t →
        (∫ s in (0 : ℝ)..t, integrablePanObservableA rate delta s * Z s - 3 * rate s) -
          2 * P.exposure t = Real.log (P.D t)) := by
  refine ⟨(P.observable_coefficients_locallyIntegrable hd).1,
    (P.observable_coefficients_locallyIntegrable hd).2.1,
    P.diagonal_constraints_ae hd, P.observableA_nonneg_ae hd,
    P.total, P.Z, P.total_zero, P.Z_zero, (fun _ ht => P.total_ac ht),
    (fun _ ht => P.Z_ac ht), (fun _ ht => P.total_positive ht),
    (fun _ ht => P.Z_positive ht), P.G_observable_ae_hasDerivAt hd,
    P.Z_observable_ae_hasDerivAt hd, ?_⟩
  intro t ht
  rw [P.observable_integral_eq_logD_add_exposure hd ht]
  ring

end IntegrablePanPreModel
end Rhone.Statistics.Identifiability
