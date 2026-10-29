/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegrablePanObservableNecessity
public import Rhone.Statistics.Identifiability.PanDiagonalSufficiency

/-! # Identification of integrable pan rates and observables from the diagonal and marginals -/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability
set_option backward.isDefEq.respectTransparency false

theorem ae_nonneg_iff_ae_pos {p : ℝ → Prop} :
    (∀ᵐ t, 0 ≤ t → p t) ↔ (∀ᵐ t, 0 < t → p t) := by
  constructor
  · exact fun h => h.mono (fun _ ht hp => ht hp.le)
  · intro h
    filter_upwards [h, (show ∀ᵐ t : ℝ, t ≠ 0 from volume.ae_ne 0)] with t ht hn h0
    exact ht (lt_of_le_of_ne h0 (Ne.symm hn))

theorem regularJointLaw_diagonal_identifies_density_ae
    {d e : ℝ → ℝ} {j k : ℝ × ℝ → ℝ}
    (hd : AEMeasurable d (volume.restrict (Ioi 0)))
    (he : AEMeasurable e (volume.restrict (Ioi 0)))
    (hdn : ∀ᵐ t ∂volume.restrict (Ioi 0), 0 ≤ d t)
    (hen : ∀ᵐ t ∂volume.restrict (Ioi 0), 0 ≤ e t)
    (h : (regularJointLaw d j).restrict timeDiagonal =
      (regularJointLaw e k).restrict timeDiagonal) :
    ∀ᵐ t, 0 ≤ t → d t = e t := by
  rw [regularJointLaw_restrict_diagonal, regularJointLaw_restrict_diagonal] at h
  have hm := congrArg (fun μ : Measure (ℝ × ℝ) => μ.map Prod.fst) h
  rw [diagonalDensityLaw_map_fst, diagonalDensityLaw_map_fst] at hm
  have ha := (withDensity_eq_iff_of_sigmaFinite hd.ennreal_ofReal he.ennreal_ofReal).mp hm
  have hr : d =ᵐ[volume.restrict (Ioi 0)] e := by
    filter_upwards [ha, hdn, hen] with t ht hdt het
    exact (ENNReal.ofReal_eq_ofReal_iff hdt het).mp ht
  apply ae_nonneg_iff_ae_pos.mpr
  exact (ae_restrict_iff' measurableSet_Ioi).mp hr

theorem integrable_conditionalPairLaw_identifies_clock
    {rate rate' : ℝ → ℝ}
    (hr : LocallyIntegrableOn rate (Ici 0) volume)
    (hs : LocallyIntegrableOn rate' (Ici 0) volume)
    (hrn : ∀ᵐ t, 0 ≤ t → 0 ≤ rate t)
    (hsn : ∀ᵐ t, 0 ≤ t → 0 ≤ rate' t)
    (h : conditionalPairLaw rate (integrablePanClock rate) 0 =
      conditionalPairLaw rate' (integrablePanClock rate') 0) :
    EqOn (integrablePanClock rate) (integrablePanClock rate') (Ici 0) ∧
      (∀ᵐ t, 0 ≤ t → rate t = rate' t) := by
  let S := fun t => Real.exp (-integrablePanClock rate t)
  let T := fun t => Real.exp (-integrablePanClock rate' t)
  have hSa (b : ℝ) : AbsolutelyContinuousOnInterval S 0 b :=
    ac_exp (integrablePanClock_ac hr 0 b).neg
  have hTa (b : ℝ) : AbsolutelyContinuousOnInterval T 0 b :=
    ac_exp (integrablePanClock_ac hs 0 b).neg
  have hSd : ∀ᵐ t, 0 ≤ t → HasDerivAt S (-(rate t * S t)) t := by
    filter_upwards [integrablePanClock_ae_hasDerivAt hr] with t ht ht0
    convert! (ht ht0).neg.exp using 1
    dsimp [S]
    ring
  have hTd : ∀ᵐ t, 0 ≤ t → HasDerivAt T (-(rate' t * T t)) t := by
    filter_upwards [integrablePanClock_ae_hasDerivAt hs] with t ht ht0
    convert! (ht ht0).neg.exp using 1
    dsimp [T]
    ring
  have hm (r : ℝ → ℝ) (hi : LocallyIntegrableOn r (Ici 0) volume) :
      AEMeasurable (fun t => r t * Real.exp (-integrablePanClock r t))
        (volume.restrict (Ioi 0)) :=
    (hi.aestronglyMeasurable.aemeasurable.mono_measure
      (Measure.restrict_mono Ioi_subset_Ici_self le_rfl)).mul
      ((Real.continuous_exp.comp (integrablePanClock_continuous hi).neg).measurable.aemeasurable)
  simp only [conditionalPairLaw, conditionalPairDensity, integrablePanClock_zero,
    zero_sub] at h
  have hd := (withDensity_eq_iff_of_sigmaFinite (hm rate hr).ennreal_ofReal
    (hm rate' hs).ennreal_ofReal).mp h
  have hflux : ∀ᵐ t, 0 ≤ t → rate t * S t = rate' t * T t := by
    apply ae_nonneg_iff_ae_pos.mpr
    have hn : ∀ᵐ t, 0 < t → 0 ≤ rate t ∧ 0 ≤ rate' t := by
      filter_upwards [hrn, hsn] with t ht hu ht0
      exact ⟨ht ht0.le, hu ht0.le⟩
    have hd' := (ae_restrict_iff' measurableSet_Ioi).mp hd
    filter_upwards [hd', hn] with t ht hn ht0
    exact (ENNReal.ofReal_eq_ofReal_iff
      (mul_nonneg (hn ht0).1 (Real.exp_pos _).le)
      (mul_nonneg (hn ht0).2 (Real.exp_pos _).le)).mp (ht ht0)
  have hST : EqOn S T (Ici 0) := by
    intro t ht
    change 0 ≤ t at ht
    have hS := ac_integral_eq_sub_ae (hSa t) (show ∀ᵐ x, x ∈ uIcc 0 t →
        HasDerivAt S (-(rate x * S x)) x from by
      filter_upwards [hSd] with x hx hm
      exact hx ((by simpa only [uIcc_of_le ht] using hm : x ∈ Icc 0 t).1))
    have hT := ac_integral_eq_sub_ae (hTa t) (show ∀ᵐ x, x ∈ uIcc 0 t →
        HasDerivAt T (-(rate' x * T x)) x from by
      filter_upwards [hTd] with x hx hm
      exact hx ((by simpa only [uIcc_of_le ht] using hm : x ∈ Icc 0 t).1))
    have hi : (∫ x in (0 : ℝ)..t, -(rate x * S x)) =
        ∫ x in (0 : ℝ)..t, -(rate' x * T x) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hflux] with x hx hm
      rw [hx ((by simpa only [uIoc_of_le ht] using hm : x ∈ Ioc 0 t).1.le)]
    rw [hS, hT] at hi
    simpa [S, T] using hi
  refine ⟨?_, ?_⟩
  · intro t ht
    exact neg_injective (Real.exp_injective (hST ht))
  · filter_upwards [hflux] with t ht ht0
    rw [hST ht0] at ht
    exact mul_right_cancel₀ (Real.exp_pos _).ne' (ht ht0)

theorem ProperIntegrablePanModel.marginals_identify_clock (P Q : ProperIntegrablePanModel)
    (h : P.pre.jointLaw.map Prod.fst = Q.pre.jointLaw.map Prod.fst) :
    EqOn (integrablePanClock P.rate) (integrablePanClock Q.rate) (Ici 0) ∧
      (∀ᵐ t, 0 ≤ t → P.rate t = Q.rate t) := by
  rw [P.jointLaw_map_fst, Q.jointLaw_map_fst] at h
  exact integrable_conditionalPairLaw_identifies_clock P.pre.rate_integrable
    Q.pre.rate_integrable P.pre.rate_nonneg Q.pre.rate_nonneg h

theorem IntegrablePanPreModel.diagonal_identifies_flux_ae
    {rate rate' : ℝ → ℝ} (P : IntegrablePanPreModel rate) (Q : IntegrablePanPreModel rate')
    (h : P.jointLaw.restrict timeDiagonal = Q.jointLaw.restrict timeDiagonal) :
    ∀ᵐ t, 0 ≤ t → P.diagonalDensity t = Q.diagonalDensity t :=
  regularJointLaw_diagonal_identifies_density_ae P.diagonalDensity_aemeasurable
    Q.diagonalDensity_aemeasurable P.diagonalDensity_nonneg_ae Q.diagonalDensity_nonneg_ae h

theorem integrable_pan_diagonal_identifies_observables
    {rate rate' : ℝ → ℝ} (P : IntegrablePanPreModel rate) (Q : IntegrablePanPreModel rate')
    (hr : ∀ᵐ t, 0 ≤ t → rate t = rate' t)
    (hd : ∀ᵐ t, 0 ≤ t → P.diagonalDensity t = Q.diagonalDensity t) :
    EqOn P.total Q.total (Ici 0) ∧ EqOn P.Z Q.Z (Ici 0) := by
  apply Q.observables_unique hd (fun _ ht => P.total_ac ht) (fun _ ht => P.Z_ac ht)
    P.total_zero P.Z_zero
  · filter_upwards [P.G_ae_hasDerivAt, hr] with t ht hrt ht0
    simpa only [← hrt ht0] using ht ht0
  · have hp : ∀ᵐ t, 0 ≤ t → P.diagonalDensity t = P.diagonalDensity t :=
      Filter.Eventually.of_forall (fun _ _ => rfl)
    filter_upwards [P.Z_observable_ae_hasDerivAt hp, hr] with t ht hrt ht0
    simpa only [integrablePanObservableA, ← hrt ht0] using ht ht0

theorem integrable_pan_diagonal_identifies_correctedLogD
    {rate rate' : ℝ → ℝ} (P : IntegrablePanPreModel rate) (Q : IntegrablePanPreModel rate')
    (hr : ∀ᵐ t, 0 ≤ t → rate t = rate' t)
    (hd : ∀ᵐ t, 0 ≤ t → P.diagonalDensity t = Q.diagonalDensity t) :
    EqOn (fun t => Real.log (P.D t) + 2 * P.exposure t)
      (fun t => Real.log (Q.D t) + 2 * Q.exposure t) (Ici 0) := by
  have hZ := (integrable_pan_diagonal_identifies_observables P Q hr hd).2
  have hp : ∀ᵐ t, 0 ≤ t → P.diagonalDensity t = P.diagonalDensity t :=
    Filter.Eventually.of_forall (fun _ _ => rfl)
  intro t ht
  change 0 ≤ t at ht
  dsimp only
  rw [← P.observable_integral_eq_logD_add_exposure hp ht,
    ← Q.observable_integral_eq_logD_add_exposure hd ht]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hr] with s hs hmem
  have hs0 : 0 ≤ s := (by simpa only [uIoc_of_le ht] using hmem : s ∈ Ioc 0 t).1.le
  simp only [integrablePanObservableA, hs hs0, hZ hs0]

theorem integrable_pan_diagonal_identifies_exposure_ae
    {rate rate' : ℝ → ℝ} (P : IntegrablePanPreModel rate) (Q : IntegrablePanPreModel rate')
    (hr : ∀ᵐ t, 0 ≤ t → rate t = rate' t)
    (hd : ∀ᵐ t, 0 ≤ t → P.diagonalDensity t = Q.diagonalDensity t) :
    ∀ᵐ t, 0 ≤ t → 0 < rate t → P.exposure t = Q.exposure t := by
  have hc := integrable_pan_diagonal_identifies_correctedLogD P Q hr hd
  filter_upwards [hr, hd] with t hrt hdt ht hp
  have hD : P.D t = Q.D t := by
    have he := hdt ht
    change rate t * P.D t = rate' t * Q.D t at he
    rw [← hrt ht] at he
    exact mul_left_cancel₀ hp.ne' he
  have he := hc ht
  dsimp only at he
  rw [hD] at he
  linarith

theorem ProperIntegrablePanModel.equal_law_identifies_rate_and_exposure
    (P Q : ProperIntegrablePanModel) (h : P.pre.jointLaw = Q.pre.jointLaw) :
    (∀ᵐ t, 0 ≤ t → P.rate t = Q.rate t) ∧
      (∀ᵐ t, 0 ≤ t → P.pre.diagonalDensity t = Q.pre.diagonalDensity t) ∧
      (∀ᵐ t, 0 ≤ t → 0 < P.rate t → P.pre.exposure t = Q.pre.exposure t) := by
  have hr := (P.marginals_identify_clock Q (congrArg (fun μ => μ.map Prod.fst) h)).2
  have hd := P.pre.diagonal_identifies_flux_ae Q.pre
    (congrArg (fun μ => μ.restrict timeDiagonal) h)
  exact ⟨hr, hd, integrable_pan_diagonal_identifies_exposure_ae P.pre Q.pre hr hd⟩

end Rhone.Statistics.Identifiability
