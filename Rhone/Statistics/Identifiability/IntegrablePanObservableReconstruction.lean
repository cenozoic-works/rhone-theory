/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegrablePanExistence
public import Rhone.Statistics.Identifiability.IntegrablePanLaw
public import Rhone.Statistics.Identifiability.IntegrablePanObservables
public import Rhone.Statistics.Identifiability.PanObservableReconstruction

/-! # Reconstruction from locally absolutely continuous observable paths -/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability

set_option backward.isDefEq.respectTransparency false

theorem ac_sqrt_of_pos {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hpos : ∀ t ∈ uIcc a b, 0 < f t) :
    AbsolutelyContinuousOnInterval (fun t => Real.sqrt (f t)) a b := by
  obtain ⟨m, hm, hmin⟩ := isCompact_uIcc.exists_isMinOn nonempty_uIcc hf.continuousOn
  obtain ⟨C, hC⟩ := hf.exists_bound
  have hdiff : ContDiffOn ℝ 1 Real.sqrt (Icc (f m) C) :=
    contDiffOn_id.sqrt (fun x hx => ne_of_gt ((hpos m hm).trans_le hx.1))
  obtain ⟨K, hK⟩ := hdiff.exists_lipschitzOnWith (by decide) (convex_Icc _ _) isCompact_Icc
  apply ac_comp_lipschitzOn f Real.sqrt (Icc (f m) C) hf hK
  intro t ht
  exact ⟨hmin ht, (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hC t ht)⟩

theorem reconstructed_masses_ac (D G Z : ℝ → ℝ)
    (hD : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval D 0 T)
    (hG : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval G 0 T)
    (hZ : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval Z 0 T)
    (hpos : ∀ t, 0 ≤ t → 0 < D t) :
    (∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval (reconstructedR D Z) 0 T) ∧
      (∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval (reconstructedU D G Z) 0 T) := by
  have hs (T : ℝ) (hT : 0 ≤ T) :
      AbsolutelyContinuousOnInterval (fun t => Real.sqrt (D t)) 0 T := by
    apply ac_sqrt_of_pos (hD T hT)
    intro t ht
    exact hpos t ((by simpa only [uIcc_of_le hT, mem_Icc] using ht : 0 ≤ t ∧ t ≤ T).1)
  constructor
  · intro T hT
    exact ((hZ T hT).fun_mul (hs T hT)).sub ((hD T hT).const_mul 2)
  · intro T hT
    exact ((hG T hT).fun_add (hD T hT)).sub ((hZ T hT).fun_mul (hs T hT))

theorem integrable_pan_observables_reconstruct_equations (rate recomb D G Z : ℝ → ℝ)
    (hD : ∀ t, 0 ≤ t → 0 < D t)
    (hd : ∀ᵐ t, 0 ≤ t → HasDerivAt D
      ((rate t / Real.sqrt (D t) * Z t - 3 * rate t - 2 * recomb t) * D t) t)
    (hg : ∀ᵐ t, 0 ≤ t → HasDerivAt G (rate t * D t - 2 * rate t * G t) t)
    (hz : ∀ᵐ t, 0 ≤ t → HasDerivAt Z (-(7 / 2 : ℝ) * rate t * Z t +
      4 * (rate t / Real.sqrt (D t)) * G t + 4 * (rate t * Real.sqrt (D t)) -
      (1 / 2 : ℝ) * (rate t / Real.sqrt (D t)) * (Z t) ^ 2) t) :
    IntegrablePanPreEquations rate recomb D (reconstructedR D Z) (reconstructedU D G Z) := by
  filter_upwards [hd, hg, hz] with t hdt hgt hzt ht
  obtain ⟨h₁, h₂, h₃⟩ := pan_observables_reconstruct_at rate recomb D G Z
    (hD t ht) (hdt ht) (hgt ht) (hzt ht)
  refine ⟨?_, h₂, h₃⟩
  convert h₁ using 1
  ring

theorem exists_integrablePanPreModel_of_observables (rate recomb D G Z : ℝ → ℝ)
    (hr : LocallyIntegrableOn rate (Ici 0) volume)
    (hρ : LocallyIntegrableOn recomb (Ici 0) volume)
    (hrn : ∀ᵐ t, 0 ≤ t → 0 ≤ rate t)
    (hρn : ∀ᵐ t, 0 ≤ t → 0 ≤ recomb t)
    (hDa : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval D 0 T)
    (hGa : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval G 0 T)
    (hZa : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval Z 0 T)
    (hD : ∀ t, 0 ≤ t → 0 < D t)
    (hD0 : D 0 = 1) (hG0 : G 0 = 1) (hZ0 : Z 0 = 2)
    (hd : ∀ᵐ t, 0 ≤ t → HasDerivAt D
      ((rate t / Real.sqrt (D t) * Z t - 3 * rate t - 2 * recomb t) * D t) t)
    (hg : ∀ᵐ t, 0 ≤ t → HasDerivAt G (rate t * D t - 2 * rate t * G t) t)
    (hz : ∀ᵐ t, 0 ≤ t → HasDerivAt Z (-(7 / 2 : ℝ) * rate t * Z t +
      4 * (rate t / Real.sqrt (D t)) * G t + 4 * (rate t * Real.sqrt (D t)) -
      (1 / 2 : ℝ) * (rate t / Real.sqrt (D t)) * (Z t) ^ 2) t) :
    ∃ P : IntegrablePanPreModel rate, P.recomb = recomb ∧ P.D = D ∧
      P.R = reconstructedR D Z ∧ P.U = reconstructedU D G Z := by
  have ha := reconstructed_masses_ac D G Z hDa hGa hZa hD
  have he := integrable_pan_observables_reconstruct_equations rate recomb D G Z hD hd hg hz
  have hzero := reconstructed_masses_initial D G Z hD0 hG0 hZ0
  obtain ⟨Q, hQ⟩ := exists_integrablePanPreModel rate recomb hr hρ hrn hρn
  have hu := integrablePanPreEquations_unique rate recomb D (reconstructedR D Z)
    (reconstructedU D G Z) Q.D Q.R Q.U hr hρ hrn hρn hDa ha.1 ha.2 Q.D_ac Q.R_ac Q.U_ac
    he (by simpa only [hQ] using Q.equations)
    ⟨hzero.1.trans Q.initial.1.symm, hzero.2.1.trans Q.initial.2.1.symm,
      hzero.2.2.trans Q.initial.2.2.symm⟩
  refine ⟨{
    recomb := recomb
    D := D
    R := reconstructedR D Z
    U := reconstructedU D G Z
    rate_integrable := hr
    recomb_integrable := hρ
    rate_nonneg := hrn
    recomb_nonneg := hρn
    D_ac := hDa
    R_ac := ha.1
    U_ac := ha.2
    D_positive := hD
    R_nonneg := ?_
    U_nonneg := ?_
    initial := hzero
    equations := he }, rfl, rfl, rfl, rfl⟩
  · intro t ht
    rw [hu.2.1 ht]
    exact Q.R_nonneg t ht
  · intro t ht
    rw [hu.2.2 ht]
    exact Q.U_nonneg t ht

noncomputable def integrableObservableCorrection (rate a Z : ℝ → ℝ) : ℝ → ℝ :=
  integrablePanClock (fun t => a t * Z t - 3 * rate t)

noncomputable def integrableObservableDiagonal (rate a A Z : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (integrableObservableCorrection rate a Z t - 2 * A t)

theorem integrableObservableCorrection_integrand_locallyIntegrable
    (rate a Z : ℝ → ℝ)
    (hr : LocallyIntegrableOn rate (Ici 0) volume)
    (ha : LocallyIntegrableOn a (Ici 0) volume)
    (hZa : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval Z 0 T) :
    LocallyIntegrableOn (fun t => a t * Z t - 3 * rate t) (Ici 0) volume :=
  (ha.mul_continuousOn (halfLineAC_continuousOn hZa) isClosed_Ici.isLocallyClosed).sub
    (hr.smul (3 : ℝ))

@[simp] theorem integrableObservableCorrection_zero (rate a Z : ℝ → ℝ) :
    integrableObservableCorrection rate a Z 0 = 0 := by
  simp [integrableObservableCorrection]

theorem integrableObservableDiagonal_pos (rate a A Z : ℝ → ℝ) (t : ℝ) :
    0 < integrableObservableDiagonal rate a A Z t := Real.exp_pos _

@[simp] theorem integrableObservableDiagonal_zero (rate a A Z : ℝ → ℝ)
    (hA : A 0 = 0) : integrableObservableDiagonal rate a A Z 0 = 1 := by
  simp [integrableObservableDiagonal, hA]

theorem integrableObservableDiagonal_ac (rate a A Z : ℝ → ℝ)
    (hr : LocallyIntegrableOn rate (Ici 0) volume)
    (ha : LocallyIntegrableOn a (Ici 0) volume)
    (hAa : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval A 0 T)
    (hZa : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval Z 0 T)
    {T : ℝ} (hT : 0 ≤ T) :
    AbsolutelyContinuousOnInterval (integrableObservableDiagonal rate a A Z) 0 T :=
  ac_exp ((integrablePanClock_ac
    (integrableObservableCorrection_integrand_locallyIntegrable rate a Z hr ha hZa)
      0 T).sub ((hAa T hT).const_mul 2))

theorem integrableObservableDiagonal_ae_hasDerivAt (rate recomb a A Z : ℝ → ℝ)
    (hr : LocallyIntegrableOn rate (Ici 0) volume)
    (ha : LocallyIntegrableOn a (Ici 0) volume)
    (hZa : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval Z 0 T)
    (hAd : ∀ᵐ t, 0 ≤ t → HasDerivAt A (recomb t) t) :
    ∀ᵐ t, 0 ≤ t → HasDerivAt (integrableObservableDiagonal rate a A Z)
      ((a t * Z t - 3 * rate t - 2 * recomb t) *
        integrableObservableDiagonal rate a A Z t) t := by
  have hi := integrableObservableCorrection_integrand_locallyIntegrable rate a Z hr ha hZa
  filter_upwards [integrablePanClock_ae_hasDerivAt hi, hAd] with t hJ hA ht
  convert ((hJ ht).sub ((hA ht).const_mul 2)).exp using 1
  · rfl
  · exact mul_comm (a t * Z t - 3 * rate t - 2 * recomb t) _

theorem exists_integrablePanPreModel_of_exposure (rate recomb a A G Z : ℝ → ℝ)
    (hr : LocallyIntegrableOn rate (Ici 0) volume)
    (hρ : LocallyIntegrableOn recomb (Ici 0) volume)
    (ha : LocallyIntegrableOn a (Ici 0) volume)
    (hrn : ∀ᵐ t, 0 ≤ t → 0 ≤ rate t)
    (hρn : ∀ᵐ t, 0 ≤ t → 0 ≤ recomb t)
    (hAa : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval A 0 T)
    (hGa : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval G 0 T)
    (hZa : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval Z 0 T)
    (hA0 : A 0 = 0) (hG0 : G 0 = 1) (hZ0 : Z 0 = 2)
    (hAd : ∀ᵐ t, 0 ≤ t → HasDerivAt A (recomb t) t)
    (haeq : ∀ᵐ t, 0 ≤ t → a t =
      rate t / Real.sqrt (integrableObservableDiagonal rate a A Z t))
    (hg : ∀ᵐ t, 0 ≤ t → HasDerivAt G
      (rate t * integrableObservableDiagonal rate a A Z t - 2 * rate t * G t) t)
    (hz : ∀ᵐ t, 0 ≤ t → HasDerivAt Z (-(7 / 2 : ℝ) * rate t * Z t +
      4 * a t * G t + 4 * (rate t * Real.sqrt (integrableObservableDiagonal rate a A Z t)) -
      (1 / 2 : ℝ) * a t * (Z t) ^ 2) t) :
    ∃ P : IntegrablePanPreModel rate, P.recomb = recomb ∧
      P.D = integrableObservableDiagonal rate a A Z ∧
      P.R = reconstructedR (integrableObservableDiagonal rate a A Z) Z ∧
      P.U = reconstructedU (integrableObservableDiagonal rate a A Z) G Z := by
  refine exists_integrablePanPreModel_of_observables rate recomb
    (integrableObservableDiagonal rate a A Z) G Z hr hρ hrn hρn
    (fun _ hT => integrableObservableDiagonal_ac rate a A Z hr ha hAa hZa hT)
    hGa hZa (fun t _ => integrableObservableDiagonal_pos rate a A Z t)
    (integrableObservableDiagonal_zero rate a A Z hA0) hG0 hZ0 ?_ hg ?_
  · filter_upwards [integrableObservableDiagonal_ae_hasDerivAt rate recomb a A Z hr ha hZa hAd,
      haeq] with t hd he ht
    simpa only [he ht] using hd ht
  · filter_upwards [hz, haeq] with t hz he ht
    simpa only [he ht] using hz ht

theorem sqrt_rate_diagonal_eq {r d D : ℝ} (hr : 0 ≤ r) (hd : d = r * D) :
    Real.sqrt (r * d) = r * Real.sqrt D := by
  rw [hd, ← mul_assoc, ← pow_two, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr]

theorem exists_integrablePanPreModel_of_observable_exposure
    (rate recomb delta a A G Z : ℝ → ℝ)
    (hr : LocallyIntegrableOn rate (Ici 0) volume)
    (hρ : LocallyIntegrableOn recomb (Ici 0) volume)
    (ha : LocallyIntegrableOn a (Ici 0) volume)
    (hrn : ∀ᵐ t, 0 ≤ t → 0 ≤ rate t)
    (hρn : ∀ᵐ t, 0 ≤ t → 0 ≤ recomb t)
    (hAa : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval A 0 T)
    (hGa : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval G 0 T)
    (hZa : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval Z 0 T)
    (hA0 : A 0 = 0) (hG0 : G 0 = 1) (hZ0 : Z 0 = 2)
    (hAd : ∀ᵐ t, 0 ≤ t → HasDerivAt A (recomb t) t)
    (hdelta : ∀ᵐ t, 0 ≤ t → delta t =
      rate t * integrableObservableDiagonal rate a A Z t)
    (haeq : ∀ᵐ t, 0 ≤ t → a t =
      rate t / Real.sqrt (integrableObservableDiagonal rate a A Z t))
    (hg : ∀ᵐ t, 0 ≤ t → HasDerivAt G (delta t - 2 * rate t * G t) t)
    (hz : ∀ᵐ t, 0 ≤ t → HasDerivAt Z
      (4 * a t * G t + 4 * Real.sqrt (rate t * delta t) -
        (7 / 2) * rate t * Z t - (a t / 2) * (Z t) ^ 2) t) :
    ∃ P : IntegrablePanPreModel rate, P.recomb = recomb ∧
      P.D = integrableObservableDiagonal rate a A Z ∧
      P.R = reconstructedR (integrableObservableDiagonal rate a A Z) Z ∧
      P.U = reconstructedU (integrableObservableDiagonal rate a A Z) G Z := by
  refine exists_integrablePanPreModel_of_exposure rate recomb a A G Z hr hρ ha hrn hρn
    hAa hGa hZa hA0 hG0 hZ0 hAd haeq ?_ ?_
  · filter_upwards [hg, hdelta] with t hgt hdt ht
    simpa only [hdt ht] using hgt ht
  · filter_upwards [hz, hdelta, hrn] with t hzt hdt hrt ht
    have hs := sqrt_rate_diagonal_eq (hrt ht) (hdt ht)
    convert hzt ht using 1
    rw [hs]
    ring

theorem regularJointLaw_congr_ae {δ₁ δ₂ : ℝ → ℝ} {j₁ j₂ : ℝ × ℝ → ℝ}
    (hd : δ₁ =ᵐ[volume.restrict (Ioi 0)] δ₂)
    (hj : j₁ =ᵐ[planeVolume.restrict upperWedge] j₂) :
    regularJointLaw δ₁ j₁ = regularJointLaw δ₂ j₂ := by
  have hd' : diagonalDensityLaw δ₁ = diagonalDensityLaw δ₂ := by
    unfold diagonalDensityLaw
    congr 1
    apply withDensity_congr_ae
    filter_upwards [hd] with t ht
    rw [ht]
  have hj' : triangularDensityLaw j₁ = triangularDensityLaw j₂ := by
    unfold triangularDensityLaw
    apply withDensity_congr_ae
    filter_upwards [hj] with p hp
    rw [hp]
  rw [regularJointLaw, regularJointLaw, hd', hj']

theorem integrablePan_reconstructed_jointLaw_eq {rate delta D G Z : ℝ → ℝ}
    (P : IntegrablePanPreModel rate) (j : ℝ × ℝ → ℝ)
    (hD : P.D = D) (hR : P.R = reconstructedR D Z) (hU : P.U = reconstructedU D G Z)
    (hdelta : ∀ᵐ t, 0 ≤ t → delta t = rate t * D t)
    (hj : ∀ᵐ p ∂planeVolume.restrict upperWedge,
      j p = (rate p.1 * G p.1 - delta p.1) * rate p.2 *
        Real.exp (integrablePanClock rate p.1 - integrablePanClock rate p.2)) :
    P.jointLaw = regularJointLaw delta j := by
  rw [P.jointLaw_eq_regular]
  apply regularJointLaw_congr_ae
  · filter_upwards [hdelta.filter_mono (ae_mono Measure.restrict_le_self),
      ae_restrict_mem measurableSet_Ioi] with t hd ht
    change rate t * P.D t = delta t
    rw [hD]
    exact (hd ht.le).symm
  · have hf : ∀ᵐ p ∂planeVolume, 0 ≤ p.1 → delta p.1 = rate p.1 * D p.1 :=
      Measure.quasiMeasurePreserving_fst.ae hdelta
    filter_upwards [hj, hf.filter_mono (ae_mono Measure.restrict_le_self),
      ae_restrict_mem upperWedge_open.measurableSet] with p hjp hdp hp
    rw [hjp, hdp hp.1.le]
    simp only [IntegrablePanPreModel.upperDensity, IntegrablePanPreModel.nonDiagonal,
      hR, hU, reconstructedR, reconstructedU]
    ring

end Rhone.Statistics.Identifiability
