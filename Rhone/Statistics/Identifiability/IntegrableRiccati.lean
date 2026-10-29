/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegrableMarkovCoordinate
public import Rhone.Statistics.Identifiability.IntegrablePanRates

/-! # Positive Riccati evolution for locally integrable coefficients -/

@[expose] public section

open Set Filter MeasureTheory
open scoped BigOperators Topology NNReal
namespace Rhone.Statistics.Identifiability

set_option backward.isDefEq.respectTransparency false

theorem ac_inv_of_positive_lower_bound {f : ℝ → ℝ} {a b c : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hc : 0 < c)
    (hlower : ∀ t ∈ uIcc a b, c ≤ f t) :
    AbsolutelyContinuousOnInterval (fun t => (f t)⁻¹) a b := by
  obtain ⟨C, hC⟩ := hf.exists_bound
  have hdiff : ContDiffOn ℝ 1 (fun x : ℝ => x⁻¹) (Icc c C) :=
    contDiffOn_id.inv (fun x hx => ne_of_gt (hc.trans_le hx.1))
  obtain ⟨K, hK⟩ := hdiff.exists_lipschitzOnWith (by decide) (convex_Icc _ _) isCompact_Icc
  apply ac_comp_lipschitzOn f (fun x : ℝ => x⁻¹) (Icc c C) hf hK
  intro t ht
  exact ⟨hlower t ht, (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hC t ht)⟩

theorem ac_safe_quotient {f g : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (fun t => f t / max (g t) (1 / 2)) a b := by
  have hm : AbsolutelyContinuousOnInterval (fun t => max (g t) (1 / 2)) a b := by
    exact ac_comp_lipschitzOn g (fun x : ℝ => max x (1 / 2)) univ hg
      ((LipschitzWith.id.max (LipschitzWith.const (1 / 2))).lipschitzOnWith)
      (fun _ _ => mem_univ _)
  simpa only [div_eq_mul_inv, Pi.mul_apply] using
    hf.fun_mul (ac_inv_of_positive_lower_bound hm (by norm_num : (0 : ℝ) < 1 / 2)
      (fun t _ => le_max_right (g t) (1 / 2)))

def riccatiLinearization (q p r : ℝ) : Fin 2 → Fin 2 → ℝ :=
  ![![0, q], ![r, -p]]

theorem exists_integrable_riccati_solution (q p r : ℝ → ℝ)
    (hq : LocallyIntegrable q volume) (hp : LocallyIntegrable p volume)
    (hr : LocallyIntegrable r volume)
    (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t) (hrn : ∀ᵐ t, 0 ≤ t → 0 ≤ r t)
    (z₀ : ℝ) (hz₀ : 0 < z₀) :
    ∃ Z : ℝ → ℝ, Z 0 = z₀ ∧ Continuous Z ∧
      (∀ a b, AbsolutelyContinuousOnInterval Z a b) ∧
      (∀ t, 0 ≤ t → 0 < Z t) ∧
      (∀ᵐ t, 0 ≤ t → HasDerivAt Z (q t - p t * Z t - r t * (Z t) ^ 2) t) := by
  let Q : ℝ → Fin 2 → Fin 2 → ℝ := fun t => riccatiLinearization (q t) (p t) (r t)
  have hQi : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp only [Q, riccatiLinearization]
    · exact locallyIntegrable_const 0
    · exact hq
    · exact hr
    · exact hp.neg
  have hQ : ∀ᵐ t, 0 ≤ t → ∀ i j, i ≠ j → 0 ≤ Q t i j := by
    filter_upwards [hqn, hrn] with t hqt hrt ht i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Q, riccatiLinearization]
  obtain ⟨v, hv0, hvc, _, hvac, _, hve⟩ := exists_integrable_row_solution Q hQi ![1, z₀]
  have he : ∀ᵐ t, 0 ≤ t → ∀ j,
      HasDerivAt (fun s => v s j) (∑ i, v t i * Q t i j) t :=
    hve.mono (fun _ ht _ => ht)
  have hn := integrable_row_solution_nonneg Q v hQi hQ (fun t _ i => hvac 0 t i) he
    (fun i => by fin_cases i <;> simp [hv0, hz₀.le])
  have hX (t : ℝ) (ht : 0 ≤ t) : 1 ≤ v t 0 := by
    have h := integrable_row_coordinate_lower_bound Q v 0 hQ
      (fun t _ i => hvac 0 t i) he hn (hQi 0 0) ht
    simpa [Q, riccatiLinearization, hv0] using h
  have hY (t : ℝ) (ht : 0 ≤ t) : 0 < v t 1 :=
    integrable_row_coordinate_pos Q v 1 hQ (fun t _ i => hvac 0 t i) he hn
      (hQi 1 1) (by simpa [hv0] using hz₀) ht
  let Z : ℝ → ℝ := fun t => v t 1 / max (v t 0) (1 / 2)
  have hZeq (t : ℝ) (ht : 0 ≤ t) : Z t = v t 1 / v t 0 := by
    simp only [Z, max_eq_left (by linarith [hX t ht] : (1 : ℝ) / 2 ≤ v t 0)]
  have hvc₀ : Continuous (fun t => v t 0) := (continuous_apply 0).comp hvc
  have hvc₁ : Continuous (fun t => v t 1) := (continuous_apply 1).comp hvc
  refine ⟨Z, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [Z, hv0]
  · exact hvc₁.div (hvc₀.max continuous_const)
      (fun t => ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) (le_max_right _ _)))
  · exact fun a b => ac_safe_quotient (hvac a b 1) (hvac a b 0)
  · intro t ht
    rw [hZeq t ht]
    exact div_pos (hY t ht) (by linarith [hX t ht])
  · filter_upwards [hve] with t ht ht0
    have hx : v t 0 ≠ 0 := ne_of_gt (by linarith [hX t ht0])
    have hdX : HasDerivAt (fun s => v s 0) (r t * v t 1) t := by
      simpa [Q, riccatiLinearization, Fin.sum_univ_two, mul_comm] using ht 0
    have hdY : HasDerivAt (fun s => v s 1) (q t * v t 0 - p t * v t 1) t := by
      convert ht 1 using 1
      simp [Q, riccatiLinearization, Fin.sum_univ_two]
      ring
    have heq : Z =ᶠ[𝓝 t] (fun s => v s 1 / v s 0) := by
      filter_upwards [hvc₀.continuousAt.eventually (lt_mem_nhds
        (by linarith [hX t ht0] : (1 : ℝ) / 2 < v t 0))] with s hs
      simp only [Z, max_eq_left hs.le]
    convert! (hdY.div hdX hx).congr_of_eventuallyEq heq using 1
    rw [hZeq t ht0]
    field_simp

theorem exists_halfLine_integrable_riccati_solution (q p r : ℝ → ℝ)
    (hq : LocallyIntegrableOn q (Ici 0) volume)
    (hp : LocallyIntegrableOn p (Ici 0) volume)
    (hr : LocallyIntegrableOn r (Ici 0) volume)
    (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t) (hrn : ∀ᵐ t, 0 ≤ t → 0 ≤ r t)
    (z₀ : ℝ) (hz₀ : 0 < z₀) :
    ∃ Z : ℝ → ℝ, Z 0 = z₀ ∧ Continuous Z ∧
      (∀ a b, AbsolutelyContinuousOnInterval Z a b) ∧
      (∀ t, 0 ≤ t → 0 < Z t) ∧
      (∀ᵐ t, 0 ≤ t → HasDerivAt Z (q t - p t * Z t - r t * (Z t) ^ 2) t) := by
  have hq' : ∀ᵐ t, 0 ≤ t → 0 ≤ panZeroExtension q t := by
    filter_upwards [hqn] with t ht ht0
    simpa only [panZeroExtension_of_nonneg q ht0] using ht ht0
  have hr' : ∀ᵐ t, 0 ≤ t → 0 ≤ panZeroExtension r t := by
    filter_upwards [hrn] with t ht ht0
    simpa only [panZeroExtension_of_nonneg r ht0] using ht ht0
  obtain ⟨Z, hZ0, hZc, hZa, hZn, hZd⟩ := exists_integrable_riccati_solution
    (panZeroExtension q) (panZeroExtension p) (panZeroExtension r)
    (panZeroExtension_locallyIntegrable hq) (panZeroExtension_locallyIntegrable hp)
    (panZeroExtension_locallyIntegrable hr) hq' hr' z₀ hz₀
  refine ⟨Z, hZ0, hZc, hZa, hZn, ?_⟩
  filter_upwards [hZd] with t ht ht0
  simpa only [panZeroExtension_of_nonneg q ht0, panZeroExtension_of_nonneg p ht0,
    panZeroExtension_of_nonneg r ht0] using ht ht0

theorem integrable_riccati_solution_unique (q p r Z W : ℝ → ℝ)
    (hp : LocallyIntegrableOn p (Ici 0) volume)
    (hr : LocallyIntegrableOn r (Ici 0) volume)
    (hZc : ContinuousOn Z (Ici 0)) (hWc : ContinuousOn W (Ici 0))
    (hZa : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval Z 0 T)
    (hWa : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval W 0 T)
    (hZd : ∀ᵐ t, 0 ≤ t → HasDerivAt Z (q t - p t * Z t - r t * (Z t) ^ 2) t)
    (hWd : ∀ᵐ t, 0 ≤ t → HasDerivAt W (q t - p t * W t - r t * (W t) ^ 2) t)
    (hzero : Z 0 = W 0) : ∀ t, 0 ≤ t → Z t = W t := by
  let c : ℝ → ℝ := fun t => p t + r t * (Z t + W t)
  have hci : LocallyIntegrableOn c (Ici 0) volume :=
    hp.add (hr.mul_continuousOn (hZc.add hWc) isClosed_Ici.isLocallyClosed)
  let H : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, panZeroExtension c s
  have hce := panZeroExtension_locallyIntegrable hci
  intro T hT
  have hHa : AbsolutelyContinuousOnInterval H 0 T :=
    (LocallyIntegrablePeanoBaker.intervalIntegrable_of_locallyIntegrable hce 0
        T).absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hHd : ∀ᵐ t, t ∈ uIcc 0 T → HasDerivAt H (c t) t := by
    filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hce] with t ht hmem
    have ht0 : 0 ≤ t := (by simpa only [uIcc_of_le hT] using hmem : t ∈ Icc 0 T).1
    simpa only [H, panZeroExtension_of_nonneg c ht0] using ht 0
  have hdiff : ∀ᵐ t, t ∈ uIcc 0 T →
      HasDerivAt (fun t => Z t - W t) (-c t * (Z t - W t)) t := by
    filter_upwards [hZd, hWd] with t hzt hwt hmem
    have ht0 : 0 ≤ t := (by simpa only [uIcc_of_le hT] using hmem : t ∈ Icc 0 T).1
    convert! (hzt ht0).sub (hwt ht0) using 1
    dsimp [c]
    ring
  have heq := survival_clock_of_ac_forward_equation (fun t => Z t - W t) c H 0 T
    ((hZa T hT).fun_sub (hWa T hT)) hHa hdiff hHd
  rw [hzero, sub_self, zero_mul] at heq
  exact sub_eq_zero.mp heq

theorem sqrt_mul_locallyIntegrable {f g : ℝ → ℝ}
    (hf : LocallyIntegrable f volume) (hg : LocallyIntegrable g volume) :
    LocallyIntegrable (fun t => Real.sqrt (f t * g t)) volume := by
  have hfa : LocallyIntegrable (fun t => |f t|) volume := by
    simpa only [Real.norm_eq_abs] using (show LocallyIntegrable (fun t => ‖f t‖) volume from fun t
        => (hf t).norm)
  have hga : LocallyIntegrable (fun t => |g t|) volume := by
    simpa only [Real.norm_eq_abs] using (show LocallyIntegrable (fun t => ‖g t‖) volume from fun t
        => (hg t).norm)
  have hm : AEStronglyMeasurable (fun t => Real.sqrt (f t * g t)) volume :=
    (hf.aestronglyMeasurable.aemeasurable.mul
        hg.aestronglyMeasurable.aemeasurable).sqrt.aestronglyMeasurable
  apply ((hfa.add hga).smul (1 / 2 : ℝ)).mono hm
  filter_upwards [] with t
  change ‖Real.sqrt (f t * g t)‖ ≤ ‖(1 / 2 : ℝ) * (|f t| + |g t|)‖
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 / 2) * (|f t| + |g t|))]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have habs : f t * g t ≤ |f t| * |g t| := by
    simpa only [abs_mul] using le_abs_self (f t * g t)
  nlinarith [sq_nonneg (|f t| - |g t|)]

theorem sqrt_mul_locallyIntegrableOn {f g : ℝ → ℝ}
    (hf : LocallyIntegrableOn f (Ici 0) volume)
    (hg : LocallyIntegrableOn g (Ici 0) volume) :
    LocallyIntegrableOn (fun t => Real.sqrt (f t * g t)) (Ici 0) volume := by
  have hi := (sqrt_mul_locallyIntegrable (panZeroExtension_locallyIntegrable hf)
    (panZeroExtension_locallyIntegrable hg)).locallyIntegrableOn (Ici 0)
  apply LocallyIntegrableOn.congr _ hi
  change ∀ᵐ t ∂volume.restrict (Ici 0), _
  rw [ae_restrict_iff' measurableSet_Ici]
  filter_upwards [] with t ht
  simp only [panZeroExtension_of_nonneg f ht, panZeroExtension_of_nonneg g ht]

end Rhone.Statistics.Identifiability
