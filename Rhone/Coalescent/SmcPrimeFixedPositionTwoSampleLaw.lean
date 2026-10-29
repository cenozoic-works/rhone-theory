/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeFixedPositionTwoSampleKernel
public import Rhone.Coalescent.SmcPrimeFixedPositionTwoSampleProposal
public import Rhone.Coalescent.SmcPrimeReferenceCutKernel
public import Rhone.Coalescent.SmcPrimeProposalLengthMean
public import Rhone.Coalescent.SmcSupport.HistoryNoise

/-!
# Law of the root height after one SMC′ proposal on the two-sample tree

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/

@[expose] public section

namespace Rhone.Coalescent.SmcPrime
open MeasureTheory Set IntervalProcess
open scoped ENNReal

theorem lintegral_Ioo_ofReal_of_hasDerivAt {a b : ℝ} (hab : a ≤ b) {F f : ℝ → ℝ}
    (hF : ∀ x, HasDerivAt F (f x) x) (hf : Continuous f) (hnn : ∀ x ∈ Ioo a b, 0 ≤ f x) :
    ∫⁻ x in Ioo a b, ENNReal.ofReal (f x) = ENNReal.ofReal (F b - F a) := by
  have hint : IntegrableOn f (Ioo a b) :=
    (hf.integrableOn_Icc (a := a) (b := b)).mono_set Ioo_subset_Icc_self
  have hnn' : 0 ≤ᵐ[volume.restrict (Ioo a b)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx using hnn x hx
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn', ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hF x)
      (hf.intervalIntegrable _ _)]

theorem hasDerivAt_exp_affine (c b x : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (c * t + b)) (c * Real.exp (c * x + b)) x := by
  have h0 : HasDerivAt (fun t : ℝ => c * t + b) c x := by
    simpa using ((hasDerivAt_id' x).const_mul c).add_const b
  have h1 := h0.exp
  rwa [mul_comm] at h1

theorem hasDerivAt_exp_neg_two_mul_sub (a x : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (-(2 * (a - t))) / 2) (Real.exp (-(2 * (a - x)))) x := by
  have h0 : HasDerivAt (fun t : ℝ => Real.exp (2 * t + -(2 * a)) / 2)
      (2 * Real.exp (2 * x + -(2 * a)) / 2) x := (hasDerivAt_exp_affine 2 (-(2 * a)) x).div_const 2
  have hfe : (fun t : ℝ => Real.exp (-(2 * (a - t))) / 2) =
      fun t => Real.exp (2 * t + -(2 * a)) / 2 := by
    funext t
    rw [show 2 * t + -(2 * a) = -(2 * (a - t)) by ring]
  rw [hfe]
  exact h0.congr_deriv (by rw [show 2 * x + -(2 * a) = -(2 * (a - x)) by ring]; ring)

theorem setLIntegral_Ici_comp_add (φ : ℝ → ℝ≥0∞) (c s : ℝ) :
    ∫⁻ e in Ici c, φ (e + s) = ∫⁻ a in Ici (c + s), φ a := by
  rw [← lintegral_indicator measurableSet_Ici, ← lintegral_indicator measurableSet_Ici,
    ← lintegral_add_right_eq_self (fun a => (Ici (c + s)).indicator φ a) s]
  refine lintegral_congr fun e => ?_
  by_cases he : c ≤ e
  · rw [indicator_of_mem (mem_Ici.mpr he),
      indicator_of_mem (mem_Ici.mpr (by linarith : c + s ≤ e + s))]
  · rw [indicator_of_notMem (fun hc => he (mem_Ici.mp hc)),
      indicator_of_notMem (fun hc => he (by have := mem_Ici.mp hc; linarith))]

theorem setLIntegral_Ioo_comp_half (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) (t d : ℝ) :
    ∫⁻ e in Ioo 0 (2 * d), φ (t + e / 2) = 2 * ∫⁻ a in Ioo t (t + d), φ a := by
  have hk : Measurable ((Ioo t (t + d)).indicator φ) := hφ.indicator measurableSet_Ioo
  have h1 : ∫⁻ e in Ioo 0 (2 * d), φ (t + e / 2) =
      ∫⁻ e, (Ioo t (t + d)).indicator φ (2⁻¹ * e + t) := by
    rw [← lintegral_indicator measurableSet_Ioo]
    refine lintegral_congr fun e => ?_
    have hiff : e ∈ Ioo 0 (2 * d) ↔ 2⁻¹ * e + t ∈ Ioo t (t + d) := by
      simp only [mem_Ioo]
      constructor <;> intro hh <;> constructor <;> linarith [hh.1, hh.2]
    have harg : 2⁻¹ * e + t = t + e / 2 := by ring
    by_cases he : e ∈ Ioo 0 (2 * d)
    · rw [indicator_of_mem he, indicator_of_mem (hiff.mp he), harg]
    · rw [indicator_of_notMem he, indicator_of_notMem (fun hc => he (hiff.mpr hc))]
  have h2 : ∫⁻ e, (Ioo t (t + d)).indicator φ (2⁻¹ * e + t) =
      2 * ∫⁻ y, (Ioo t (t + d)).indicator φ (y + t) := by
    have hmap := Real.map_volume_mul_left (a := (2⁻¹ : ℝ)) (by norm_num)
    have h3 : ∫⁻ e, (Ioo t (t + d)).indicator φ (2⁻¹ * e + t) =
        ∫⁻ y, (Ioo t (t + d)).indicator φ (y + t)
          ∂(Measure.map (fun x : ℝ => 2⁻¹ * x) volume) := by
      have hk' : Measurable fun y : ℝ => (Ioo t (t + d)).indicator φ (y + t) :=
        hk.comp (measurable_id.add_const t)
      rw [lintegral_map hk' (measurable_const_mul _)]
    rw [h3, hmap, lintegral_smul_measure]
    simp
  rw [h1, h2, lintegral_add_right_eq_self ((Ioo t (t + d)).indicator φ) t,
    lintegral_indicator measurableSet_Ioo]

theorem lintegral_unitUniform_comp_mul {h : ℝ} (hh : 0 < h) (φ : ℝ → ℝ≥0∞)
    (hφ : Measurable φ) :
    ∫⁻ u, φ (h * u) ∂unitUniform = ENNReal.ofReal h⁻¹ * ∫⁻ t in Ioo 0 h, φ t := by
  have hk : Measurable ((Ioo 0 h).indicator φ) := hφ.indicator measurableSet_Ioo
  have h1 : ∫⁻ u, φ (h * u) ∂unitUniform = ∫⁻ u, (Ioo 0 h).indicator φ (h * u) := by
    rw [unitUniform, ← lintegral_indicator measurableSet_Ioo]
    refine lintegral_congr fun u => ?_
    have hiff : u ∈ Ioo (0 : ℝ) 1 ↔ h * u ∈ Ioo 0 h := by
      simp only [mem_Ioo]
      constructor
      · intro hu
        exact ⟨mul_pos hh hu.1, by nlinarith [hu.2]⟩
      · intro hu
        refine ⟨?_, ?_⟩
        · by_contra hc
          have := mul_nonpos_of_nonneg_of_nonpos hh.le (not_lt.mp hc)
          linarith [hu.1]
        · by_contra hc
          have := mul_nonneg hh.le (sub_nonneg.mpr (not_lt.mp hc))
          nlinarith [hu.2]
    by_cases hu : u ∈ Ioo (0 : ℝ) 1
    · rw [indicator_of_mem hu, indicator_of_mem (hiff.mp hu)]
    · rw [indicator_of_notMem hu, indicator_of_notMem (fun hc => hu (hiff.mpr hc))]
  have hmap := Real.map_volume_mul_left (a := h) hh.ne'
  have h3 : ∫⁻ u, (Ioo 0 h).indicator φ (h * u) =
      ∫⁻ y, (Ioo 0 h).indicator φ y ∂(Measure.map (fun x : ℝ => h * x) volume) := by
    rw [lintegral_map hk (measurable_const_mul _)]
  rw [h1, h3, hmap, lintegral_smul_measure, lintegral_indicator measurableSet_Ioo,
    abs_of_pos (inv_pos.mpr hh)]
  rfl

theorem lintegral_unitUniform_comp_neg_log (ψ : ℝ → ℝ≥0∞) (hψ : Measurable ψ) :
    ∫⁻ u, ψ (-Real.log u) ∂unitUniform =
      ∫⁻ e in Ioi 0, ENNReal.ofReal (Real.exp (-e)) * ψ e := by
  have hmap := Rhone.Coalescent.SmcSupport.inverseClock_law 1 (by norm_num)
  simp only [div_one] at hmap
  have hpdf : Measurable (ProbabilityTheory.gammaPDF 1 1) :=
    (ProbabilityTheory.measurable_gammaPDFReal 1 1).ennreal_ofReal
  have hpt : ∀ x : ℝ, ProbabilityTheory.gammaPDF 1 1 x * ψ x =
      (Ici (0 : ℝ)).indicator (fun e => ENNReal.ofReal (Real.exp (-e)) * ψ e) x := by
    intro x
    rw [ProbabilityTheory.gammaPDF_eq]
    by_cases hx : 0 ≤ x
    · rw [indicator_of_mem (mem_Ici.mpr hx)]
      simp [hx, Real.Gamma_one]
    · rw [indicator_of_notMem (fun hc => hx (mem_Ici.mp hc))]
      simp [hx]
  have h1 : ∫⁻ u, ψ (-Real.log u) ∂unitUniform = ∫⁻ e, ψ e ∂ProbabilityTheory.expMeasure 1 := by
    rw [← hmap, lintegral_map hψ (by fun_prop)]
  rw [h1, ProbabilityTheory.expMeasure, ProbabilityTheory.gammaMeasure,
    lintegral_withDensity_eq_lintegral_mul _ hpdf hψ]
  simp only [Pi.mul_apply, hpt]
  rw [lintegral_indicator measurableSet_Ici, setLIntegral_congr Ioi_ae_eq_Ici.symm]

theorem twoSampleTargetClade_measurable : Measurable twoSampleTargetClade := by
  have he : twoSampleTargetClade = fun u => attachmentTarget (twoSampleTree 1) 0 u :=
    funext fun u => (twoSampleTree_attachmentTarget_below le_rfl one_pos u).symm
  rw [he]
  exact (attachmentTargetFiber_measurable 2 2).comp
    (measurable_const.prodMk (measurable_const.prodMk measurable_id))

theorem unitUniform_twoSampleTargetClade (i : Fin 2) :
    unitUniform {u | twoSampleTargetClade u = {i}} = 2⁻¹ := by
  have hlen : (Finset.univ : Finset (Fin 2)).toList.length = 2 := by
    rw [Finset.length_toList]
    rfl
  have hnd := Finset.nodup_toList (Finset.univ : Finset (Fin 2))
  have hform : ∃ x y : Fin 2, x ≠ y ∧ ∀ u : ℝ, u < 1 →
      twoSampleTargetClade u = if u * 2 < 1 then {x} else {y} := by
    unfold twoSampleTargetClade
    match hl : (Finset.univ : Finset (Fin 2)).toList, hlen, hnd with
    | [x, y], _, hnd' =>
      refine ⟨x, y, by simpa using hnd', fun u hu => ?_⟩
      by_cases h1 : u * 2 < 1
      · simp [chooseByRate, h1]
      · have h2 : u * 2 - 1 < 1 := by linarith
        simp [chooseByRate, h1, h2]
  obtain ⟨x, y, hxy, hf⟩ := hform
  have hsing : ∀ a b : Fin 2, ({a} : Finset (Fin 2)) = {b} ↔ a = b := fun a b =>
    Finset.singleton_inj
  have hi : i = x ∨ i = y :=
    (by decide : ∀ i x y : Fin 2, x ≠ y → i = x ∨ i = y) i x y hxy
  have hhalf : ENNReal.ofReal (2⁻¹ : ℝ) = 2⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos (by norm_num)]
    simp
  rw [unitUniform, Measure.restrict_apply' measurableSet_Ioo]
  rcases hi with rfl | rfl
  · have hset : {u | twoSampleTargetClade u = {i}} ∩ Ioo 0 1 = Ioo 0 2⁻¹ := by
      ext u
      simp only [mem_inter_iff, mem_ofPred_eq, mem_Ioo]
      constructor
      · rintro ⟨hu, h0, h1⟩
        rw [hf u h1] at hu
        refine ⟨h0, ?_⟩
        by_contra hc
        have hc' : ¬ u * 2 < 1 := fun h => hc (by linarith)
        simp only [hc', ↓reduceIte, hsing] at hu
        exact hxy hu.symm
      · rintro ⟨h0, h1⟩
        have h1' : u < 1 := by linarith
        refine ⟨?_, h0, h1'⟩
        have hlt : u * 2 < 1 := by linarith
        rw [hf u h1']
        simp only [hlt, ↓reduceIte]
    rw [hset, Real.volume_Ioo, sub_zero, hhalf]
  · have hset : {u | twoSampleTargetClade u = {i}} ∩ Ioo 0 1 = Ico 2⁻¹ 1 := by
      ext u
      simp only [mem_inter_iff, mem_ofPred_eq, mem_Ioo, mem_Ico]
      constructor
      · rintro ⟨hu, h0, h1⟩
        rw [hf u h1] at hu
        refine ⟨?_, h1⟩
        by_contra hc
        have hc' : u * 2 < 1 := by linarith [not_le.mp hc]
        simp only [hc', ↓reduceIte, hsing] at hu
        exact hxy hu
      · rintro ⟨h0, h1⟩
        refine ⟨?_, by linarith, h1⟩
        have hlt : ¬ u * 2 < 1 := by linarith
        rw [hf u h1]
        simp only [hlt, ↓reduceIte]
    rw [hset, Real.volume_Ico, show (1 : ℝ) - 2⁻¹ = 2⁻¹ by norm_num, hhalf]

theorem lintegral_twoSampleTargetClade_ite (i : Fin 2) (x y : ℝ≥0∞) :
    ∫⁻ u, (if twoSampleTargetClade u = {i} then x else y) ∂unitUniform =
      2⁻¹ * x + 2⁻¹ * y := by
  have hS : MeasurableSet {u | twoSampleTargetClade u = {i}} :=
    measurableSet_eq_fun twoSampleTargetClade_measurable measurable_const
  have hmass := unitUniform_twoSampleTargetClade i
  have hcompl : unitUniform {u | twoSampleTargetClade u = {i}}ᶜ = 2⁻¹ := by
    rw [prob_compl_eq_one_sub hS, hmass]
    exact ENNReal.one_sub_inv_two
  rw [← lintegral_add_compl _ hS]
  have h1 : ∫⁻ u in {u | twoSampleTargetClade u = {i}},
      (if twoSampleTargetClade u = {i} then x else y) ∂unitUniform =
      ∫⁻ _ in {u | twoSampleTargetClade u = {i}}, x ∂unitUniform :=
    setLIntegral_congr_fun hS fun u hu => by
      have hu' : twoSampleTargetClade u = {i} := hu
      simp only [hu', ↓reduceIte]
  have h2 : ∫⁻ u in {u | twoSampleTargetClade u = {i}}ᶜ,
      (if twoSampleTargetClade u = {i} then x else y) ∂unitUniform =
      ∫⁻ _ in {u | twoSampleTargetClade u = {i}}ᶜ, y ∂unitUniform :=
    setLIntegral_congr_fun hS.compl fun u hu => by
      have hu' : ¬ twoSampleTargetClade u = {i} := hu
      simp only [hu', ↓reduceIte]
  rw [h1, h2, setLIntegral_const, setLIntegral_const, hmass, hcompl, mul_comm x, mul_comm y]

theorem lintegral_budget_twoSample {h t : ℝ} (hth : t < h) (g : ℝ → ℝ≥0∞)
    (hg : Measurable g) :
    ∫⁻ e in Ioi 0, ENNReal.ofReal (Real.exp (-e)) *
        (if e < 2 * (h - t) then 2⁻¹ * g h + 2⁻¹ * g (t + e / 2)
          else g (h + (e - 2 * (h - t)))) =
      2⁻¹ * g h * ENNReal.ofReal (1 - Real.exp (-(2 * (h - t)))) +
        (∫⁻ a in Ioo t h, ENNReal.ofReal (Real.exp (-(2 * (a - t)))) * g a) +
        ENNReal.ofReal (Real.exp (-(2 * (h - t)))) *
          ∫⁻ a in Ici h, ENNReal.ofReal (Real.exp (-(a - h))) * g a := by
  have hd : 0 < 2 * (h - t) := by linarith
  have hsplit : Ioi (0 : ℝ) = Ioo 0 (2 * (h - t)) ∪ Ici (2 * (h - t)) :=
    (Ioo_union_Ici_eq_Ioi hd).symm
  have hdisj : Disjoint (Ioo 0 (2 * (h - t))) (Ici (2 * (h - t))) :=
    Set.disjoint_left.mpr fun x hx hx' => not_lt.mpr hx' hx.2
  have hexp : Measurable (fun e : ℝ => ENNReal.ofReal (Real.exp (-e))) := by fun_prop
  have hbelow : ∫⁻ e in Ioo 0 (2 * (h - t)), ENNReal.ofReal (Real.exp (-e)) *
        (if e < 2 * (h - t) then 2⁻¹ * g h + 2⁻¹ * g (t + e / 2)
          else g (h + (e - 2 * (h - t)))) =
      2⁻¹ * g h * ENNReal.ofReal (1 - Real.exp (-(2 * (h - t)))) +
        ∫⁻ a in Ioo t h, ENNReal.ofReal (Real.exp (-(2 * (a - t)))) * g a := by
    have hc : ∫⁻ e in Ioo 0 (2 * (h - t)), ENNReal.ofReal (Real.exp (-e)) *
          (if e < 2 * (h - t) then 2⁻¹ * g h + 2⁻¹ * g (t + e / 2)
            else g (h + (e - 2 * (h - t)))) =
        ∫⁻ e in Ioo 0 (2 * (h - t)), (2⁻¹ * g h * ENNReal.ofReal (Real.exp (-e)) +
          (fun a => ENNReal.ofReal (Real.exp (-(2 * (a - t)))) * (2⁻¹ * g a)) (t + e / 2)) :=
      setLIntegral_congr_fun measurableSet_Ioo fun e he => by
        have harg : -(2 * (t + e / 2 - t)) = -e := by ring
        simp only [he.2, ↓reduceIte, harg]
        ring
    have hmass : ∫⁻ e in Ioo 0 (2 * (h - t)), ENNReal.ofReal (Real.exp (-e)) =
        ENNReal.ofReal (1 - Real.exp (-(2 * (h - t)))) := by
      have hder : ∀ x : ℝ, HasDerivAt (fun e : ℝ => -1 * Real.exp (-1 * e + 0))
          (Real.exp (-x)) x := by
        intro x
        exact ((hasDerivAt_exp_affine (-1) 0 x).const_mul (-1)).congr_deriv
          (by rw [show (-1 : ℝ) * x + 0 = -x by ring]; ring)
      rw [lintegral_Ioo_ofReal_of_hasDerivAt hd.le hder (by fun_prop)
        (fun x _ => (Real.exp_pos _).le)]
      congr 1
      rw [show (-1 : ℝ) * (2 * (h - t)) + 0 = -(2 * (h - t)) by ring,
        show (-1 : ℝ) * 0 + 0 = 0 by ring, Real.exp_zero]
      ring
    have hφ : Measurable (fun a : ℝ =>
        ENNReal.ofReal (Real.exp (-(2 * (a - t)))) * (2⁻¹ * g a)) := by fun_prop
    rw [hc, lintegral_add_left (hexp.const_mul _),
      lintegral_const_mul _ hexp, hmass,
      setLIntegral_Ioo_comp_half _ hφ t (h - t)]
    congr 1
    have hth' : t + (h - t) = h := by ring
    rw [hth', ← lintegral_const_mul' _ _ (by norm_num)]
    refine lintegral_congr fun a => ?_
    rw [← mul_assoc, ← mul_assoc, mul_comm (2 : ℝ≥0∞), mul_assoc _ (2 : ℝ≥0∞),
      ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]
  have habove : ∫⁻ e in Ici (2 * (h - t)), ENNReal.ofReal (Real.exp (-e)) *
        (if e < 2 * (h - t) then 2⁻¹ * g h + 2⁻¹ * g (t + e / 2)
          else g (h + (e - 2 * (h - t)))) =
      ENNReal.ofReal (Real.exp (-(2 * (h - t)))) *
        ∫⁻ a in Ici h, ENNReal.ofReal (Real.exp (-(a - h))) * g a := by
    have hc : ∫⁻ e in Ici (2 * (h - t)), ENNReal.ofReal (Real.exp (-e)) *
          (if e < 2 * (h - t) then 2⁻¹ * g h + 2⁻¹ * g (t + e / 2)
            else g (h + (e - 2 * (h - t)))) =
        ∫⁻ e in Ici (2 * (h - t)),
          (fun a => ENNReal.ofReal (Real.exp (-(2 * (h - t)))) *
            (ENNReal.ofReal (Real.exp (-(a - h))) * g a)) (e + (h - 2 * (h - t))) :=
      setLIntegral_congr_fun measurableSet_Ici fun e he => by
        have hne : ¬ e < 2 * (h - t) := not_lt.mpr he
        have harg : e + (h - 2 * (h - t)) = h + (e - 2 * (h - t)) := by ring
        have hexp' : Real.exp (-e) =
            Real.exp (-(2 * (h - t))) * Real.exp (-(h + (e - 2 * (h - t)) - h)) := by
          rw [← Real.exp_add]
          congr 1
          ring
        simp only [hne, ↓reduceIte, harg]
        rw [hexp', ENNReal.ofReal_mul (Real.exp_pos _).le, mul_assoc]
    have hth' : 2 * (h - t) + (h - 2 * (h - t)) = h := by ring
    have hshift := setLIntegral_Ici_comp_add
      (fun a => ENNReal.ofReal (Real.exp (-(2 * (h - t)))) *
        (ENNReal.ofReal (Real.exp (-(a - h))) * g a)) (2 * (h - t)) (h - 2 * (h - t))
    rw [hth'] at hshift
    rw [hc]
    exact hshift.trans (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top)
  rw [hsplit, lintegral_union measurableSet_Ici hdisj, hbelow, habove]

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 3–7. -/
theorem twoSampleTree_proposal_rootHeight_lintegral (R : ℝ) {h : ℝ} (hh : 0 < h)
    (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ u, g (rootHeight (proposal R (twoSampleTree h) u).2.2) ∂proposalNoiseLaw =
      ENNReal.ofReal (twoSampleSelfMass h) * g h +
        ∫⁻ a in Ioi 0, ENNReal.ofReal (twoSampleJumpDensity h a) * g a := by
  let G : (ℝ × ℝ) × (ℝ × ℝ) → ℝ≥0∞ := fun p =>
    if -Real.log p.2.1 < 2 * (h - h * p.1.2) then
      (if twoSampleTargetClade p.2.2 = {if p.1.1 < 1 / 2 then (0 : Fin 2) else 1}
        then g h else g (h * p.1.2 + -Real.log p.2.1 / 2))
    else g (h + (-Real.log p.2.1 - 2 * (h - h * p.1.2)))
  have hidx : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      ({if p.1.1 < 1 / 2 then (0 : Fin 2) else 1} : Finset (Fin 2))) :=
    (measurable_of_finite (fun i : Fin 2 => ({i} : Finset (Fin 2)))).comp
      (Measurable.ite (measurableSet_lt (measurable_fst.comp measurable_fst) measurable_const)
        measurable_const measurable_const)
  have htgt : MeasurableSet {p : (ℝ × ℝ) × (ℝ × ℝ) |
      twoSampleTargetClade p.2.2 = {if p.1.1 < 1 / 2 then (0 : Fin 2) else 1}} :=
    measurableSet_eq_fun (twoSampleTargetClade_measurable.comp (by fun_prop)) hidx
  have hG : Measurable G :=
    Measurable.ite (measurableSet_lt (by fun_prop) (by fun_prop))
      (Measurable.ite htgt measurable_const (hg.comp (by fun_prop)))
      (hg.comp (by fun_prop))
  have hmarks : proposalNoiseLaw.map (fun u => ((u 1, u 2), (u 3, u 4))) =
      (unitUniform.prod unitUniform).prod (unitUniform.prod unitUniform) := by
    have hgr := proposalNoiseLaw_grouped
    have hcomp : (fun u : ProposalNoise => ((u 1, u 2), (u 3, u 4))) =
        Prod.snd ∘ fun u : ProposalNoise => (u 0, ((u 1, u 2), (u 3, u 4))) := rfl
    rw [hcomp, ← Measure.map_map measurable_snd (by fun_prop), hgr, Measure.map_snd_prod]
    simp
  have hae : (fun u : ProposalNoise => g (rootHeight (proposal R (twoSampleTree h) u).2.2))
      =ᵐ[proposalNoiseLaw] fun u => G ((u 1, u 2), (u 3, u 4)) := by
    filter_upwards [proposalNoiseLaw_ae_marks] with u hu
    rw [twoSampleTree_proposal_rootHeight R hh u hu]
    simp only [G]
    split_ifs <;> rfl
  rw [lintegral_congr_ae hae, ← lintegral_map hG (by fun_prop), hmarks,
    lintegral_prod _ hG.aemeasurable]
  have hinner : ∀ p : ℝ × ℝ, p.2 ∈ Ioo (0 : ℝ) 1 →
      ∫⁻ q, G (p, q) ∂unitUniform.prod unitUniform =
        ∫⁻ e in Ioi 0, ENNReal.ofReal (Real.exp (-e)) *
          (if e < 2 * (h - h * p.2) then 2⁻¹ * g h + 2⁻¹ * g (h * p.2 + e / 2)
            else g (h + (e - 2 * (h - h * p.2)))) := by
    intro p _
    have hGp : Measurable fun q : ℝ × ℝ => G (p, q) := hG.comp (by fun_prop)
    rw [lintegral_prod _ hGp.aemeasurable]
    have hq : ∀ u3 : ℝ, ∫⁻ u4, G (p, (u3, u4)) ∂unitUniform =
        (fun e => if e < 2 * (h - h * p.2) then 2⁻¹ * g h + 2⁻¹ * g (h * p.2 + e / 2)
          else g (h + (e - 2 * (h - h * p.2)))) (-Real.log u3) := by
      intro u3
      simp only [G]
      by_cases he : -Real.log u3 < 2 * (h - h * p.2)
      · simp only [he, ↓reduceIte]
        convert lintegral_twoSampleTargetClade_ite (if p.1 < 1 / 2 then 0 else 1) (g h)
          (g (h * p.2 + -Real.log u3 / 2))
      · simp only [he, ↓reduceIte, lintegral_const, measure_univ, mul_one]
    simp only [hq]
    have hψ : Measurable (fun e : ℝ =>
        if e < 2 * (h - h * p.2) then 2⁻¹ * g h + 2⁻¹ * g (h * p.2 + e / 2)
          else g (h + (e - 2 * (h - h * p.2)))) := by
      refine Measurable.ite (measurableSet_lt measurable_id measurable_const) ?_ ?_ <;> fun_prop
    exact lintegral_unitUniform_comp_neg_log _ hψ
  have hcut : ∀ᵐ p ∂unitUniform.prod unitUniform, p.2 ∈ Ioo (0 : ℝ) 1 := by
    have h2 : ∀ᵐ v ∂unitUniform, v ∈ Ioo (0 : ℝ) 1 := ae_restrict_mem measurableSet_Ioo
    exact (Measure.quasiMeasurePreserving_snd (μ := unitUniform) (ν := unitUniform)).ae h2
  rw [lintegral_congr_ae (hcut.mono fun p hp => hinner p hp)]
  have hΨ : Measurable (fun t : ℝ => ∫⁻ e in Ioi 0, ENNReal.ofReal (Real.exp (-e)) *
      (if e < 2 * (h - t) then 2⁻¹ * g h + 2⁻¹ * g (t + e / 2)
        else g (h + (e - 2 * (h - t))))) := by
    refine Measurable.lintegral_prod_right'
      (f := fun q : ℝ × ℝ => ENNReal.ofReal (Real.exp (-q.2)) *
        (if q.2 < 2 * (h - q.1) then 2⁻¹ * g h + 2⁻¹ * g (q.1 + q.2 / 2)
          else g (h + (q.2 - 2 * (h - q.1))))) ?_
    exact (by fun_prop : Measurable fun q : ℝ × ℝ => ENNReal.ofReal (Real.exp (-q.2))).mul
      (Measurable.ite (measurableSet_lt (by fun_prop) (by fun_prop))
        (measurable_const.add (measurable_const.mul (hg.comp (by fun_prop))))
        (hg.comp (by fun_prop)))
  have hfst : ∫⁻ p, (fun t : ℝ => ∫⁻ e in Ioi 0, ENNReal.ofReal (Real.exp (-e)) *
        (if e < 2 * (h - t) then 2⁻¹ * g h + 2⁻¹ * g (t + e / 2)
          else g (h + (e - 2 * (h - t))))) (h * p.2) ∂unitUniform.prod unitUniform =
      ∫⁻ u, (fun t : ℝ => ∫⁻ e in Ioi 0, ENNReal.ofReal (Real.exp (-e)) *
        (if e < 2 * (h - t) then 2⁻¹ * g h + 2⁻¹ * g (t + e / 2)
          else g (h + (e - 2 * (h - t))))) (h * u) ∂unitUniform := by
    have hm := hΨ.comp
      (by fun_prop : Measurable fun p : ℝ × ℝ => h * p.2)
    simp only [Function.comp_def] at hm
    rw [lintegral_prod _ hm.aemeasurable]
    simp only [lintegral_const, measure_univ, mul_one]
  rw [hfst, lintegral_unitUniform_comp_mul hh _ hΨ,
    setLIntegral_congr_fun measurableSet_Ioo
      (fun t ht => lintegral_budget_twoSample ht.2 g hg)]
  have e2 : Real.exp (-(2 * h)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have e3 := Real.add_one_le_exp (-(2 * h))
  have hI1 : ∫⁻ t in Ioo 0 h, ENNReal.ofReal (1 - Real.exp (-(2 * (h - t)))) =
      ENNReal.ofReal (h - (1 - Real.exp (-(2 * h))) / 2) := by
    have hder : ∀ x : ℝ, HasDerivAt (fun t : ℝ => t - Real.exp (-(2 * (h - t))) / 2)
        (1 - Real.exp (-(2 * (h - x)))) x := fun x =>
      (hasDerivAt_id' x).sub (hasDerivAt_exp_neg_two_mul_sub h x)
    rw [lintegral_Ioo_ofReal_of_hasDerivAt hh.le hder (by fun_prop) (fun x hx => by
      have : Real.exp (-(2 * (h - x))) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hx.2])
      linarith)]
    congr 1
    rw [sub_self, mul_zero, neg_zero, Real.exp_zero, sub_zero]
    ring
  have hI3 : ∀ a : ℝ, 0 ≤ a → ∫⁻ t in Ioo 0 a, ENNReal.ofReal (Real.exp (-(2 * (a - t)))) =
      ENNReal.ofReal ((1 - Real.exp (-(2 * a))) / 2) := by
    intro a ha
    rw [lintegral_Ioo_ofReal_of_hasDerivAt ha (hasDerivAt_exp_neg_two_mul_sub a)
      (by fun_prop) (fun x _ => (Real.exp_pos _).le)]
    congr 1
    rw [sub_self, mul_zero, neg_zero, Real.exp_zero, sub_zero]
    ring
  have hI2 : ∫⁻ t in Ioo 0 h, ∫⁻ a in Ioo t h,
        ENNReal.ofReal (Real.exp (-(2 * (a - t)))) * g a =
      ∫⁻ a in Ioo 0 h, ENNReal.ofReal ((1 - Real.exp (-(2 * a))) / 2) * g a := by
    have hW : Measurable (fun q : ℝ × ℝ => (Ioi q.1).indicator
        (fun a => ENNReal.ofReal (Real.exp (-(2 * (a - q.1)))) * g a) q.2) := by
      have hset : MeasurableSet {q : ℝ × ℝ | q.1 < q.2} :=
        measurableSet_lt measurable_fst measurable_snd
      have hbody : Measurable (fun q : ℝ × ℝ =>
          ENNReal.ofReal (Real.exp (-(2 * (q.2 - q.1)))) * g q.2) :=
        (by fun_prop : Measurable fun q : ℝ × ℝ =>
          ENNReal.ofReal (Real.exp (-(2 * (q.2 - q.1))))).mul (hg.comp measurable_snd)
      convert hbody.indicator hset using 1
      funext q
      by_cases hq : q.1 < q.2
      · rw [indicator_of_mem (mem_Ioi.mpr hq), indicator_of_mem (show q ∈ {q : ℝ × ℝ |
          q.1 < q.2} from hq)]
      · rw [indicator_of_notMem (fun hc => hq (mem_Ioi.mp hc)),
          indicator_of_notMem (show q ∉ {q : ℝ × ℝ | q.1 < q.2} from hq)]
    calc ∫⁻ t in Ioo 0 h, ∫⁻ a in Ioo t h,
          ENNReal.ofReal (Real.exp (-(2 * (a - t)))) * g a
        = ∫⁻ t in Ioo 0 h, ∫⁻ a in Ioo 0 h, (Ioi t).indicator
            (fun a => ENNReal.ofReal (Real.exp (-(2 * (a - t)))) * g a) a := by
          refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
          rw [lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi]
          congr 2
          ext a
          simp only [mem_inter_iff, mem_Ioi, mem_Ioo]
          constructor
          · intro ha
            exact ⟨ha.1, ht.1.trans ha.1, ha.2⟩
          · intro ha
            exact ⟨ha.1, ha.2.2⟩
      _ = ∫⁻ a in Ioo 0 h, ∫⁻ t in Ioo 0 h, (Ioi t).indicator
            (fun a => ENNReal.ofReal (Real.exp (-(2 * (a - t)))) * g a) a :=
          lintegral_lintegral_swap hW.aemeasurable
      _ = ∫⁻ a in Ioo 0 h, ENNReal.ofReal ((1 - Real.exp (-(2 * a))) / 2) * g a := by
          refine setLIntegral_congr_fun measurableSet_Ioo fun a ha => ?_
          have hpt : ∀ t : ℝ, (Ioi t).indicator
              (fun a => ENNReal.ofReal (Real.exp (-(2 * (a - t)))) * g a) a =
              (Iio a).indicator
                (fun t => ENNReal.ofReal (Real.exp (-(2 * (a - t)))) * g a) t := by
            intro t
            by_cases hta : t < a
            · rw [indicator_of_mem (mem_Ioi.mpr hta), indicator_of_mem (mem_Iio.mpr hta)]
            · rw [indicator_of_notMem (fun hc => hta (mem_Ioi.mp hc)),
                indicator_of_notMem (fun hc => hta (mem_Iio.mp hc))]
          simp only [hpt]
          rw [lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
          have hset : Iio a ∩ Ioo 0 h = Ioo 0 a := by
            ext t
            simp only [mem_inter_iff, mem_Iio, mem_Ioo]
            constructor
            · intro ht
              exact ⟨ht.2.1, ht.1⟩
            · intro ht
              exact ⟨ht.2, ht.1, ht.2.trans ha.2⟩
          rw [hset, lintegral_mul_const _ (by fun_prop), hI3 a ha.1.le]
  have hk1 : ∫⁻ a in Ioo 0 h, ENNReal.ofReal (twoSampleJumpDensity h a) * g a =
      ENNReal.ofReal h⁻¹ *
        ∫⁻ a in Ioo 0 h, ENNReal.ofReal ((1 - Real.exp (-(2 * a))) / 2) * g a := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_congr_fun measurableSet_Ioo fun a ha => ?_
    rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_pos.mpr hh).le]
    simp only [twoSampleJumpDensity, ha.2, ↓reduceIte]
    congr 2
    field_simp
  have hk2 : ∫⁻ a in Ici h, ENNReal.ofReal (twoSampleJumpDensity h a) * g a =
      ENNReal.ofReal h⁻¹ * (ENNReal.ofReal ((1 - Real.exp (-(2 * h))) / 2) *
        ∫⁻ a in Ici h, ENNReal.ofReal (Real.exp (-(a - h))) * g a) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_congr_fun measurableSet_Ici fun a ha => ?_
    have hc : 0 ≤ (1 - Real.exp (-(2 * h))) / 2 := by linarith
    rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (inv_pos.mpr hh).le,
      ← ENNReal.ofReal_mul (mul_nonneg (inv_pos.mpr hh).le hc)]
    simp only [twoSampleJumpDensity, not_lt.mpr (mem_Ici.mp ha), ↓reduceIte]
    congr 2
    field_simp
  have hself : ENNReal.ofReal (twoSampleSelfMass h) * g h =
      ENNReal.ofReal h⁻¹ *
        (2⁻¹ * g h * ENNReal.ofReal (h - (1 - Real.exp (-(2 * h))) / 2)) := by
    have hnn : 0 ≤ h - (1 - Real.exp (-(2 * h))) / 2 := by linarith
    have h2 : (2⁻¹ : ℝ≥0∞) = ENNReal.ofReal 2⁻¹ := by
      rw [ENNReal.ofReal_inv_of_pos (by norm_num)]
      simp
    rw [h2, mul_comm (ENNReal.ofReal 2⁻¹ * g h), ← mul_assoc, ← mul_assoc,
      ← ENNReal.ofReal_mul (inv_pos.mpr hh).le, ← ENNReal.ofReal_mul
        (mul_nonneg (inv_pos.mpr hh).le hnn)]
    congr 2
    unfold twoSampleSelfMass
    field_simp
    ring
  have hexpm : Measurable (fun t : ℝ => ENNReal.ofReal (Real.exp (-(2 * (h - t))))) := by
    fun_prop
  have hsum1 : Measurable (fun t : ℝ =>
      2⁻¹ * g h * ENNReal.ofReal (1 - Real.exp (-(2 * (h - t))))) := by fun_prop
  have hsum2 : Measurable (fun t : ℝ => ∫⁻ a in Ioo t h,
      ENNReal.ofReal (Real.exp (-(2 * (a - t)))) * g a) := by
    have hW : Measurable (fun q : ℝ × ℝ => (Ioo q.1 h).indicator
        (fun a => ENNReal.ofReal (Real.exp (-(2 * (a - q.1)))) * g a) q.2) := by
      have hset : MeasurableSet {q : ℝ × ℝ | q.1 < q.2 ∧ q.2 < h} :=
        (measurableSet_lt measurable_fst measurable_snd).inter
          (measurableSet_lt measurable_snd measurable_const)
      have hbody : Measurable (fun q : ℝ × ℝ =>
          ENNReal.ofReal (Real.exp (-(2 * (q.2 - q.1)))) * g q.2) :=
        (by fun_prop : Measurable fun q : ℝ × ℝ =>
          ENNReal.ofReal (Real.exp (-(2 * (q.2 - q.1))))).mul (hg.comp measurable_snd)
      convert hbody.indicator hset using 1
      funext q
      by_cases hq : q.1 < q.2 ∧ q.2 < h
      · rw [indicator_of_mem (mem_Ioo.mpr hq), indicator_of_mem (show q ∈ {q : ℝ × ℝ |
          q.1 < q.2 ∧ q.2 < h} from hq)]
      · rw [indicator_of_notMem (fun hc => hq (mem_Ioo.mp hc)),
          indicator_of_notMem (show q ∉ {q : ℝ × ℝ | q.1 < q.2 ∧ q.2 < h} from hq)]
    have := Measurable.lintegral_prod_right' (ν := (volume : Measure ℝ)) hW
    convert this using 1
    funext t
    exact (lintegral_indicator measurableSet_Ioo _).symm
  have hm1 : Measurable (fun t : ℝ => ENNReal.ofReal (1 - Real.exp (-(2 * (h - t))))) := by
    fun_prop
  have hsplit : Ioi (0 : ℝ) = Ioo 0 h ∪ Ici h := (Ioo_union_Ici_eq_Ioi hh).symm
  have hdisj : Disjoint (Ioo 0 h) (Ici h) :=
    Set.disjoint_left.mpr fun x hx hx' => not_lt.mpr hx' hx.2
  have hsum12 : Measurable (fun t : ℝ =>
      2⁻¹ * g h * ENNReal.ofReal (1 - Real.exp (-(2 * (h - t)))) +
        ∫⁻ a in Ioo t h, ENNReal.ofReal (Real.exp (-(2 * (a - t)))) * g a) := hsum1.add hsum2
  rw [lintegral_add_left hsum12, lintegral_add_left hsum1,
    lintegral_const_mul _ hm1, hI1, hI2, lintegral_mul_const _ hexpm, hI3 h hh.le,
    hsplit, lintegral_union measurableSet_Ici hdisj, hk1, hk2, hself]
  ring

theorem twoSampleTree_proposal_lengthBiased_invariant (R : ℝ) (g : ℝ → ℝ≥0∞)
    (hg : Measurable g) :
    ∫⁻ h in Ioi 0, ENNReal.ofReal (h * Real.exp (-h)) *
        ∫⁻ u, g (rootHeight (proposal R (twoSampleTree h) u).2.2) ∂proposalNoiseLaw =
      ∫⁻ h in Ioi 0, ENNReal.ofReal (h * Real.exp (-h)) * g h := by
  rw [← twoSample_lengthBiased_invariant g hg]
  refine setLIntegral_congr_fun measurableSet_Ioi fun h hh => ?_
  rw [twoSampleTree_proposal_rootHeight_lintegral R hh g hg]

end Rhone.Coalescent.SmcPrime
