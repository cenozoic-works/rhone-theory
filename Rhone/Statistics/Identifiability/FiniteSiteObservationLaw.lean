/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegrablePanMutationMoments

/-! # The explicit stationary equal-rates observation model for two samples and two sites -/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Rhone.Statistics.Identifiability.FiniteSiteObservation

abbrev AllelePair (K : ℕ) := Fin K × Fin K
abbrev Observation (K : ℕ) := AllelePair K × AllelePair K

def limit (K : ℕ) : ℝ := ((K : ℝ) - 1) / K

noncomputable def difference (K : ℕ) (k t : ℝ) : ℝ :=
  limit K * (1 - Real.exp (-k * t))

def siteKernel (K : ℕ) (z : ℝ) (a : AllelePair K) : ℝ :=
  if a.1 = a.2 then (1-z) / K else z / ((K : ℝ) * ((K : ℝ)-1))

noncomputable def conditionalKernel (K : ℕ) (k : ℝ)
    (t : ℝ × ℝ) (a : Observation K) : ℝ :=
  siteKernel K (difference K k t.1) a.1 * siteKernel K (difference K k t.2) a.2

noncomputable def mass (K : ℕ) (k : ℝ) (μ : Measure (ℝ × ℝ))
    (a : Observation K) : ℝ := ∫ t, conditionalKernel K k t a ∂μ

noncomputable def law (K : ℕ) (k : ℝ) (μ : Measure (ℝ × ℝ)) :
    Measure (Observation K) :=
  Measure.sum fun a => ENNReal.ofReal (mass K k μ a) • Measure.dirac a

noncomputable def firstMoment (K : ℕ) (k : ℝ) (μ : Measure (ℝ × ℝ)) : ℝ :=
  ∫ t, difference K k t.1 ∂μ

noncomputable def secondMoment (K : ℕ) (k : ℝ) (μ : Measure (ℝ × ℝ)) : ℝ :=
  ∫ t, difference K k t.2 ∂μ

noncomputable def jointMoment (K : ℕ) (k : ℝ) (μ : Measure (ℝ × ℝ)) : ℝ :=
  ∫ t, difference K k t.1 * difference K k t.2 ∂μ

noncomputable def momentPair (K : ℕ) (k : ℝ) (μ : Measure (ℝ × ℝ)) : ℝ × ℝ :=
  (firstMoment K k μ, jointMoment K k μ)

def NonnegativeTimes (μ : Measure (ℝ × ℝ)) : Prop :=
  ∀ᵐ t ∂μ, 0 ≤ t.1 ∧ 0 ≤ t.2

lemma limit_bounds {K : ℕ} (hK : 2 ≤ K) : 0 ≤ limit K ∧ limit K ≤ 1 := by
  have h : (1 : ℝ) < K := by exact_mod_cast hK
  unfold limit
  constructor
  · exact div_nonneg (by linarith) (by linarith)
  · apply (div_le_one (by linarith : (0 : ℝ) < K)).2
    linarith

lemma difference_bounds {K : ℕ} {k t : ℝ} (hK : 2 ≤ K) (hk : 0 ≤ k)
    (ht : 0 ≤ t) : 0 ≤ difference K k t ∧ difference K k t ≤ 1 := by
  have he : Real.exp (-k*t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hp := (Real.exp_pos (-k*t)).le
  have hL := limit_bounds hK
  unfold difference
  constructor
  · exact mul_nonneg hL.1 (sub_nonneg.mpr he)
  · exact (mul_le_mul_of_nonneg_left (by linarith : 1 - Real.exp (-k*t) ≤ 1)
      hL.1).trans (by simpa using hL.2)

@[fun_prop] lemma difference_measurable (K : ℕ) (k : ℝ) : Measurable (difference K k) := by
  exact measurable_const.mul (measurable_const.sub
    (Real.measurable_exp.comp (measurable_const.mul measurable_id)))

lemma siteKernel_nonneg {K : ℕ} (hK : 2 ≤ K) {z : ℝ}
    (hz : 0 ≤ z ∧ z ≤ 1) (a : AllelePair K) : 0 ≤ siteKernel K z a := by
  have h : (1 : ℝ) < K := by exact_mod_cast hK
  unfold siteKernel
  split
  · exact div_nonneg (sub_nonneg.mpr hz.2) (by linarith)
  · exact div_nonneg hz.1 (mul_nonneg (by linarith) (by linarith))

lemma siteKernel_le_one {K : ℕ} (hK : 2 ≤ K) {z : ℝ}
    (hz : 0 ≤ z ∧ z ≤ 1) (a : AllelePair K) : siteKernel K z a ≤ 1 := by
  have h : (1 : ℝ) < K := by exact_mod_cast hK
  have h2 : (2 : ℝ) ≤ K := by exact_mod_cast hK
  unfold siteKernel
  split
  · apply (div_le_one (by linarith : (0 : ℝ) < K)).2
    linarith [hz.1]
  · apply (div_le_one (mul_pos (by linarith : (0 : ℝ) < K)
      (by linarith : (0 : ℝ) < (K : ℝ)-1))).2
    nlinarith [hz.2]

lemma siteKernel_sum {K : ℕ} (hK : 2 ≤ K) (z : ℝ) :
    ∑ a : AllelePair K, siteKernel K z a = 1 := by
  have h : (1 : ℝ) < K := by exact_mod_cast hK
  have hK0 : (K : ℝ) ≠ 0 := by linarith
  have hK1 : (K : ℝ)-1 ≠ 0 := by linarith
  have hex (a b : Fin K) : siteKernel K z (a,b) =
      z / ((K : ℝ) * ((K : ℝ)-1)) +
      if a = b then (1-z)/K - z / ((K : ℝ) * ((K : ℝ)-1)) else 0 := by
    unfold siteKernel
    split <;> simp_all
  rw [Fintype.sum_prod_type]
  simp_rw [hex]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  field_simp
  ring

lemma conditionalKernel_sum {K : ℕ} (hK : 2 ≤ K) (k : ℝ) (t : ℝ × ℝ) :
    ∑ a : Observation K, conditionalKernel K k t a = 1 := by
  simp only [conditionalKernel, Fintype.sum_prod_type, ← Finset.mul_sum,
    siteKernel_sum hK, mul_one]

lemma conditionalKernel_measurable (K : ℕ) (k : ℝ) (a : Observation K) :
    Measurable (fun t => conditionalKernel K k t a) := by
  unfold conditionalKernel siteKernel
  split <;> split <;>
    fun_prop

lemma conditionalKernel_bounds {K : ℕ} {k : ℝ} (hK : 2 ≤ K) (hk : 0 ≤ k)
    {t : ℝ × ℝ} (ht : 0 ≤ t.1 ∧ 0 ≤ t.2) (a : Observation K) :
    0 ≤ conditionalKernel K k t a ∧ conditionalKernel K k t a ≤ 1 := by
  have h1 := difference_bounds hK hk ht.1
  have h2 := difference_bounds hK hk ht.2
  exact ⟨mul_nonneg (siteKernel_nonneg hK h1 _) (siteKernel_nonneg hK h2 _),
    (mul_le_of_le_one_left (siteKernel_nonneg hK h2 _) (siteKernel_le_one hK h1 _)).trans
        (siteKernel_le_one hK h2 _)⟩

lemma conditionalKernel_integrable {K : ℕ} {k : ℝ} {μ : Measure (ℝ × ℝ)}
    [IsFiniteMeasure μ] (hK : 2 ≤ K) (hk : 0 ≤ k) (hμ : NonnegativeTimes μ)
    (a : Observation K) : Integrable (fun t => conditionalKernel K k t a) μ := by
  refine Integrable.of_bound (conditionalKernel_measurable K k a).aestronglyMeasurable 1 ?_
  filter_upwards [hμ] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (conditionalKernel_bounds hK hk ht a).1]
  exact (conditionalKernel_bounds hK hk ht a).2

lemma mass_nonneg {K : ℕ} {k : ℝ} {μ : Measure (ℝ × ℝ)}
    (hK : 2 ≤ K) (hk : 0 ≤ k) (hμ : NonnegativeTimes μ) (a : Observation K) :
    0 ≤ mass K k μ a := by
  apply integral_nonneg_of_ae
  filter_upwards [hμ] with t ht
  exact (conditionalKernel_bounds hK hk ht a).1

lemma mass_sum {K : ℕ} {k : ℝ} {μ : Measure (ℝ × ℝ)} [IsProbabilityMeasure μ]
    (hK : 2 ≤ K) (hk : 0 ≤ k) (hμ : NonnegativeTimes μ) :
    ∑ a : Observation K, mass K k μ a = 1 := by
  unfold mass
  rw [← integral_finsetSum _ (fun a _ => conditionalKernel_integrable hK hk hμ a)]
  simp_rw [conditionalKernel_sum hK]
  simp

lemma law_singleton (K : ℕ) (k : ℝ) (μ : Measure (ℝ × ℝ)) (a : Observation K) :
    law K k μ {a} = ENNReal.ofReal (mass K k μ a) := by
  simp [law, Pi.single_apply, mul_ite]

theorem law_probability {K : ℕ} {k : ℝ} {μ : Measure (ℝ × ℝ)}
    [IsProbabilityMeasure μ] (hK : 2 ≤ K) (hk : 0 ≤ k) (hμ : NonnegativeTimes μ) :
    IsProbabilityMeasure (law K k μ) := by
  constructor
  simp only [law, Measure.sum_apply _ MeasurableSet.univ, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one, tsum_fintype]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => mass_nonneg hK hk hμ a),
    mass_sum hK hk hμ, ENNReal.ofReal_one]

lemma first_observable_integrable {K : ℕ} {k : ℝ} {μ : Measure (ℝ × ℝ)}
    [IsFiniteMeasure μ] (hK : 2 ≤ K) (hk : 0 ≤ k) (hμ : NonnegativeTimes μ) :
    Integrable (fun t => difference K k t.1) μ := by
  refine Integrable.of_bound ((difference_measurable K k).comp
    measurable_fst).aestronglyMeasurable 1 ?_
  filter_upwards [hμ] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (difference_bounds hK hk ht.1).1]
  exact (difference_bounds hK hk ht.1).2

lemma second_observable_integrable {K : ℕ} {k : ℝ} {μ : Measure (ℝ × ℝ)}
    [IsFiniteMeasure μ] (hK : 2 ≤ K) (hk : 0 ≤ k) (hμ : NonnegativeTimes μ) :
    Integrable (fun t => difference K k t.2) μ := by
  refine Integrable.of_bound ((difference_measurable K k).comp
    measurable_snd).aestronglyMeasurable 1 ?_
  filter_upwards [hμ] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (difference_bounds hK hk ht.2).1]
  exact (difference_bounds hK hk ht.2).2

lemma joint_observable_integrable {K : ℕ} {k : ℝ} {μ : Measure (ℝ × ℝ)}
    [IsFiniteMeasure μ] (hK : 2 ≤ K) (hk : 0 ≤ k) (hμ : NonnegativeTimes μ) :
    Integrable (fun t => difference K k t.1 * difference K k t.2) μ := by
  refine (second_observable_integrable hK hk hμ).bdd_mul (c := 1)
    ((difference_measurable K k).comp measurable_fst).aestronglyMeasurable ?_
  filter_upwards [hμ] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (difference_bounds hK hk ht.1).1]
  exact (difference_bounds hK hk ht.1).2

def orientations (K : ℕ) (a : AllelePair K) : ℝ :=
  if a.1 = a.2 then K else (K : ℝ) * ((K : ℝ)-1)

def pattern (pA pB q : ℝ) (sameA sameB : Prop) [Decidable sameA] [Decidable sameB] : ℝ :=
  if sameA then (if sameB then 1-pA-pB+q else pB-q)
  else (if sameB then pA-q else q)

theorem mass_eq_moments {K : ℕ} {k : ℝ} {μ : Measure (ℝ × ℝ)}
    [IsProbabilityMeasure μ] (hK : 2 ≤ K) (hk : 0 ≤ k) (hμ : NonnegativeTimes μ)
    (a : Observation K) :
    mass K k μ a =
      pattern (firstMoment K k μ) (secondMoment K k μ) (jointMoment K k μ)
        (a.1.1 = a.1.2) (a.2.1 = a.2.2) /
      (orientations K a.1 * orientations K a.2) := by
  have hf := first_observable_integrable hK hk hμ
  have hg := second_observable_integrable hK hk hμ
  have hfg := joint_observable_integrable hK hk hμ
  have h1 : Integrable (fun _ : ℝ × ℝ => (1 : ℝ)) μ := integrable_const 1
  have hf1 : Integrable (fun t => 1-difference K k t.1) μ := h1.sub hf
  have hf2 : Integrable (fun t => 1-difference K k t.1-difference K k t.2) μ :=
    hf1.sub hg
  unfold mass conditionalKernel siteKernel orientations pattern
  split_ifs with ha hb
  · simp_rw [div_mul_div_comm]
    rw [integral_div]
    congr 1
    calc
      (∫ t, (1-difference K k t.1) * (1-difference K k t.2) ∂μ) =
          ∫ t, 1-difference K k t.1-difference K k t.2 +
            difference K k t.1 * difference K k t.2 ∂μ := by
        apply integral_congr_ae
        exact ae_of_all _ (fun _ => by ring)
      _ = _ := by
        rw [integral_add hf2 hfg,
          integral_sub hf1 hg, integral_sub h1 hf]
        simp only [integral_const, probReal_univ, smul_eq_mul, one_mul,
          firstMoment, secondMoment, jointMoment]
  · simp_rw [div_mul_div_comm]
    rw [integral_div]
    congr 1
    calc
      (∫ t, (1-difference K k t.1) * difference K k t.2 ∂μ) =
          ∫ t, difference K k t.2 - difference K k t.1 * difference K k t.2 ∂μ := by
        apply integral_congr_ae
        exact ae_of_all _ (fun _ => by ring)
      _ = _ := integral_sub hg hfg
  · simp_rw [div_mul_div_comm]
    rw [integral_div]
    congr 1
    calc
      (∫ t, difference K k t.1 * (1-difference K k t.2) ∂μ) =
          ∫ t, difference K k t.1 - difference K k t.1 * difference K k t.2 ∂μ := by
        apply integral_congr_ae
        exact ae_of_all _ (fun _ => by ring)
      _ = _ := integral_sub hf hfg
  · simp_rw [div_mul_div_comm]
    exact integral_div _ _

theorem firstMoment_eq_secondMoment {K : ℕ} {k : ℝ} {μ : Measure (ℝ × ℝ)}
    (hsym : μ.map Prod.fst = μ.map Prod.snd) :
    firstMoment K k μ = secondMoment K k μ := by
  unfold firstMoment secondMoment
  rw [← integral_map measurable_fst.aemeasurable
    (difference_measurable K k).aestronglyMeasurable, hsym,
    integral_map measurable_snd.aemeasurable
      (difference_measurable K k).aestronglyMeasurable]

theorem mass_eq_two_moments {K : ℕ} {k : ℝ} {μ : Measure (ℝ × ℝ)}
    [IsProbabilityMeasure μ] (hK : 2 ≤ K) (hk : 0 ≤ k) (hμ : NonnegativeTimes μ)
    (hsym : μ.map Prod.fst = μ.map Prod.snd) (a : Observation K) :
    mass K k μ a =
      pattern (firstMoment K k μ) (firstMoment K k μ) (jointMoment K k μ)
        (a.1.1 = a.1.2) (a.2.1 = a.2.2) /
      (orientations K a.1 * orientations K a.2) := by
  rw [mass_eq_moments hK hk hμ, ← firstMoment_eq_secondMoment hsym]

theorem mass_eq_four_patterns {K : ℕ} {k : ℝ} {μ : Measure (ℝ × ℝ)}
    [IsProbabilityMeasure μ] (hK : 2 ≤ K) (hk : 0 ≤ k) (hμ : NonnegativeTimes μ)
    (hsym : μ.map Prod.fst = μ.map Prod.snd) (a : Observation K) :
    mass K k μ a =
      if a.1.1 = a.1.2 then
        if a.2.1 = a.2.2 then
          (1 - 2 * firstMoment K k μ + jointMoment K k μ) / (K : ℝ)^2
        else (firstMoment K k μ - jointMoment K k μ) / ((K : ℝ)^2 * ((K : ℝ)-1))
      else
        if a.2.1 = a.2.2 then
          (firstMoment K k μ - jointMoment K k μ) / ((K : ℝ)^2 * ((K : ℝ)-1))
        else jointMoment K k μ / ((K : ℝ)^2 * ((K : ℝ)-1)^2) := by
  rw [mass_eq_two_moments hK hk hμ hsym]
  unfold pattern orientations
  split_ifs <;> ring

theorem law_eq_of_momentPair_eq {K : ℕ} {k : ℝ} {μ ν : Measure (ℝ × ℝ)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hK : 2 ≤ K) (hk : 0 ≤ k) (hμ : NonnegativeTimes μ) (hν : NonnegativeTimes ν)
    (hsymμ : μ.map Prod.fst = μ.map Prod.snd)
    (hsymν : ν.map Prod.fst = ν.map Prod.snd)
    (hmom : momentPair K k μ = momentPair K k ν) : law K k μ = law K k ν := by
  have hp : firstMoment K k μ = firstMoment K k ν := congrArg Prod.fst hmom
  have hq : jointMoment K k μ = jointMoment K k ν := congrArg Prod.snd hmom
  have hm : mass K k μ = mass K k ν := by
    funext a
    rw [mass_eq_two_moments hK hk hμ hsymμ,
      mass_eq_two_moments hK hk hν hsymν, hp, hq]
  simp only [law, hm]

theorem momentPair_eq_panMutationMomentPair (K : ℕ) (k : ℝ)
    (P : ProperIntegrablePanModel) :
    momentPair K k P.pre.jointLaw = P.mutationMomentPair (limit K) k := by
  apply Prod.ext
  · rfl
  · unfold momentPair jointMoment ProperIntegrablePanModel.mutationMomentPair
    dsimp only
    apply integral_congr_ae
    exact ae_of_all _ (fun _ => by
      unfold difference ProperIntegrablePanModel.productMutationObservable
      ring)

theorem pan_nonnegativeTimes (P : ProperIntegrablePanModel) :
    NonnegativeTimes P.pre.jointLaw := by
  have hp : ∀ᵐ t ∂conditionalPairLaw P.rate (integrablePanClock P.rate) 0, 0 ≤ t := by
    unfold conditionalPairLaw
    apply (withDensity_absolutelyContinuous _ _).ae_le
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact ht.le
  have hf : ∀ᵐ t ∂P.pre.jointLaw.map Prod.fst, 0 ≤ t := by
    rw [P.jointLaw_map_fst]
    exact hp
  have hg : ∀ᵐ t ∂P.pre.jointLaw.map Prod.snd, 0 ≤ t := by
    rw [P.jointLaw_map_snd]
    exact hp
  exact (ae_of_ae_map measurable_fst.aemeasurable hf).and
    (ae_of_ae_map measurable_snd.aemeasurable hg)

theorem law_eq_pan_of_momentPair_eq {K : ℕ} {k : ℝ} {μ : Measure (ℝ × ℝ)}
    [IsProbabilityMeasure μ] (P : ProperIntegrablePanModel)
    (hK : 2 ≤ K) (hk : 0 ≤ k) (hμ : NonnegativeTimes μ)
    (hsym : μ.map Prod.fst = μ.map Prod.snd)
    (hmom : momentPair K k μ = P.mutationMomentPair (limit K) k) :
    law K k μ = law K k P.pre.jointLaw := by
  let := P.jointLaw_probability
  apply law_eq_of_momentPair_eq hK hk hμ (pan_nonnegativeTimes P) hsym
  · rw [P.jointLaw_map_fst, P.jointLaw_map_snd]
  · rw [momentPair_eq_panMutationMomentPair]
    exact hmom

end Rhone.Statistics.Identifiability.FiniteSiteObservation
