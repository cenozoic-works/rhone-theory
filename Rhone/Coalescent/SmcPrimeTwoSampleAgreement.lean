/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeTwoSampleAgreementStep
public import Rhone.Coalescent.SmcPrimeFixedPositionNonpositive
public import Rhone.Analysis.SmcPrimeTwoSampleFormulas

/-!
# Two samples, two positions: agreement probability under the SMC′ law

Source: wilton_carmi_hobolth2015, eq. (7); marjoram_wall2006, Methods, “The SMC′ algorithm”. -/

@[expose] public section

namespace Rhone.Coalescent.SmcPrime
open MeasureTheory ProbabilityTheory Set IntervalProcess
open scoped ENNReal

def twoSampleAgreement (x y : GenomicProbe) : Set (Genealogy 2) :=
  {G | G x 0 1 = G y 0 1}

theorem twoSampleAgreement_measurable (x y : GenomicProbe) :
    MeasurableSet (twoSampleAgreement x y) := by
  have h : ∀ q : GenomicProbe, Measurable fun G : Genealogy 2 => G q 0 1 := fun q =>
    (measurable_pi_apply (1 : Fin 2)).comp
      ((measurable_pi_apply (0 : Fin 2)).comp (measurable_pi_apply q))
  exact measurableSet_eq_fun (h x) (h y)

theorem spatialGenealogyObservation_two_eq (ω : ℕ → SpatialState 2)
    (hmono : ∀ n, (ω n).1 ≤ (ω (n + 1)).1) (q : GenomicProbe) (k : ℕ)
    (hk : (ω k).1 ≤ (q.val : ℝ) ∧ (q.val : ℝ) < (ω (k + 1)).1) :
    spatialGenealogyObservation 2 ω q 0 1 = ENNReal.ofReal (rootHeight (ω k).2) := by
  have hm : Monotone fun n => (ω n).1 := monotone_nat_of_le_succ hmono
  have huniq : ∀ k' : ℕ, (ω k').1 ≤ (q.val : ℝ) ∧ (q.val : ℝ) < (ω (k' + 1)).1 → k' = k := by
    intro k' hk'
    rcases lt_trichotomy k' k with hlt | heq | hgt
    · exact absurd ((hm (Nat.succ_le_of_lt hlt)).trans hk.1) (not_le.mpr hk'.2)
    · exact heq
    · exact absurd ((hm (Nat.succ_le_of_lt hgt)).trans hk'.1) (not_le.mpr hk.2)
  unfold spatialGenealogyObservation
  refine le_antisymm ?_ (le_iInf fun k' => ?_)
  · refine iInf_le_of_le k ?_
    simp only [hk, and_self, ↓reduceIte, twoSample_treePairMRCA, le_refl]
  · by_cases hk' : (ω k').1 ≤ (q.val : ℝ) ∧ (q.val : ℝ) < (ω (k' + 1)).1
    · rw [huniq k' hk']
      simp only [hk, and_self, ↓reduceIte, twoSample_treePairMRCA, le_refl]
    · simp only [hk', ↓reduceIte, le_top]

theorem twoSampleAgreement_indicator_eq_tsum {x y : GenomicProbe} (hxy : x.val < y.val)
    (ω : ℕ → SpatialState 2) (hmono : ∀ n, (ω n).1 ≤ (ω (n + 1)).1)
    (hx : ∃ k, (ω k).1 ≤ (x.val : ℝ) ∧ (x.val : ℝ) < (ω (k + 1)).1)
    (hy : ∃ k, (ω k).1 ≤ (y.val : ℝ) ∧ (y.val : ℝ) < (ω (k + 1)).1)
    (hnr : ∀ k j, rootHeight (ω (k + j + 1)).2 = rootHeight (ω k).2 →
      rootHeight (ω (k + j + 1)).2 = rootHeight (ω (k + j)).2) :
    (spatialGenealogyObservation 2 ⁻¹' twoSampleAgreement x y).indicator
        (1 : (ℕ → SpatialState 2) → ℝ≥0∞) ω =
      ∑' k, ∑' n, agreeTerm (x.val : ℝ) (y.val : ℝ) n (fun j => ω (k + j)) := by
  have hxyR : (x.val : ℝ) < (y.val : ℝ) := by exact_mod_cast hxy
  have hm : Monotone fun n => (ω n).1 := monotone_nat_of_le_succ hmono
  obtain ⟨k0, hk0⟩ := hx
  obtain ⟨m0, hm0⟩ := hy
  have hkm : k0 ≤ m0 := by
    by_contra hc
    have h1 := (hm (Nat.succ_le_of_lt (not_le.mp hc))).trans hk0.1
    exact absurd (h1.trans hxyR.le) (not_le.mpr hm0.2)
  obtain ⟨n0, rfl⟩ := Nat.exists_eq_add_of_le hkm
  have hux : ∀ k : ℕ, k ≠ k0 →
      ¬ ((ω k).1 ≤ (x.val : ℝ) ∧ (x.val : ℝ) < (ω (k + 1)).1) := by
    intro k hne hk
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact absurd ((hm (Nat.succ_le_of_lt hlt)).trans hk0.1) (not_le.mpr hk.2)
    · exact absurd ((hm (Nat.succ_le_of_lt hgt)).trans hk.1) (not_le.mpr hk0.2)
  have huy : ∀ n : ℕ, n ≠ n0 →
      ¬ ((ω (k0 + n)).1 ≤ (y.val : ℝ) ∧ (y.val : ℝ) < (ω (k0 + n + 1)).1) := by
    intro n hne hn
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h1 : k0 + n + 1 ≤ k0 + n0 := by omega
      exact absurd ((hm h1).trans hm0.1) (not_le.mpr hn.2)
    · have h1 : k0 + n0 + 1 ≤ k0 + n := by omega
      exact absurd ((hm h1).trans hn.1) (not_le.mpr hm0.2)
  have hheld : ∀ n : ℕ, rootHeight (ω (k0 + n)).2 = rootHeight (ω k0).2 →
      ∀ j ≤ n, rootHeight (ω (k0 + j)).2 = rootHeight (ω k0).2 := by
    intro n
    induction n with
    | zero =>
      intro h j hj
      rw [Nat.le_zero.mp hj]
      exact h
    | succ n ih =>
      intro h j hj
      rcases Nat.lt_or_ge j (n + 1) with hlt | hge
      · exact ih ((hnr k0 n h).symm.trans h) j (Nat.lt_succ_iff.mp hlt)
      · rw [le_antisymm hj hge]
        exact h
  have hk0' : ∑' k, ∑' n, agreeTerm (x.val : ℝ) (y.val : ℝ) n (fun j => ω (k + j)) =
      ∑' n, agreeTerm (x.val : ℝ) (y.val : ℝ) n (fun j => ω (k0 + j)) := by
    refine tsum_eq_single k0 fun k hk => ENNReal.tsum_eq_zero.mpr fun n => ?_
    change (if (ω k).1 ≤ (x.val : ℝ) ∧ (x.val : ℝ) < (ω (k + 1)).1 then (1 : ℝ≥0∞) else 0) *
      _ = 0
    simp only [hux k hk, ↓reduceIte, zero_mul]
  have hn0' : ∑' n, agreeTerm (x.val : ℝ) (y.val : ℝ) n (fun j => ω (k0 + j)) =
      agreeTerm (x.val : ℝ) (y.val : ℝ) n0 (fun j => ω (k0 + j)) := by
    refine tsum_eq_single n0 fun n hn => ?_
    change _ * ((if (ω (k0 + n)).1 ≤ (y.val : ℝ) then (1 : ℝ≥0∞) else 0) *
      (if (y.val : ℝ) < (ω (k0 + n + 1)).1 then 1 else 0) * _) = 0
    by_cases h1 : (ω (k0 + n)).1 ≤ (y.val : ℝ)
    · have h2 : ¬ (y.val : ℝ) < (ω (k0 + n + 1)).1 := fun h => huy n hn ⟨h1, h⟩
      simp only [h2, ↓reduceIte, mul_zero, zero_mul]
    · simp only [h1, ↓reduceIte, zero_mul, mul_zero]
  have hterm : agreeTerm (x.val : ℝ) (y.val : ℝ) n0 (fun j => ω (k0 + j)) =
      ∏ j ∈ Finset.range (n0 + 1),
        (if rootHeight (ω (k0 + j)).2 = rootHeight (ω k0).2 then (1 : ℝ≥0∞) else 0) := by
    change (if (ω k0).1 ≤ (x.val : ℝ) ∧ (x.val : ℝ) < (ω (k0 + 1)).1 then (1 : ℝ≥0∞) else 0) *
      ((if (ω (k0 + n0)).1 ≤ (y.val : ℝ) then (1 : ℝ≥0∞) else 0) *
        (if (y.val : ℝ) < (ω (k0 + n0 + 1)).1 then 1 else 0) *
        ∏ j ∈ Finset.range (n0 + 1),
          (if rootHeight (ω (k0 + j)).2 = rootHeight (ω k0).2 then (1 : ℝ≥0∞) else 0)) = _
    simp only [hk0, hm0.1, hm0.2, and_self, ↓reduceIte, one_mul]
  rw [hk0', hn0', hterm]
  have hobsx := spatialGenealogyObservation_two_eq ω hmono x k0 hk0
  have hobsy := spatialGenealogyObservation_two_eq ω hmono y (k0 + n0) hm0
  have hiff : ω ∈ spatialGenealogyObservation 2 ⁻¹' twoSampleAgreement x y ↔
      rootHeight (ω (k0 + n0)).2 = rootHeight (ω k0).2 := by
    change spatialGenealogyObservation 2 ω x 0 1 = spatialGenealogyObservation 2 ω y 0 1 ↔ _
    rw [hobsx, hobsy, ENNReal.ofReal_eq_ofReal_iff (root_height_nonneg _)
      (root_height_nonneg _)]
    exact eq_comm
  by_cases hagree : rootHeight (ω (k0 + n0)).2 = rootHeight (ω k0).2
  · rw [indicator_of_mem (hiff.mpr hagree)]
    refine (Finset.prod_eq_one fun j hj => ?_).symm
    simp only [hheld n0 hagree j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)), ↓reduceIte]
  · rw [indicator_of_notMem (mt hiff.mp hagree)]
    refine (Finset.prod_eq_zero (Finset.mem_range.mpr (Nat.lt_succ_self n0)) ?_).symm
    simp only [hagree, ↓reduceIte]

theorem smcPrime_two_sample_agreement_prob_of_pos {R : ℝ} (hR : 0 < R)
    (x y : GenomicProbe) (hxy : x.val < y.val) :
    smcPrimeGenealogyLaw 2 R (twoSampleAgreement x y) =
      ENNReal.ofReal (Analysis.SmcPrime.smcPrimeAgreementProb (R * ((y.val : ℝ) - (x.val : ℝ)))) :=
          by
  have hxyR : (x.val : ℝ) < (y.val : ℝ) := by exact_mod_cast hxy
  have hx0 : (0 : ℝ) ≤ (x.val : ℝ) := by exact_mod_cast x.property.1
  have hx1 : (x.val : ℝ) < 1 := by exact_mod_cast x.property.2
  have hy0 : (0 : ℝ) ≤ (y.val : ℝ) := by exact_mod_cast y.property.1
  have hy1 : (y.val : ℝ) < 1 := by exact_mod_cast y.property.2
  have hpre : MeasurableSet (spatialGenealogyObservation 2 ⁻¹' twoSampleAgreement x y) :=
    spatialGenealogyObservation_measurable 2 (twoSampleAgreement_measurable x y)
  let g : ℝ → ℝ≥0∞ := (Ioi (0 : ℝ)).indicator fun h =>
    ENNReal.ofReal (Real.exp
        (-(R * Analysis.SmcPrime.smcPrimeLambda h * ((y.val : ℝ) - (x.val : ℝ)))))
  have hg : Measurable g := by
    refine Measurable.indicator (ENNReal.measurable_ofReal.comp ?_) measurableSet_Ioi
    unfold Analysis.SmcPrime.smcPrimeLambda
    fun_prop
  have hg1 : ∀ h, g h ≤ 1 := by
    intro h
    by_cases hh : 0 < h
    · simp only [g, indicator_of_mem (show h ∈ Ioi (0 : ℝ) from hh)]
      refine ENNReal.ofReal_le_one.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ?_))
      exact mul_nonneg (mul_nonneg hR.le (Analysis.SmcPrime.smcPrimeLambda_nonneg hh.le))
        (sub_nonneg.mpr hxyR.le)
    · simp only [g, indicator_of_notMem (show h ∉ Ioi (0 : ℝ) from hh), zero_le]
  have hae : ∀ᵐ ω ∂(spatialProcess 2 R).law (spatialInitialLaw 2),
      (spatialGenealogyObservation 2 ⁻¹' twoSampleAgreement x y).indicator
          (1 : (ℕ → SpatialState 2) → ℝ≥0∞) ω =
        ∑' k, ∑' n, agreeTerm (x.val : ℝ) (y.val : ℝ) n (fun j => ω (k + j)) := by
    filter_upwards [spatialProcess_law_position_ae 2 R,
      spatialProcess_two_probe_segment_ae R hx0 hx1,
      spatialProcess_two_probe_segment_ae R hy0 hy1,
      spatialProcess_two_law_noReturn_ae hR] with ω h1 h2 h3 h4
    exact twoSampleAgreement_indicator_eq_tsum hxy ω (fun n => (h1 n).2) h2 h3 h4
  have hF : Measurable fun ω' : ℕ → SpatialState 2 =>
      ∑' n, agreeTerm (x.val : ℝ) (y.val : ℝ) n ω' :=
    Measurable.tsum fun n => measurable_agreeTerm _ _ n
  have hFk : ∀ k : ℕ, Measurable fun ω : ℕ → SpatialState 2 =>
      ∑' n, agreeTerm (x.val : ℝ) (y.val : ℝ) n (fun j => ω (k + j)) := fun k =>
    hF.comp (Rhone.MarkovChain.DiscreteProcess.measurable_shift (S := SpatialState 2) k)
  have hk : ∀ k : ℕ, ∫⁻ ω, ∑' n, agreeTerm (x.val : ℝ) (y.val : ℝ) n (fun j => ω (k + j))
      ∂(spatialProcess 2 R).law (spatialInitialLaw 2) =
      stateMean R k (probeWeight R (x.val : ℝ) g) := by
    intro k
    rw [spatialProcess_law_lintegral_shift 2 R (spatialInitialLaw 2) k _ hF]
    unfold stateMean
    refine lintegral_congr_ae ?_
    filter_upwards [spatialProcess_two_law_twoSampleArray_ae R] with ω hω
    rw [lintegral_tsum fun n => (measurable_agreeTerm _ _ n).aemeasurable,
      spatialProcess_two_agreeTerm_tsum hR hxyR.le hy1 (ω k) (hω k).1 (hω k).2]
    simp only [probeWeight, g, indicator_of_mem (show rootHeight (ω k).2 ∈ Ioi (0 : ℝ) from
      (hω k).2)]
  unfold smcPrimeGenealogyLaw
  rw [Measure.map_apply (spatialGenealogyObservation_measurable 2)
    (twoSampleAgreement_measurable x y), ← lintegral_indicator_one hpre,
    lintegral_congr_ae hae,
    lintegral_tsum fun k => (hFk k).aemeasurable]
  simp only [hk]
  rw [tsum_stateMean_probeWeight hR hx0 hx1 g hg hg1]
  unfold Analysis.SmcPrime.smcPrimeAgreementProb
  rw [ofReal_integral_eq_lintegral_ofReal
    (Analysis.SmcPrime.smcPrimeAgreementIntegrand_integrableOn
        (mul_nonneg hR.le (sub_nonneg.mpr hxyR.le)))
    (Filter.Eventually.of_forall fun h => Real.exp_nonneg _)]
  refine setLIntegral_congr_fun measurableSet_Ioi fun h hh => ?_
  simp only [g, indicator_of_mem hh]
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
  congr 2
  ring

/-- Source: wilton_carmi_hobolth2015, eq. (7). -/
theorem smcPrime_two_sample_agreement_prob (R : ℝ) (hR : 0 ≤ R)
    (x y : GenomicProbe) (hxy : x.val < y.val) :
    smcPrimeGenealogyLaw 2 R (twoSampleAgreement x y) =
      ENNReal.ofReal (Analysis.SmcPrime.smcPrimeAgreementProb (R * ((y.val : ℝ) - (x.val : ℝ)))) :=
          by
  rcases hR.eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul, Analysis.SmcPrime.smcPrimeAgreementProb_zero, ENNReal.ofReal_one,
      smcPrimeGenealogyLaw_zero_eq_kingmanTree 2,
      Measure.map_apply (treeConstantGenealogy_measurable 2)
        (twoSampleAgreement_measurable x y)]
    have huniv : (fun (T : Tree 2) (_ : GenomicProbe) (i j : Fin 2) => treePairMRCA T i j) ⁻¹'
        twoSampleAgreement x y = univ := eq_univ_of_forall fun T => rfl
    rw [huniv, measure_univ]
  · exact smcPrime_two_sample_agreement_prob_of_pos hpos x y hxy

end Rhone.Coalescent.SmcPrime
