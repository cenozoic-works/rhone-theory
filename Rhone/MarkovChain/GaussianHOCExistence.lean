/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.GaussianHOCNormalizer
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Gaussian density lower bounds for existence of the house-of-cards normalizer

Source: kingman1978_selection, sec. 3, eq. (3.3)–(3.5), p. 4; turelli1984, p. 150, eq. (3.2b);
barton_turelli1987, pp. 158, 163. -/

@[expose] public section
noncomputable section
namespace Rhone.MarkovChain.GaussianHouseOfCards
open ProbabilityTheory MeasureTheory Filter
open scoped ENNReal NNReal Topology

/-- Source: barton_turelli1987, pp. 158, 163. -/
theorem gaussian_pdf_near_zero_lower_bound (T : ℝ≥0) (hT : 0 < T)
    (z : ℝ) (hz : |z| ≤ 1) :
    ProbabilityTheory.gaussianPDFReal 0 T 1 ≤ ProbabilityTheory.gaussianPDFReal 0 T z := by
  have hsq : z^2 ≤ 1 := by nlinarith [abs_le.mp hz]
  have hTreal : 0 < (T : ℝ) := NNReal.coe_pos.mpr hT
  simp only [gaussianPDFReal, sub_zero, one_pow]
  apply mul_le_mul_of_nonneg_left ?_ (by positivity)
  apply Real.exp_le_exp.mpr
  apply (div_le_div_iff_of_pos_right (by positivity : 0 < 2*(T : ℝ))).mpr
  linarith

/-- Source: barton_turelli1987, pp. 158, 163. -/
theorem gaussian_small_interval_mass_lower_bound (T : ℝ≥0) (hT : 0 < T)
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    2*r*ProbabilityTheory.gaussianPDFReal 0 T 1 ≤
      (ProbabilityTheory.gaussianReal 0 T).real (Set.Icc (-r) r) := by
  have hbound : (∫ _ in Set.Icc (-r) r, gaussianPDFReal 0 T 1) ≤
      ∫ z in Set.Icc (-r) r, gaussianPDFReal 0 T z := by
    have hc : IntegrableOn (fun _ : ℝ => gaussianPDFReal 0 T 1) (Set.Icc (-r) r) volume :=
      integrableOn_const (by simp [Real.volume_Icc])
    apply integral_mono_ae hc
      (integrable_gaussianPDFReal 0 T).restrict
    filter_upwards [ae_restrict_mem measurableSet_Icc] with z hz
    apply gaussian_pdf_near_zero_lower_bound T hT z
    apply (abs_le.mpr hz).trans hr1
  rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul] at hbound
  have hmass : (gaussianReal 0 T).real (Set.Icc (-r) r) =
      ∫ z in Set.Icc (-r) r, gaussianPDFReal 0 T z := by
    rw [measureReal_def, gaussianReal_apply_eq_integral 0 (ne_of_gt hT),
      ENNReal.toReal_ofReal (integral_nonneg fun z => gaussianPDFReal_nonneg 0 T z)]
  rw [hmass]
  convert hbound using 1
  ring

/-- Source: barton_turelli1987, pp. 158, 163. -/
theorem gaussian_hoc_near_one_mass_lower_bound (u S : ℝ) (T : ℝ≥0)
    (r : ℝ) (hu : 0 < u) (hS : 0 < S) (hT : 0 < T)
    (hr0 : 0 < r) (hr1 : r ≤ 1) (hcost : r ^ 2 / (2 * S) < 1) :
    2*ProbabilityTheory.gaussianPDFReal 0 T 1*u*S/r ≤
      gaussianHOCMass u (1-r^2/(2*S)) S T := by
  let k := 1-r^2/(2*S)
  have hk0 : 0 < k := sub_pos.mpr hcost
  have hk1 : k < 1 := by
    have : 0 < r^2/(2*S) := div_pos (sq_pos_of_pos hr0) (by positivity)
    dsimp [k]
    linarith
  have hq := gaussian_hoc_weight_integrable u k S T hu.le hk0.le hk1 hS
  have hlocal (z : ℝ) (hz : z ∈ Set.Icc (-r) r) :
      u*S/r^2 ≤ gaussianHOCWeight u k S z := by
    have hzsq : z^2 ≤ r^2 := by nlinarith [abs_le.mp (abs_le.mpr hz)]
    have hw := gaussian_fitness_bounds S hS z
    have ht : 1-z^2/(2*S) ≤ gaussianFitness S z := by
      simpa only [gaussianFitness, neg_div] using Real.one_sub_le_exp_neg (z^2/(2*S))
    have htw : (r^2/(2*S))*gaussianFitness S z ≤ r^2/(2*S) :=
      by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hw.2
        (show 0 ≤ r^2/(2*S) by positivity)
    have hzr : z^2/(2*S) ≤ r^2/(2*S) :=
      div_le_div_of_nonneg_right hzsq (by positivity)
    have htwo : r^2/S = 2*(r^2/(2*S)) := by ring
    have hdenle : 1-k*gaussianFitness S z ≤ r^2/S := by
      dsimp [k]
      nlinarith
    have hden : 0 < 1-k*gaussianFitness S z := by nlinarith
    have hb := div_le_div_of_nonneg_left hu.le hden hdenle
    have heq : u/(r^2/S) = u*S/r^2 := by field_simp
    rw [heq] at hb
    exact hb
  have hset : (∫ _ in Set.Icc (-r) r, u*S/r^2 ∂gaussianReal 0 T) ≤
      ∫ z in Set.Icc (-r) r, gaussianHOCWeight u k S z ∂gaussianReal 0 T := by
    apply integral_mono_ae (integrable_const _) hq.restrict
    filter_upwards [ae_restrict_mem measurableSet_Icc] with z hz
    exact hlocal z hz
  rw [setIntegral_const, smul_eq_mul] at hset
  calc
    2*gaussianPDFReal 0 T 1*u*S/r =
        (2*r*gaussianPDFReal 0 T 1)*(u*S/r^2) := by field_simp
    _ ≤ (gaussianReal 0 T).real (Set.Icc (-r) r)*(u*S/r^2) :=
      mul_le_mul_of_nonneg_right (gaussian_small_interval_mass_lower_bound T hT r hr0.le hr1)
        (by positivity)
    _ ≤ ∫ z in Set.Icc (-r) r, gaussianHOCWeight u k S z ∂gaussianReal 0 T := hset
    _ ≤ gaussianHOCMass u k S T :=
      setIntegral_le_integral hq (Filter.Eventually.of_forall fun z =>
        (gaussian_hoc_weight_bounds u k S hu.le hk0.le hk1 hS z).1)

/--
Source: kingman1978_selection, sec. 3, eq. (3.3)–(3.5), (3.8)–(3.9), pp. 4–5; turelli1984, p. 150,
eq. (3.2a)–(3.2b); barton_turelli1987, pp. 158, 163. -/
theorem gaussian_hoc_normalizer_exists_unique
    (u S : ℝ) (T : ℝ≥0) (hu0 : 0 < u) (hu1 : u < 1)
    (hS : 0 < S) (hT : 0 < T) :
    ∃! k : ℝ, 1 - u < k ∧ k < 1 ∧ gaussianHOCMass u k S T = 1 := by
  let C := gaussianPDFReal 0 T 1
  have hC : 0 < C := by
    dsimp [C]
    exact gaussianPDFReal_pos 0 T 1 (ne_of_gt hT)
  have hmin : 0 < min 1 (min (2*S*u) (2*C*u*S)) := by positivity
  obtain ⟨r, hr0, hr⟩ := exists_between hmin
  have hr1 : r < 1 := lt_of_lt_of_le hr (min_le_left _ _)
  have hrSu : r < 2*S*u :=
    lt_of_lt_of_le hr ((min_le_right _ _).trans (min_le_left _ _))
  have hrC : r < 2*C*u*S :=
    lt_of_lt_of_le hr ((min_le_right _ _).trans (min_le_right _ _))
  have hcost : r^2/(2*S) < u := by
    apply (div_lt_iff₀ (by positivity : 0 < 2*S)).mpr
    nlinarith
  let K := 1-r^2/(2*S)
  have hK0 : 1-u < K := by dsimp [K]; linarith
  have hK1 : K < 1 := by
    dsimp [K]
    have : 0 < r^2/(2*S) := by positivity
    linarith
  have hmassK : 1 < gaussianHOCMass u K S T := by
    have hb := gaussian_hoc_near_one_mass_lower_bound u S T r hu0 hS hT
      hr0 hr1.le (hcost.trans hu1)
    have hc : 1 < 2*C*u*S/r := (lt_div_iff₀ hr0).mpr (by simpa using hrC)
    exact hc.trans_le hb
  have hleft := gaussian_hoc_mass_left_endpoint_lt_one u S T hu0 hu1 hS hT
  have hcont := (gaussian_hoc_mass_continuous_on u S T hu0.le hS K
    (by linarith) hK1).mono (show Set.Icc (1-u) K ⊆ Set.Icc 0 K from
      fun x hx => ⟨by linarith [hx.1], hx.2⟩)
  obtain ⟨k, hk, hmass⟩ := intermediate_value_Icc hK0.le hcont ⟨hleft.le, hmassK.le⟩
  change gaussianHOCMass u k S T = 1 at hmass
  have hk0 : 1-u < k := by
    apply lt_of_le_of_ne hk.1
    intro heq
    rw [heq, hmass] at hleft
    exact (lt_irrefl 1) hleft
  have hk1 : k < 1 := hk.2.trans_lt hK1
  refine ⟨k, ⟨hk0, hk1, hmass⟩, ?_⟩
  intro k' hk'
  apply (gaussian_hoc_mass_strict_mono u S T hu0 hS).injOn
    (show k' ∈ Set.Ico 0 1 from ⟨by linarith [hk'.1], hk'.2.1⟩)
    (show k ∈ Set.Ico 0 1 from ⟨by linarith, hk1⟩)
  exact hk'.2.2.trans hmass.symm

end Rhone.MarkovChain.GaussianHouseOfCards
