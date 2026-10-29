/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteSeparator.BlockStatistics

/-! # Unconditional moment extraction from finite-site pattern masses -/

@[expose] public section

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Rhone.Statistics.ThreeSiteSeparator
open ThreeTipSites SingleSiteChannel

def observationMoment {K L : ℕ} (π : Roots K L) (k : ℝ) (μ : Measure (ℝ × ℝ))
    (f : Panel K L → ℝ) : ℝ := ∑ x, f x*mass π k μ x

lemma conditionalMean_of_fixed {K : ℕ} (π : Roots K 3) (k : ℝ) (t : ℝ × ℝ)
    (f : Panel K 3 → ℝ) (m : ℝ) (hm : ∀ q, fixedMean π k t q f = m) :
    (∑ x, f x*conditional π k t x) = m := by
  have he (x : Panel K 3) : f x*conditional π k t x =
      (1/3 : ℝ)*∑ q : Fin 3, f x*fixedTopology π k t q x := by
    unfold conditional
    rw [← Finset.mul_sum]
    ring
  simp_rw [he]
  rw [← Finset.mul_sum, Finset.sum_comm]
  change (1/3 : ℝ)*∑ q : Fin 3, fixedMean π k t q f = m
  simp_rw [hm]
  norm_num
  ring

lemma observationMoment_eq_integral {K L : ℕ} (hK : 0 < K) (π : Roots K L)
    {k : ℝ} (hk : 0 ≤ k) {μ : Measure (ℝ × ℝ)} [IsFiniteMeasure μ]
    (hμ : NonnegativeTimes μ) (f : Panel K L → ℝ) :
    observationMoment π k μ f = ∫ t, (∑ x, f x*conditional π k t x) ∂μ := by
  unfold observationMoment mass
  simp_rw [← integral_const_mul]
  exact (integral_finsetSum _
    (fun x _ => (conditional_integrable hK π hk hμ x).const_mul (f x))).symm

lemma observationMoment_eq_of_law_eq {K L : ℕ} (π : Roots K L)
    {k ℓ : ℝ} (hk : 0 ≤ k) (hℓ : 0 ≤ ℓ) {μ ν : Measure (ℝ × ℝ)}
    (hμ : NonnegativeTimes μ) (hν : NonnegativeTimes ν)
    (he : law π k μ = law π ℓ ν) (f : Panel K L → ℝ) :
    observationMoment π k μ f = observationMoment π ℓ ν f := by
  have hm (x : Panel K L) : mass π k μ x = mass π ℓ ν x := by
    have hx := congrArg (fun ρ : Measure (Panel K L) => ρ {x}) he
    rw [law_singleton, law_singleton] at hx
    have ht := congrArg ENNReal.toReal hx
    simpa only [ENNReal.toReal_ofReal (mass_nonneg π hk hμ x),
      ENNReal.toReal_ofReal (mass_nonneg π hℓ hν x)] using ht
  simp only [observationMoment, hm]

lemma observed_a_moment {K : ℕ} (hK : 3 ≤ K) {k : ℝ} (hk : 0 ≤ k)
    {μ : Measure (ℝ × ℝ)} [IsFiniteMeasure μ] (hμ : NonnegativeTimes μ) :
    observationMoment (uniformBlockRoots K 3 (by omega)) k μ aStat =
      ∫ t, (Real.exp (-k*t.1) + 2*Real.exp (-k*(t.1+t.2)))/3 ∂μ := by
  rw [observationMoment_eq_integral (by omega) _ hk hμ]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => conditionalMean_of_fixed _ k t aStat _
    (fun q => aStat_mean hK k t q)

lemma observed_p2_moment {K : ℕ} (hK : 3 ≤ K) {k : ℝ} (hk : 0 ≤ k)
    {μ : Measure (ℝ × ℝ)} [IsFiniteMeasure μ] (hμ : NonnegativeTimes μ) :
    observationMoment (uniformBlockRoots K 3 (by omega)) k μ p2Stat =
      ∫ t, (Real.exp (-k*t.1)^2 + 2*Real.exp (-k*(t.1+t.2))^2)/3 ∂μ := by
  rw [observationMoment_eq_integral (by omega) _ hk hμ]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => conditionalMean_of_fixed _ k t p2Stat _
    (fun q => p2Stat_mean hK k t q)

lemma observed_p3_moment {K : ℕ} (hK : 3 ≤ K) {k : ℝ} (hk : 0 ≤ k)
    {μ : Measure (ℝ × ℝ)} [IsFiniteMeasure μ] (hμ : NonnegativeTimes μ) :
    observationMoment (uniformBlockRoots K 3 (by omega)) k μ p3Stat =
      ∫ t, (Real.exp (-k*t.1)^3 + 2*Real.exp (-k*(t.1+t.2))^3)/3 ∂μ := by
  rw [observationMoment_eq_integral (by omega) _ hk hμ]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => conditionalMean_of_fixed _ k t p3Stat _
    (fun q => p3Stat_mean hK k t q)

lemma observed_h_moment {K : ℕ} (hK : 3 ≤ K) {k : ℝ} (hk : 0 ≤ k)
    {μ : Measure (ℝ × ℝ)} [IsFiniteMeasure μ] (hμ : NonnegativeTimes μ) :
    observationMoment (uniformBlockRoots K 3 (by omega)) k μ hStat =
      ∫ t, secondMomentKernel k t*
        (Real.exp (-k*t.1)^2 + 2*Real.exp (-k*(t.1+t.2))^2)/3 ∂μ := by
  rw [observationMoment_eq_integral (by omega) _ hk hμ]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => conditionalMean_of_fixed _ k t hStat _
    (fun q => hStat_mean hK k t q)

lemma observed_j_moment {K : ℕ} (hK : 3 ≤ K) {k : ℝ} (hk : 0 ≤ k)
    {μ : Measure (ℝ × ℝ)} [IsFiniteMeasure μ] (hμ : NonnegativeTimes μ) :
    observationMoment (uniformBlockRoots K 3 (by omega)) k μ jStat =
      ∫ t, secondMomentKernel k t*(2*Real.exp (-k*t.1)*Real.exp (-k*(t.1+t.2)) +
        Real.exp (-k*(t.1+t.2))^2)/3 ∂μ := by
  rw [observationMoment_eq_integral (by omega) _ hk hμ]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => conditionalMean_of_fixed _ k t jStat _
    (fun q => jStat_mean hK k t q)

end Rhone.Statistics.ThreeSiteSeparator
