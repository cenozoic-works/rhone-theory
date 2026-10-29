/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteSeparator.SourceRewardIntegrals

/-! # Exact Laplace transform of the duration law for the two-island source -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.ThreeSiteSeparator
open MarkovChain.Identifiability Identifiability

lemma entryMeasure_nonnegative_support (m : ℝ) (j : Fin 2) :
    ∀ᵐ s ∂entryMeasure m j, 0 ≤ s := by
  exact (withDensity_absolutelyContinuous _ _).ae_le
    ((ae_restrict_mem measurableSet_Ioi).mono fun _ h => h.le)

lemma postMeasure_nonnegative_support (m : ℝ) (j : Fin 2) :
    ∀ᵐ s ∂postMeasure m j, 0 ≤ s := by
  exact (withDensity_absolutelyContinuous _ _).ae_le
    ((ae_restrict_mem measurableSet_Ioi).mono fun _ h => h.le)

lemma source_component_exp_integrable {m a b : ℝ} (hm : 0 < m) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (j : Fin 2) : Integrable (fun p : ℝ × ℝ => Real.exp (-a*p.1-b*p.2))
      ((entryMeasure m j).prod (postMeasure m j)) := by
  let : IsFiniteMeasure (entryMeasure m j) := entryMeasure_finite hm j
  let : IsProbabilityMeasure (postMeasure m j) := postMeasure_probability hm j
  apply Integrable.of_bound (by fun_prop) 1
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (entryMeasure_nonnegative_support m j),
    Measure.quasiMeasurePreserving_snd.ae (postMeasure_nonnegative_support m j)] with p hp hq
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_one_iff.mpr
  have h1 := mul_nonneg ha hp
  have h2 := mul_nonneg hb hq
  linarith

lemma source_component_laplace {m a b : ℝ} (hm : 0 < m) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (j : Fin 2) :
    (∫ p : ℝ × ℝ, Real.exp (-a*p.1-b*p.2) ∂(entryMeasure m j).prod (postMeasure m j)) =
      (prePotential m a (if j = 0 then 1 else 0) (if j = 1 then 1 else 0)) 0 *
        pairLaplacePotential 0 1 m b j := by
  let : IsFiniteMeasure (entryMeasure m j) := entryMeasure_finite hm j
  let : IsProbabilityMeasure (postMeasure m j) := postMeasure_probability hm j
  have he (p : ℝ × ℝ) : Real.exp (-a*p.1-b*p.2) =
      Real.exp (-a*p.1)*Real.exp (-b*p.2) := by rw [← Real.exp_add]; congr 1; ring
  simp_rw [he]
  rw [integral_prod_mul (fun s => Real.exp (-a*s)) (fun s => Real.exp (-b*s)),
    entryMeasure_laplace hm ha, postMeasure_laplace hm hb]

lemma source_duration_laplace {m a b : ℝ} (hm : 0 < m) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∫ p : ℝ × ℝ, Real.exp (-a*p.1-b*p.2) ∂IslandThreeTimes.durationLaw 0 1 m) =
      prePotential m a 1 0 0*pairLaplacePotential 0 1 m b 0 +
        prePotential m a 0 1 0*pairLaplacePotential 0 1 m b 1 := by
  rw [source_duration_products m hm.le,
    integral_add_measure (source_component_exp_integrable hm ha hb 0)
      (source_component_exp_integrable hm ha hb 1),
    source_component_laplace hm ha hb, source_component_laplace hm ha hb]
  norm_num

theorem integral_eq_sourceMoment {m : ℝ} (hm : 0 < m) (p q : ℕ) :
    (∫ t : ℝ × ℝ, Real.exp (-((p : ℝ)+q)*t.1-(q : ℝ)*t.2)
      ∂IslandThreeTimes.durationLaw 0 1 m) = sourceMoment p q m := by
  have ha : 0 ≤ (p : ℝ)+q := by positivity
  have hb : 0 ≤ (q : ℝ) := by positivity
  have hD : preDenominator m ((p : ℝ)+q) ≠ 0 := (preDenominator_pos hm ha).ne'
  have hE : pairLaplaceDenominator 0 1 m q ≠ 0 :=
    (pairLaplaceDenominator_pos 0 (by norm_num) hm hb).ne'
  rw [source_duration_laplace hm ha hb]
  unfold prePotential pairLaplacePotential sourceMoment
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  by_cases hq : q = 0
  · subst q
    simp only [ite_true, Nat.cast_zero, add_zero]
    unfold pairLaplaceDenominator preDenominator at *
    norm_num at *
    field_simp
    ring
  · simp only [hq, ite_false]
    unfold pairLaplaceDenominator preDenominator at *
    norm_num at *
    field_simp
    ring

end Rhone.Statistics.ThreeSiteSeparator
