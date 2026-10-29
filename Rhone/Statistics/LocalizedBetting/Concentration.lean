/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.DependentPairedTest.MeasureBridge

/-! # Range-four-thirds finite-sample localization bound for the concrete feature table -/

@[expose] public section

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Rhone.Statistics.LocalizedBetting
open DependenceBudget DependentPairedTest
open Identifiability.FinitePanelSampling
variable {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]

theorem range_four_thirds_concentration {I : Type*} [Fintype I]
    (P : Law X) (f : I → X → ℝ) (hb : ∀ i x, -1 / 3 ≤ f i x ∧ f i x ≤ 1)
    {N : ℕ} (hN : 0 < N) {eps : ℝ} (heps : 0 ≤ eps) :
    probability (iid P N) (fun z => ∃ i, eps ≤ |sampleMean (f i) z - rejection P (f i)|) ≤
      2 * Fintype.card I * Real.exp (-9 * N * eps ^ 2 / 8) := by
  let g : I → X → ℝ := fun i x => (3 * f i x - 1) / 2
  have hg : ∀ i x, |g i x| ≤ 1 := by
    intro i x
    obtain ⟨hl, hu⟩ := hb i x
    dsimp [g]
    rw [abs_le]
    constructor <;> linarith
  have h := iid_finite_scores_abs_ge (lawMeasure P) g (fun _ => by fun_prop) hg hN
    (show 0 ≤ 3 * eps / 2 by positivity)
  have hm (i : I) : (∫ x, g i x ∂lawMeasure P) = (3 * rejection P (f i) - 1) / 2 := by
    rw [law_measure_integral]
    have he : (∑ x, P.mass x * ((3 * f i x - 1) / 2)) =
        (3 * (∑ x, P.mass x * f i x) - ∑ x, P.mass x) / 2 := by
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro x _
      ring
    change (∑ x, P.mass x * ((3 * f i x - 1) / 2)) = _
    rw [he, P.total]
    rfl
  have hs (i : I) (z : Fin N → X) :
      sampleMean (g i) z = (3 * sampleMean (f i) z - 1) / 2 := by
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    simp only [sampleMean, g, ← Finset.sum_div, Finset.sum_sub_distrib,
      ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one]
    field_simp
  have hd (i : I) (z : Fin N → X) :
      |sampleMean (g i) z - ∫ x, g i x ∂lawMeasure P| =
        3 / 2 * |sampleMean (f i) z - rejection P (f i)| := by
    rw [hs, hm, show (3 * sampleMean (f i) z - 1) / 2 -
      (3 * rejection P (f i) - 1) / 2 =
        (3 / 2) * (sampleMean (f i) z - rejection P (f i)) by ring, abs_mul]
    norm_num
  simp_rw [hd] at h
  rw [iid_measure_probability] at h
  have he : (fun z : Fin N → X => ∃ i, 3 * eps / 2 ≤
      3 / 2 * |sampleMean (f i) z - rejection P (f i)|) =
      (fun z => ∃ i, eps ≤ |sampleMean (f i) z - rejection P (f i)|) := by
    funext z
    congr 1
    funext i
    apply propext
    constructor <;> intro ht <;> linarith
  rw [he] at h
  convert h using 1
  congr 2
  ring

end Rhone.Statistics.LocalizedBetting
