/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.CollapsedGenealogy.Decoder
public import Rhone.Statistics.CollapsedGenealogy.CompactMoments
public import Rhone.Statistics.CollapsedGenealogy.Moments

/-! # Compact encoding and measurable recovery of the collapsed object -/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Rhone.Statistics.CollapsedGenealogy
open ThreeSiteSeparator ThreeTipSites

def boundedDecay (t : ℝ) : ℝ := Real.exp (-max 0 t)

theorem bounded_decay_bounds (t : ℝ) : boundedDecay t ∈ Icc (0 : ℝ) 1 := by
  refine ⟨(Real.exp_pos _).le, ?_⟩
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (le_max_left _ _))

def encode (k : ℝ) (g : Joint) : Cube 3 := fun i =>
  ⟨pairMeans (boundedDecay (k * g.1.1)) (boundedDecay (k * (g.1.1 + g.1.2))) g.2 i, by
    unfold pairMeans
    split_ifs <;> exact bounded_decay_bounds _⟩

theorem encode_measurable (k : ℝ) : Measurable (encode k) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.subtype_mk
  apply measurable_from_prod_countable_left
  intro q
  unfold pairMeans boundedDecay
  dsimp only
  by_cases h : (q = 0 ∧ i = 0) ∨ (q = 1 ∧ i = 2) ∨ (q = 2 ∧ i = 1)
  · simp only [ite_eq_left h]; fun_prop
  · simp only [ite_eq_right h]; fun_prop

theorem encode_value {k : ℝ} (hk : 0 ≤ k) (g : Joint) (hg : 0 ≤ g.1.1 ∧ 0 ≤ g.1.2)
    (i : Fin 3) : (encode k g i).val =
      pairMeans (Real.exp (-k * g.1.1)) (Real.exp (-k * (g.1.1 + g.1.2))) g.2 i := by
  have hu := mul_nonneg hk hg.1
  have huv := mul_nonneg hk (add_nonneg hg.1 hg.2)
  simp [encode, boundedDecay, max_eq_right hu, max_eq_right huv, neg_mul]

theorem decoded_encode {k : ℝ} (hk : 0 ≤ k) (g : Joint) (hg : 0 ≤ g.1.1 ∧ 0 ≤ g.1.2) :
    decode (fun i => (encode k g i).val) = collapse (scale k g) := by
  simp_rw [encode_value hk g hg]
  have he : k * (g.1.1 + g.1.2) = k * g.1.1 + k * g.1.2 := mul_add _ _ _
  simpa only [scale, he, neg_mul] using decode_means (scale k g) (mul_nonneg hk hg.2)

theorem decoded_encoding_map {k : ℝ} (hk : 0 ≤ k) (μ : Measure Joint)
    (hμ : NonnegativeJoint μ) :
    Measure.map (fun x : Cube 3 => decode (fun i => (x i).val)) (Measure.map (encode k) μ) =
      object k μ := by
  have hd : Measurable (fun x : Cube 3 => decode (fun i => (x i).val)) :=
    decode_measurable.comp (by fun_prop)
  rw [Measure.map_map hd (encode_measurable k)]
  apply Measure.map_congr
  filter_upwards [hμ] with g hg
  exact decoded_encode hk g hg

theorem encoded_word_moment {K : ℕ} (hK : 2 ≤ K) {k : ℝ} (hk : 0 ≤ k)
    (μ : Measure Joint) [IsFiniteMeasure μ] (hμ : NonnegativeJoint μ)
    (L : ℕ) (w : Fin L → Fin 3) :
    (∫ x, ∏ j, (x (w j)).val ∂Measure.map (encode k) μ) =
      ∑ x : Panel K L, (∏ s, uScore (w s) (x s)) *
        jointMass (uniformBlockRoots K L (by omega)) k μ x := by
  have hw : Measurable (fun x : Cube 3 => ∏ j, (x (w j)).val) := by fun_prop
  rw [integral_map (encode_measurable k).aemeasurable hw.aestronglyMeasurable,
    word_moment hK hk μ hμ]
  apply integral_congr_ae
  filter_upwards [hμ] with g hg
  simp_rw [encode_value hk g hg]

end Rhone.Statistics.CollapsedGenealogy
