/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.WeakRegularSeparation.EncodingMoments

/-! # Unused-site padding for bounded pair-score words in full finite blocks -/

@[expose] public section

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Rhone.Statistics.WeakRegularSeparation
open CollapsedGenealogy ThreeSiteSeparator ThreeTipSites

def optionalScore {K : ℕ} (e : Option (Fin 3)) (x : Triple K) : ℝ :=
  e.elim 1 (fun q => uScore q x)

def optionalCoordinate (e : Option (Fin 3)) (x : Cube 3) : ℝ :=
  e.elim 1 (fun q => (x q).val)

theorem optional_score_bound {K : ℕ} (hK : 2 ≤ K) (e : Option (Fin 3))
    (x : Triple K) : |optionalScore e x| ≤ 1 := by
  cases e with
  | none => norm_num [optionalScore]
  | some q =>
    fin_cases q <;> exact pairScore_abs_le_one hK _ _

theorem optional_site_mean {K : ℕ} (hK : 2 ≤ K) {k : ℝ} (hk : 0 ≤ k)
    (g : Joint) (hg : 0 ≤ g.1.1 ∧ 0 ≤ g.1.2) (e : Option (Fin 3)) :
    (∑ y : Triple K, optionalScore e y *
      site K (fun _ => 1 / (K : ℝ)) k g.1 (orientation K g.2 y)) =
      optionalCoordinate e (encode k g) := by
  cases e with
  | none =>
    simp only [optionalScore, optionalCoordinate, Option.elim_none, one_mul]
    rw [Equiv.sum_comp (orientation K g.2)]
    exact site_sum (by omega) _ (by simp [ne_of_gt (show (0 : ℝ) < K by positivity)]) k g.1
  | some q =>
    simp only [optionalScore, optionalCoordinate, Option.elim_some]
    rw [oriented_pair_mean hK, encode_value hk g hg]

theorem padded_word_moment {K L : ℕ} (hK : 2 ≤ K) {k : ℝ} (hk : 0 ≤ k)
    (μ : Measure Joint) [IsFiniteMeasure μ] (hμ : NonnegativeJoint μ)
    (w : Fin L → Option (Fin 3)) :
    (∫ x, ∏ j, optionalCoordinate (w j) x ∂μ.map (encode k)) =
      ∑ x : Panel K L, (∏ j, optionalScore (w j) (x j)) *
        jointMass (uniformBlockRoots K L (by omega)) k μ x := by
  have hf : Measurable (fun x : Cube 3 => ∏ j, optionalCoordinate (w j) x) := by
    apply Finset.measurable_prod
    intro j _
    cases w j with
    | none => exact measurable_const
    | some q => exact measurable_subtype_coe.comp (measurable_pi_apply q)
  rw [integral_map (encode_measurable k).aemeasurable hf.aestronglyMeasurable]
  unfold jointMass
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ (fun x _ =>
    (fixed_integrable (by omega) _ hk μ hμ x).const_mul _)]
  apply integral_congr_ae
  filter_upwards [hμ] with g hg
  rw [fixedTopology_product_scores]
  symm
  apply Finset.prod_congr rfl
  intro j _
  exact optional_site_mean hK hk g hg (w j)

end Rhone.Statistics.WeakRegularSeparation
