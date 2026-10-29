/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.UpperBranch
public import Rhone.Statistics.Identifiability.RankMeasure

/-! # The upper-triangle density is a restriction of the normalized joint law -/

@[expose] public section

open scoped ENNReal
open Set MeasureTheory
namespace Rhone.Statistics.Identifiability

set_option backward.isDefEq.respectTransparency false

theorem positive_density_nonpos_zero (f : ℝ → ℝ≥0∞) :
    ((volume.restrict (Ioi (0 : ℝ))).withDensity f) (Iic 0) = 0 := by
  apply withDensity_absolutelyContinuous _ _
  rw [Measure.restrict_apply measurableSet_Iic]
  rw [Set.inter_comm, Set.Ioi_inter_Iic, Set.Ioc_self, measure_empty]

theorem diagonal_map_restrict_upper_zero (μ : Measure (ℝ × ℝ)) :
    (μ.map (fun p => (p.1,p.1))).restrict upperWedge = 0 := by
  apply Measure.restrict_eq_zero.mpr
  rw [Measure.map_apply (continuous_fst.prodMk continuous_fst).measurable
    upperWedge_open.measurableSet]
  have h : (fun p : ℝ × ℝ => (p.1,p.1)) ⁻¹' upperWedge = ∅ := by
    ext p
    simp [upperWedge]
  rw [h, measure_empty]

theorem lower_map_restrict_upper_zero (μ ν : Measure ℝ) [SFinite ν]
    (hν : ν (Iic 0) = 0) :
    ((μ.prod ν).map (fun p => (p.1+p.2,p.1))).restrict upperWedge = 0 := by
  apply Measure.restrict_eq_zero.mpr
  rw [Measure.map_apply (f := fun p : ℝ × ℝ => (p.1+p.2,p.1))
    ((continuous_fst.add continuous_snd).prodMk continuous_fst).measurable
    upperWedge_open.measurableSet]
  apply measure_mono_null (t := univ ×ˢ Iic 0) _ _
  · intro p hp
    refine ⟨mem_univ _, ?_⟩
    have h : p.1+p.2 < p.1 := hp.2
    change p.2 ≤ 0
    linarith
  · rw [Measure.prod_prod, hν, mul_zero]

theorem upperEventLaw_restrict (k : Nat) {c q r : ℝ}
    (hc : 0 ≤ c) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    (upperEventLaw k c q r).restrict upperWedge = upperEventLaw k c q r := by
  rw [upperEventLaw_density k hc hq hr, restrict_withDensity upperWedge_open.measurableSet]
  rw [Measure.restrict_restrict upperWedge_open.measurableSet, Set.inter_self]

theorem jointLaw_restrict_upper (k : Nat) {c q r : ℝ}
    (hc : 0 ≤ c) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    (jointLaw k c q r).restrict upperWedge = upperEventLaw k c q r := by
  have hs (i : Fin 2) : SFinite
      (firstExitLaw (MarkovChain.Identifiability.pairGenerator k c q) i) := by
    unfold firstExitLaw
    infer_instance
  have hz (i : Fin 2) : firstExitLaw (MarkovChain.Identifiability.pairGenerator k c q) i (Iic 0) =
      0 :=
    positive_density_nonpos_zero _
  unfold jointLaw
  rw [Measure.sum_fintype]
  simp only [Fin.sum_univ_succ]
  norm_num [lagLaw, postPairState, Measure.restrict_add]
  change (((markLaw k c q r 0).prod (Measure.dirac 0)).map
      (fun p : ℝ × ℝ => (p.1,p.1))).restrict upperWedge +
    ((((markLaw k c q r 1).prod
        (firstExitLaw (MarkovChain.Identifiability.pairGenerator k c q) 0)).map
      upperShear).restrict upperWedge +
    ((((markLaw k c q r 2).prod
        (firstExitLaw (MarkovChain.Identifiability.pairGenerator k c q) 1)).map
      upperShear).restrict upperWedge +
    ((((markLaw k c q r 3).prod
        (firstExitLaw (MarkovChain.Identifiability.pairGenerator k c q) 0)).map
      (fun p : ℝ × ℝ => (p.1+p.2,p.1))).restrict upperWedge +
    (((markLaw k c q r 4).prod
        (firstExitLaw (MarkovChain.Identifiability.pairGenerator k c q) 1)).map
      (fun p : ℝ × ℝ => (p.1+p.2,p.1))).restrict upperWedge))) = upperEventLaw k c q r
  rw [diagonal_map_restrict_upper_zero,
    lower_map_restrict_upper_zero _ _ (hz 0), lower_map_restrict_upper_zero _ _ (hz 1)]
  simp only [zero_add, add_zero]
  rw [← Measure.restrict_add]
  exact upperEventLaw_restrict k hc hq hr

end Rhone.Statistics.Identifiability
