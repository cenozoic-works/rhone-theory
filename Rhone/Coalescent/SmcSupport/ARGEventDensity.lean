/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcSupport.ARGActionMixture

/-! # Chronological density of the unrestricted event kernel -/
@[expose] public section
namespace Rhone.Coalescent.SmcSupport
open MeasureTheory IntervalProcess
open scoped ENNReal

theorem argActionStep_pair_density (R : ℝ) (z : AugmentedState)
    (hm : 1 < z.1.2.2.1) (i j : Fin z.1.2.2.1) :
    ENNReal.ofReal ((candidateRate false R z.1 (.inl (i, j)) : ℝ) /
      (totalRate false R z.1 : ℝ)) •
      (unitUniform.prod unitUniform).map (argActionStep R z (.inl (i, j))) =
    if i.val < j.val then argPairTransition R z i j else 0 := by
  have ht := unrestricted_totalRate_positive R z.1 (by omega)
  have hq : 0 < (totalRate false R z.1 : ℝ) := by exact_mod_cast ht
  by_cases hij : i.val < j.val
  · have hc : candidateRate false R z.1 (.inl (i, j)) = 1 := by
      simp [candidateRate, hij]
    rw [hc, NNReal.coe_one, ite_eq_left hij]
    let g : ℝ → AugmentedState := fun t =>
      (atTime t (coalSuccessor z.1 i j), (t, .inr (.inl (i.val, j.val))))
    have hg : Measurable g :=
      (measurable_id.prodMk measurable_const).prodMk
        (measurable_id.prodMk measurable_const)
    have hclock : (unitUniform.prod unitUniform).map
        (fun v : ℝ × ℝ => z.1.1 - Real.log v.1 / (totalRate false R z.1 : ℝ)) =
        (volume.restrict (Set.Ioi z.1.1)).withDensity
          (fun t => ENNReal.ofReal ((totalRate false R z.1 : ℝ) *
            Real.exp (-(totalRate false R z.1 : ℝ) * (t - z.1.1)))) := by
      change (unitUniform.prod unitUniform).map
        ((fun u : ℝ => z.1.1 - Real.log u / (totalRate false R z.1 : ℝ)) ∘ Prod.fst) = _
      rw [← Measure.map_map (by fun_prop) measurable_fst, Measure.map_fst_prod]
      simp only [measure_univ, one_smul]
      exact inverseClock_shift_density _ hq _
    change ENNReal.ofReal (1 / (totalRate false R z.1 : ℝ)) •
      (unitUniform.prod unitUniform).map
        (g ∘ fun v => z.1.1 - Real.log v.1 / (totalRate false R z.1 : ℝ)) = _
    rw [← Measure.map_map hg (by fun_prop), hclock, ← Measure.map_smul _ hg.aemeasurable]
    unfold argPairTransition
    apply congrArg (fun μ : Measure ℝ => μ.map g)
    rw [← withDensity_smul _ (by fun_prop)]
    congr 1
    funext t
    change ENNReal.ofReal (1 / (totalRate false R z.1 : ℝ)) *
      ENNReal.ofReal ((totalRate false R z.1 : ℝ) *
        Real.exp (-(totalRate false R z.1 : ℝ) * (t - z.1.1))) = _
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  · have hc : candidateRate false R z.1 (.inl (i, j)) = 0 := by
      simp [candidateRate, hij]
    simp [hc, hij]

theorem argActionStep_split_density (R : ℝ) (hR : 0 ≤ R)
    (z : AugmentedState) (hm : 1 < z.1.2.2.1) (i : Fin z.1.2.2.1) :
    ENNReal.ofReal ((candidateRate false R z.1 (.inr i) : ℝ) /
      (totalRate false R z.1 : ℝ)) •
      (unitUniform.prod unitUniform).map (argActionStep R z (.inr i)) =
    argSplitTransition R z i := by
  have ht := unrestricted_totalRate_positive R z.1 (by omega)
  have hq : 0 < (totalRate false R z.1 : ℝ) := by exact_mod_cast ht
  have hc : (candidateRate false R z.1 (.inr i) : ℝ) =
      R / 2 * hullLength (z.1.2.2.2 i).2 := by
    exact candidateRate_split_eq false R hR z.1 i
  rw [hc]
  by_cases hl : 0 < hullLength (z.1.2.2.2 i).2
  · have hab : hullLo (z.1.2.2.2 i).2 < hullHi (z.1.2.2.2 i).2 := by
      simpa only [hullLength, lt_max_iff, lt_self_iff_false, false_or, sub_pos] using hl
    have hlen : hullLength (z.1.2.2.2 i).2 =
        hullHi (z.1.2.2.2 i).2 - hullLo (z.1.2.2.2 i).2 :=
      max_eq_right (sub_pos.mpr hab).le
    let g : ℝ × ℝ → AugmentedState := fun p =>
      (atTime p.1 (splitSuccessor z.1 i p.2), (p.1, .inr (.inr (i.val, p.2))))
    have hs : Measurable (fun p : ℝ × ℝ => splitSuccessor z.1 i p.2) :=
      (splitSuccessorFiber_measurable z.1.2.2.1 i).comp
        (show Measurable (fun p : ℝ × ℝ => ((z.1.1, z.1.2.1, z.1.2.2.2), p.2)) from
          measurable_const.prodMk measurable_snd)
    have hg : Measurable g := (measurable_fst.prodMk hs.snd).prodMk
      (measurable_fst.prodMk (measurable_inr.comp
        (measurable_inr.comp (measurable_const.prodMk measurable_snd))))
    have hcmap : (unitUniform.prod unitUniform).map
        (fun v : ℝ × ℝ =>
          (z.1.1 - Real.log v.1 / (totalRate false R z.1 : ℝ),
           hullLo (z.1.2.2.2 i).2 + hullLength (z.1.2.2.2 i).2 * v.2)) =
        ((volume.restrict (Set.Ioi z.1.1)).withDensity
          (fun t => ENNReal.ofReal ((totalRate false R z.1 : ℝ) *
            Real.exp (-(totalRate false R z.1 : ℝ) * (t - z.1.1))))).prod
          (ENNReal.ofReal ((hullLength (z.1.2.2.2 i).2)⁻¹) •
            volume.restrict (Set.Ioo (hullLo (z.1.2.2.2 i).2)
              (hullHi (z.1.2.2.2 i).2))) := by
      change (unitUniform.prod unitUniform).map
        (Prod.map (fun u : ℝ => z.1.1 - Real.log u / (totalRate false R z.1 : ℝ))
          (fun u : ℝ => hullLo (z.1.2.2.2 i).2 + hullLength (z.1.2.2.2 i).2 * u)) = _
      rw [← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
        inverseClock_shift_density _ hq _]
      rw [hlen, affineCut_uniform_law _ _ hab]
    change ENNReal.ofReal (R / 2 * hullLength (z.1.2.2.2 i).2 /
      (totalRate false R z.1 : ℝ)) • (unitUniform.prod unitUniform).map
        (g ∘ fun v => (z.1.1 - Real.log v.1 / (totalRate false R z.1 : ℝ),
          hullLo (z.1.2.2.2 i).2 + hullLength (z.1.2.2.2 i).2 * v.2)) = _
    rw [← Measure.map_map hg (by fun_prop), hcmap,
      Measure.prod_smul_right, Measure.map_smul _ hg.aemeasurable, smul_smul,
      ← Measure.map_smul _ hg.aemeasurable,
      prod_withDensity_left (by fun_prop)]
    unfold argSplitTransition
    apply congrArg (fun μ : Measure (ℝ × ℝ) => μ.map g)
    rw [← withDensity_smul _ (by fun_prop)]
    congr 1
    funext p
    change (ENNReal.ofReal (R / 2 * hullLength (z.1.2.2.2 i).2 /
      (totalRate false R z.1 : ℝ)) * ENNReal.ofReal ((hullLength (z.1.2.2.2 i).2)⁻¹)) *
      ENNReal.ofReal ((totalRate false R z.1 : ℝ) *
        Real.exp (-(totalRate false R z.1 : ℝ) * (p.1 - z.1.1))) = _
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  · have hzero : hullLength (z.1.2.2.2 i).2 = 0 :=
      le_antisymm (le_of_not_gt hl) (le_max_left _ _)
    have hab : hullHi (z.1.2.2.2 i).2 ≤ hullLo (z.1.2.2.2 i).2 := by
      have h := le_max_right 0 (hullHi (z.1.2.2.2 i).2 - hullLo (z.1.2.2.2 i).2)
      change hullLength (z.1.2.2.2 i).2 = 0 at hzero
      rw [← hullLength, hzero] at h
      linarith
    simp [hzero, argSplitTransition, Set.Ioo_eq_empty_of_le hab]

theorem eventKernel_ARG_density (R : ℝ) (hR : 0 ≤ R)
    (z : AugmentedState) (hm : 1 < z.1.2.2.1) :
    eventKernel false R z =
      (∑ i, ∑ j, if i.val < j.val then argPairTransition R z i j else 0) +
      ∑ i, argSplitTransition R z i := by
  rw [eventKernel_ARG_action_mixture R z hm, Fintype.sum_sum_type]
  congr 1
  · rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact argActionStep_pair_density R z hm i j
  · apply Finset.sum_congr rfl
    intro i _
    exact argActionStep_split_density R hR z hm i

end Rhone.Coalescent.SmcSupport
