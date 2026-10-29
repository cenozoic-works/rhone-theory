/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Rhone.Coalescent.SmcSupport.ARGWordHistory
public import Rhone.Coalescent.SmcSupport.StateMeasurable
public import Rhone.Coalescent.FiniteIntervalGenealogyMeas
public import Mathlib.Probability.Kernel.Composition.WithDensity

/-!
# Pair-or-idle kernel restriction and exact extra chronological survival

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/
@[expose] public section
namespace Rhone.Coalescent.SmcSupport
open MeasureTheory ProbabilityTheory IntervalProcess
open scoped ENNReal

def argNoSplitEvent : Set AugmentedState :=
  {y | (genealogyEventCode y.2.2).1 ≠ 2}

theorem argNoSplitEvent_measurable : MeasurableSet argNoSplitEvent :=
  (measurableSet_eq_fun (genealogyEventCode_measurable.comp measurable_snd.snd).fst
    measurable_const).compl

noncomputable def argNoSplitFactor (R : ℝ) (z y : AugmentedState) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-((totalRate false R z.1 : ℝ) -
    (totalRate false 0 z.1 : ℝ)) * (y.1.1 - z.1.1)))

theorem argNoSplitFactor_measurable (R : ℝ) (z : AugmentedState) :
    Measurable (argNoSplitFactor R z) := by
  unfold argNoSplitFactor
  fun_prop

theorem argTotalRate_measurable (R : ℝ) :
    Measurable (fun s : State => (totalRate false R s : ℝ)) := by
  intro t ht
  change MeasurableSet {s : State | (totalRate false R s : ℝ) ∈ t}
  apply statePredicate_measurable
  intro m
  exact (totalRateFiber_coe_measurable false R m) ht

theorem argNoSplitFactor_joint_measurable (R : ℝ) :
    Measurable (Function.uncurry (argNoSplitFactor R)) := by
  unfold argNoSplitFactor Function.uncurry
  exact (Real.measurable_exp.comp
    ((((argTotalRate_measurable R).comp measurable_fst.fst).sub
      ((argTotalRate_measurable 0).comp measurable_fst.fst)).neg.mul
        (measurable_snd.fst.fst.sub measurable_fst.fst.fst))).ennreal_ofReal

theorem argPairTransition_noSplitFactor (R : ℝ) (z : AugmentedState)
    (i j : Fin z.1.2.2.1) :
    argPairTransition R z i j =
      (argPairTransition 0 z i j).withDensity (argNoSplitFactor R z) := by
  let F (t : ℝ) : AugmentedState :=
    (atTime t (coalSuccessor z.1 i j), (t, .inr (.inl (i.val, j.val))))
  have hF : Measurable F :=
    (measurable_id.prodMk measurable_const).prodMk
      (measurable_id.prodMk measurable_const)
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_withDensity_eq_lintegral_mul _ (argNoSplitFactor_measurable R z) hg]
  change (∫⁻ y, g y ∂((volume.restrict (Set.Ioi z.1.1)).withDensity
    (fun t => ENNReal.ofReal (Real.exp (-(totalRate false R z.1 : ℝ) *
      (t - z.1.1))))).map F) = _
  rw [lintegral_map hg hF,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop)
      (show Measurable (fun t => g (F t)) from hg.comp hF)]
  change _ = ∫⁻ y, argNoSplitFactor R z y * g y
    ∂((volume.restrict (Set.Ioi z.1.1)).withDensity
      (fun t => ENNReal.ofReal (Real.exp (-(totalRate false 0 z.1 : ℝ) *
        (t - z.1.1))))).map F
  rw [lintegral_map (show Measurable (fun y => argNoSplitFactor R z y * g y) from
      (argNoSplitFactor_measurable R z).mul hg) hF,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop)
      (show Measurable (fun t => argNoSplitFactor R z (F t) * g (F t)) from
        ((argNoSplitFactor_measurable R z).mul hg).comp hF)]
  apply lintegral_congr
  intro t
  change ENNReal.ofReal (Real.exp (-(totalRate false R z.1 : ℝ) * (t - z.1.1))) * g (F t) =
    ENNReal.ofReal (Real.exp (-(totalRate false 0 z.1 : ℝ) * (t - z.1.1))) *
      (ENNReal.ofReal (Real.exp (-((totalRate false R z.1 : ℝ) -
        (totalRate false 0 z.1 : ℝ)) * (t - z.1.1))) * g (F t))
  rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
  have he : -(totalRate false R z.1 : ℝ) * (t - z.1.1) =
      -(totalRate false 0 z.1 : ℝ) * (t - z.1.1) +
        -((totalRate false R z.1 : ℝ) - (totalRate false 0 z.1 : ℝ)) *
          (t - z.1.1) := by ring
  rw [he]

theorem argPairTransition_noSplit_restrict (R : ℝ) (z : AugmentedState)
    (i j : Fin z.1.2.2.1) :
    (argPairTransition R z i j).restrict argNoSplitEvent = argPairTransition R z i j := by
  rw [argPairTransition, Measure.restrict_map
    (show Measurable (fun t : ℝ => (atTime t (coalSuccessor z.1 i j),
      (t, .inr (.inl (i.val, j.val)))) : ℝ → AugmentedState) from
      (measurable_id.prodMk measurable_const).prodMk
        (measurable_id.prodMk measurable_const)) argNoSplitEvent_measurable]
  have hp : (fun t : ℝ => (atTime t (coalSuccessor z.1 i j),
      (t, .inr (.inl (i.val, j.val)))) : ℝ → AugmentedState) ⁻¹' argNoSplitEvent = Set.univ := by
    ext t
    simp [argNoSplitEvent, genealogyEventCode]
  rw [hp, Measure.restrict_univ]

theorem argSplitTransition_noSplit_restrict (R : ℝ) (z : AugmentedState)
    (i : Fin z.1.2.2.1) :
    (argSplitTransition R z i).restrict argNoSplitEvent = 0 := by
  rw [argSplitTransition, Measure.restrict_map
    (show Measurable (fun p : ℝ × ℝ => (atTime p.1 (splitSuccessor z.1 i p.2),
      (p.1, .inr (.inr (i.val, p.2))))) from by
      have hs : Measurable (fun p : ℝ × ℝ => splitSuccessor z.1 i p.2) :=
        (splitSuccessorFiber_measurable z.1.2.2.1 i).comp
          (show Measurable (fun p : ℝ × ℝ => ((z.1.1, z.1.2.1, z.1.2.2.2), p.2)) from
            measurable_const.prodMk measurable_snd)
      exact (measurable_fst.prodMk hs.snd).prodMk
        (measurable_fst.prodMk (measurable_inr.comp
          (measurable_inr.comp (measurable_const.prodMk measurable_snd)))))
    argNoSplitEvent_measurable]
  have hp : (fun p : ℝ × ℝ => (atTime p.1 (splitSuccessor z.1 i p.2),
      (p.1, .inr (.inr (i.val, p.2))))) ⁻¹' argNoSplitEvent = ∅ := by
    ext p
    simp [argNoSplitEvent, genealogyEventCode]
  rw [hp, Measure.restrict_empty, Measure.map_zero]
private theorem pairSum_withDensity (s : State) (f : AugmentedState → ℝ≥0∞)
    (μ : Fin s.2.2.1 → Fin s.2.2.1 → Measure AugmentedState) :
    (∑ i, ∑ j, μ i j).withDensity f = ∑ i, ∑ j, (μ i j).withDensity f := by
  classical
  have hadd : ∀ (u : Finset (Fin s.2.2.1)) (g : Fin s.2.2.1 → Measure AugmentedState),
      (∑ i ∈ u, g i).withDensity f = ∑ i ∈ u, (g i).withDensity f := by
    intro u g
    induction u using Finset.induction_on with
    | empty => simp
    | @insert a u ha ih => simp [ha, withDensity_add_measure, ih]
  rw [hadd Finset.univ]
  apply Finset.sum_congr rfl
  intro i _
  exact hadd Finset.univ (μ i)

theorem eventKernel_noSplitFactor (R : ℝ) (hR : 0 ≤ R) (z : AugmentedState) :
    (eventKernel false R z).restrict argNoSplitEvent =
      (eventKernel false 0 z).withDensity (argNoSplitFactor R z) := by
  classical
  by_cases hm : 1 < z.1.2.2.1
  · rw [eventKernel_ARG_density R hR z hm,
      eventKernel_ARG_density 0 (by positivity) z hm]
    change Measure.restrictₗ _ ((∑ i, ∑ j, _) + ∑ i, _) = _
    simp only [map_add, map_sum, Measure.restrictₗ_apply]
    simp_rw [
      argSplitTransition_noSplit_restrict, Finset.sum_const_zero, add_zero,
      argSplitTransition_zero, Finset.sum_const_zero, add_zero]
    rw [pairSum_withDensity]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i.val < j.val
    · simp only [ite_eq_left hij]
      rw [argPairTransition_noSplit_restrict, argPairTransition_noSplitFactor]
    · simp [hij]
  · have hle : z.1.2.2.1 ≤ 1 := Nat.le_of_not_gt hm
    have hk (r : ℝ) : eventKernel false r z = Measure.dirac (z.1, (z.1.1, .inl ())) := by
      rw [eventKernel_apply]
      simp [sampleStep, hle]
    rw [hk R, hk 0, restrict_dirac' argNoSplitEvent_measurable,
      dirac_withDensity' (argNoSplitFactor_measurable R z)]
    simp [argNoSplitEvent, genealogyEventCode, argNoSplitFactor]
end Rhone.Coalescent.SmcSupport
