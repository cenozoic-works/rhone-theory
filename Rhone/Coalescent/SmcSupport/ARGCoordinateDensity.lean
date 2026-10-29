/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcSupport.ARGWordHistory

/-! # Chronological integrals of the ordered-pair and genomic-split measures -/
@[expose] public section
namespace Rhone.Coalescent.SmcSupport
open IntervalProcess MeasureTheory
open scoped ENNReal

theorem argPairTransition_lintegral (R : ℝ) (z : AugmentedState)
    (i j : Fin z.1.2.2.1) (f : AugmentedState → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ y, f y ∂argPairTransition R z i j =
    ∫⁻ t in Set.Ioi z.1.1,
      ENNReal.ofReal (Real.exp (-(totalRate false R z.1 : ℝ) * (t - z.1.1))) *
        f (atTime t (coalSuccessor z.1 i j), (t, .inr (.inl (i.val, j.val)))) := by
  have hg : Measurable (fun t : ℝ =>
      ((atTime t (coalSuccessor z.1 i j), (t, .inr (.inl (i.val, j.val)))) :
        AugmentedState)) :=
    (measurable_id.prodMk measurable_const).prodMk
      (measurable_id.prodMk measurable_const)
  rw [argPairTransition, lintegral_map hf hg]
  exact lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (hf.comp hg)

theorem argSplitTransition_lintegral (R : ℝ) (z : AugmentedState)
    (i : Fin z.1.2.2.1) (f : AugmentedState → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ y, f y ∂argSplitTransition R z i =
    ∫⁻ p,
      ENNReal.ofReal (R / 2 *
        Real.exp (-(totalRate false R z.1 : ℝ) * (p.1 - z.1.1))) *
        f (atTime p.1 (splitSuccessor z.1 i p.2), (p.1, .inr (.inr (i.val, p.2))))
      ∂((volume.restrict (Set.Ioi z.1.1)).prod
        (volume.restrict (Set.Ioo (hullLo (z.1.2.2.2 i).2) (hullHi (z.1.2.2.2 i).2)))) := by
  have hs : Measurable (fun p : ℝ × ℝ => splitSuccessor z.1 i p.2) :=
    (splitSuccessorFiber_measurable z.1.2.2.1 i).comp
      (show Measurable (fun p : ℝ × ℝ => ((z.1.1, z.1.2.1, z.1.2.2.2), p.2)) from
        measurable_const.prodMk measurable_snd)
  have hg : Measurable (fun p : ℝ × ℝ =>
      ((atTime p.1 (splitSuccessor z.1 i p.2), (p.1, .inr (.inr (i.val, p.2)))) :
        AugmentedState)) :=
    (measurable_fst.prodMk hs.snd).prodMk
      (measurable_fst.prodMk (measurable_inr.comp
        (measurable_inr.comp (measurable_const.prodMk measurable_snd))))
  rw [argSplitTransition, lintegral_map hf hg]
  exact lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (hf.comp hg)

end Rhone.Coalescent.SmcSupport
