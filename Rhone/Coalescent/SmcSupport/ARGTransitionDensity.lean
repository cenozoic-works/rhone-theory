/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcSupport.HistoryNoise
public import Mathlib.MeasureTheory.Measure.WithDensity

/-! # Chronological branch measures for the unrestricted sampler -/
@[expose] public section
namespace Rhone.Coalescent.SmcSupport
open IntervalProcess MeasureTheory ProbabilityTheory

noncomputable def argPairTransition (R : ℝ) (z : AugmentedState)
    (i j : Fin z.1.2.2.1) : Measure AugmentedState :=
  ((volume.restrict (Set.Ioi z.1.1)).withDensity
    (fun t => ENNReal.ofReal (Real.exp (-(totalRate false R z.1 : ℝ) * (t - z.1.1))))).map
    (fun t => (atTime t (coalSuccessor z.1 i j),
      (t, .inr (.inl (i.val, j.val)))))

noncomputable def argSplitTransition (R : ℝ) (z : AugmentedState)
    (i : Fin z.1.2.2.1) : Measure AugmentedState :=
  (((volume.restrict (Set.Ioi z.1.1)).prod
    (volume.restrict (Set.Ioo (hullLo (z.1.2.2.2 i).2)
      (hullHi (z.1.2.2.2 i).2)))).withDensity
    (fun p => ENNReal.ofReal (R / 2 *
      Real.exp (-(totalRate false R z.1 : ℝ) * (p.1 - z.1.1))))).map
    (fun p => (atTime p.1 (splitSuccessor z.1 i p.2),
      (p.1, .inr (.inr (i.val, p.2)))))

end Rhone.Coalescent.SmcSupport
