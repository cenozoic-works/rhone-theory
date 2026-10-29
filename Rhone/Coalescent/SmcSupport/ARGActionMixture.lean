/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcSupport.SelectorProduct
public import Rhone.Coalescent.SmcSupport.HistoryCoordinates

/-! # Finite action decomposition of the unrestricted event sampler -/
@[expose] public section
namespace Rhone.Coalescent.SmcSupport
open MeasureTheory IntervalProcess
open scoped ENNReal

noncomputable def argActionStep (R : ℝ) (z : AugmentedState)
    (a : ActionIndex z.1) (v : ℝ × ℝ) : AugmentedState :=
  let t := z.1.1 - Real.log v.1 / (totalRate false R z.1 : ℝ)
  match a with
  | .inl ij => (atTime t (coalSuccessor z.1 ij.1 ij.2),
      (t, .inr (.inl (ij.1.val, ij.2.val))))
  | .inr i =>
    let x := hullLo (z.1.2.2.2 i).2 + hullLength (z.1.2.2.2 i).2 * v.2
    (atTime t (splitSuccessor z.1 i x), (t, .inr (.inr (i.val, x))))

theorem argActionStep_measurable (R : ℝ) (z : AugmentedState)
    (a : ActionIndex z.1) : Measurable (argActionStep R z a) := by
  let t : ℝ × ℝ → ℝ := fun v => z.1.1 - Real.log v.1 / (totalRate false R z.1 : ℝ)
  have ht : Measurable t := by fun_prop
  cases a with
  | inl ij => exact (ht.prodMk measurable_const).prodMk (ht.prodMk measurable_const)
  | inr i =>
    let x : ℝ × ℝ → ℝ := fun v =>
      hullLo (z.1.2.2.2 i).2 + hullLength (z.1.2.2.2 i).2 * v.2
    have hx : Measurable x := by fun_prop
    have hs : Measurable (fun v : ℝ × ℝ => splitSuccessor z.1 i (x v)) := by
      exact (splitSuccessorFiber_measurable z.1.2.2.1 i).comp
        (show Measurable (fun v : ℝ × ℝ =>
          ((z.1.1, z.1.2.1, z.1.2.2.2), x v)) from measurable_const.prodMk hx)
    exact (ht.prodMk hs.snd).prodMk
      (ht.prodMk (measurable_inr.comp (measurable_inr.comp (measurable_const.prodMk hx))))

theorem eventKernel_ARG_action_mixture (R : ℝ) (z : AugmentedState)
    (hm : 1 < z.1.2.2.1) :
    eventKernel false R z = ∑ a : ActionIndex z.1,
      ENNReal.ofReal ((candidateRate false R z.1 a : ℝ) /
        (totalRate false R z.1 : ℝ)) •
      (unitUniform.prod unitUniform).map (argActionStep R z a) := by
  classical
  have ht := unrestricted_totalRate_positive R z.1 (by omega)
  let f : ℝ × (ℝ × ℝ) → AugmentedState := fun p =>
    sampleStep false R z.1 ![p.1, p.2.1, p.2.2]
  have hf : Measurable f := by
    change Measurable ((fun p : State × Noise => sampleStep false R p.1 p.2) ∘
      (fun p : ℝ × (ℝ × ℝ) => (z.1, ![p.1, p.2.1, p.2.2])))
    apply (sampleStep_measurable false R).comp
    apply measurable_const.prodMk
    apply measurable_pi_iff.mpr
    intro i
    fin_cases i <;> fun_prop
  let : MeasurableSpace (Option (ActionIndex z.1)) := ⊤
  have hs : Measurable (selectorScalar false R z.1) :=
    chooseByRate_measurable (fun b _ => (candidateRate false R z.1 b : ℝ))
      (fun _ => measurable_const) Finset.univ.toList
      (fun v => v * (totalRate false R z.1 : ℝ)) (measurable_id.mul_const _)
  have hE (a : ActionIndex z.1) : MeasurableSet
      {v | selectorScalar false R z.1 v = some a} :=
    hs (show MeasurableSet ({some a} : Set (Option (ActionIndex z.1))) from by trivial)
  have hbranch (a : ActionIndex z.1) (ω : ℝ)
      (hω : selectorScalar false R z.1 ω = some a) (v : ℝ × ℝ) :
      f (ω, v) = argActionStep R z a v := by
    have hselect : selectedAction false R z.1 ![ω, v.1, v.2] = some a := hω
    simp only [f, sampleStep, not_le.mpr hm, ne_of_gt ht, or_self,
      hselect]
    cases a <;> rfl
  rw [eventKernel_apply]
  calc
    noiseLaw.map (fun u => sampleStep false R z.1 u) =
        (noiseLaw.map (fun u => (u 0, u 1, u 2))).map f := by
      rw [Measure.map_map hf (by fun_prop)]
      congr 1
    _ = _ := by
      rw [noiseLaw_coordinates,
        map_prod_of_partition unitUniform (unitUniform.prod unitUniform)
          _ hE (selectorScalar_partition false R z.1 ht) f hf
          (argActionStep R z) (argActionStep_measurable R z) hbranch]
      apply Finset.sum_congr rfl
      intro a _
      rw [selectorScalar_mass false R z.1 ht a]
end Rhone.Coalescent.SmcSupport
