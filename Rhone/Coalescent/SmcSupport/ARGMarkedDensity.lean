/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcSupport.ARGFiniteHistory

/-! # Selected-event restrictions of the unrestricted event kernel -/
@[expose] public section
namespace Rhone.Coalescent.SmcSupport
open IntervalProcess MeasureTheory ProbabilityTheory
open scoped ENNReal

local instance : MeasurableSpace (Option Action) := ⊤

def argEventAction : Event → Option Action
  | .inl _ => none
  | .inr (.inl ij) => some (.inl ij)
  | .inr (.inr ix) => some (.inr ix.1)

def argActionNatural {s : State} : ActionIndex s → Action
  | .inl ij => .inl (ij.1.val, ij.2.val)
  | .inr i => .inr i.val

def argActionFiber (a : Action) : Set AugmentedState :=
  {y | argEventAction y.2.2 = some a}

theorem argEventAction_measurable : Measurable argEventAction := by
  apply measurable_fun_sum
  · exact measurable_const
  · apply measurable_fun_sum
    · exact measurable_of_countable _
    · exact (measurable_of_countable (fun i : ℕ => some (Sum.inr i : Action))).comp
        measurable_fst

theorem argActionFiber_measurable (a : Action) : MeasurableSet (argActionFiber a) :=
  (argEventAction_measurable.comp measurable_snd.snd)
    (show MeasurableSet ({some a} : Set (Option Action)) from by trivial)

private theorem argActionNatural_injective (s : State) :
    Function.Injective (argActionNatural (s := s)) := by
  intro a b h
  cases a with
  | inl ij =>
    cases b with
    | inl kl =>
      simp only [argActionNatural, Sum.inl.injEq, Prod.mk.injEq] at h
      exact congrArg Sum.inl (Prod.ext (Fin.ext h.1) (Fin.ext h.2))
    | inr k => simp [argActionNatural] at h
  | inr i =>
    cases b with
    | inl kl => simp [argActionNatural] at h
    | inr k => exact congrArg Sum.inr (Fin.ext (Sum.inr.inj h))

private theorem argActionStep_restrict (R : ℝ) (z : AugmentedState)
    (a b : ActionIndex z.1) :
    ((unitUniform.prod unitUniform).map (argActionStep R z b)).restrict
      (argActionFiber (argActionNatural a)) =
    if b = a then (unitUniform.prod unitUniform).map (argActionStep R z b) else 0 := by
  classical
  rw [Measure.restrict_map (argActionStep_measurable R z b)
    (argActionFiber_measurable _)]
  have htag (v : ℝ × ℝ) :
      argEventAction (argActionStep R z b v).2.2 = some (argActionNatural b) := by
    cases b <;> rfl
  have hpre : argActionStep R z b ⁻¹' argActionFiber (argActionNatural a) =
      if b = a then Set.univ else ∅ := by
    ext v
    simp only [Set.mem_preimage, argActionFiber, Set.mem_ofPred_eq, htag, Option.some.injEq]
    rw [(argActionNatural_injective z.1).eq_iff]
    by_cases h : b = a <;> simp [h]
  rw [hpre]
  by_cases h : b = a <;> simp [h]

theorem eventKernel_ARG_action_restrict (R : ℝ) (z : AugmentedState)
    (hm : 1 < z.1.2.2.1) (a : ActionIndex z.1) :
    (eventKernel false R z).restrict (argActionFiber (argActionNatural a)) =
      ENNReal.ofReal ((candidateRate false R z.1 a : ℝ) /
        (totalRate false R z.1 : ℝ)) •
        (unitUniform.prod unitUniform).map (argActionStep R z a) := by
  classical
  rw [eventKernel_ARG_action_mixture R z hm]
  change Measure.restrictₗ _ (∑ b, _) = _
  rw [map_sum]
  simp only [Measure.restrictₗ_apply]
  simp_rw [Measure.restrict_smul, argActionStep_restrict]
  simp

theorem eventKernel_ARG_pair_restrict (R : ℝ) (z : AugmentedState)
    (hm : 1 < z.1.2.2.1) (i j : Fin z.1.2.2.1) :
    (eventKernel false R z).restrict (argActionFiber (.inl (i.val, j.val))) =
      if i.val < j.val then argPairTransition R z i j else 0 := by
  simpa only [argActionNatural] using
    (eventKernel_ARG_action_restrict R z hm (.inl (i, j))).trans
      (argActionStep_pair_density R z hm i j)

theorem eventKernel_ARG_split_restrict (R : ℝ) (hR : 0 ≤ R)
    (z : AugmentedState) (hm : 1 < z.1.2.2.1) (i : Fin z.1.2.2.1) :
    (eventKernel false R z).restrict (argActionFiber (.inr i.val)) =
      argSplitTransition R z i := by
  simpa only [argActionNatural] using
    (eventKernel_ARG_action_restrict R z hm (.inr i)).trans
      (argActionStep_split_density R hR z hm i)

theorem argPrefixLaw_marked_next (R : ℝ) (z : AugmentedState) (n : ℕ)
    (E : Set (ARGPrefix n)) (hE : MeasurableSet E) (a : Action) :
    (((eventProcess false R).pathLaw z).map
      (fun ω => ((fun k : Finset.Iic n => ω k.val), ω (n + 1)))).restrict
        (E ×ˢ argActionFiber a) =
    ((argPrefixLaw R z n).restrict E).compProd
      (((eventProcess false R).stepSeq n).restrict (argActionFiber_measurable a)) := by
  rw [argPrefixLaw_next]
  ext t ht
  rw [Measure.restrict_apply ht, Measure.compProd_apply (ht.inter
    (hE.prod (argActionFiber_measurable a))), Measure.compProd_apply ht]
  simp only [ProbabilityTheory.Kernel.restrict_apply,
    Measure.restrict_apply' (argActionFiber_measurable a)]
  have hsection (h : ARGPrefix n) :
      (eventProcess false R).stepSeq n h
        (Prod.mk h ⁻¹' (t ∩ E ×ˢ argActionFiber a)) =
      E.indicator (fun h => (eventProcess false R).stepSeq n h
        ((Prod.mk h ⁻¹' t) ∩ argActionFiber a)) h := by
    classical
    by_cases hh : h ∈ E
    · rw [Set.indicator_of_mem hh]
      congr 1
      ext y
      simp [hh]
    · rw [Set.indicator_of_notMem hh]
      have hempty : Prod.mk h ⁻¹' (t ∩ E ×ˢ argActionFiber a) = ∅ := by
        ext y
        simp [hh]
      rw [hempty, measure_empty]
  simp_rw [hsection]
  rw [lintegral_indicator hE]

end Rhone.Coalescent.SmcSupport
