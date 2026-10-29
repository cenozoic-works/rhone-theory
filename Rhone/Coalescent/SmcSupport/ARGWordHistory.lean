/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcSupport.ARGMarkedDensity

/-! # Finite event words integrate the pair and split densities -/
@[expose] public section
namespace Rhone.Coalescent.SmcSupport
open IntervalProcess MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable def argActionTransition (R : ℝ) (z : AugmentedState) :
    ActionIndex z.1 → Measure AugmentedState
  | .inl ij => if ij.1.val < ij.2.val then argPairTransition R z ij.1 ij.2 else 0
  | .inr i => argSplitTransition R z i

noncomputable def argNaturalTransition (R : ℝ) (z : AugmentedState)
    (a : Action) : Measure AugmentedState := by
  classical
  exact if 1 < z.1.2.2.1 then
    ∑ b : ActionIndex z.1,
      if argActionNatural b = a then argActionTransition R z b else 0
  else 0

private theorem argActionStep_natural_restrict (R : ℝ) (z : AugmentedState)
    (a : Action) (b : ActionIndex z.1) :
    ((unitUniform.prod unitUniform).map (argActionStep R z b)).restrict
      (argActionFiber a) =
    if argActionNatural b = a then
      (unitUniform.prod unitUniform).map (argActionStep R z b) else 0 := by
  classical
  rw [Measure.restrict_map (argActionStep_measurable R z b)
    (argActionFiber_measurable a)]
  have htag (v : ℝ × ℝ) :
      argEventAction (argActionStep R z b v).2.2 = some (argActionNatural b) := by
    cases b <;> rfl
  have hpre : argActionStep R z b ⁻¹' argActionFiber a =
      if argActionNatural b = a then Set.univ else ∅ := by
    ext v
    simp only [Set.mem_preimage, argActionFiber, Set.mem_ofPred_eq, htag, Option.some.injEq]
    by_cases h : argActionNatural b = a <;> simp [h]
  rw [hpre]
  by_cases h : argActionNatural b = a <;> simp [h]

theorem eventKernel_ARG_natural_restrict (R : ℝ) (hR : 0 ≤ R)
    (z : AugmentedState) (a : Action) :
    (eventKernel false R z).restrict (argActionFiber a) =
      argNaturalTransition R z a := by
  classical
  by_cases hm : 1 < z.1.2.2.1
  · rw [eventKernel_ARG_action_mixture R z hm]
    change Measure.restrictₗ _ (∑ b, _) = _
    rw [map_sum]
    simp only [Measure.restrictₗ_apply, Measure.restrict_smul,
      argActionStep_natural_restrict, argNaturalTransition, ite_eq_left hm]
    apply Finset.sum_congr rfl
    intro b _
    by_cases h : argActionNatural b = a
    · simp only [ite_eq_left h]
      cases b with
      | inl ij => exact argActionStep_pair_density R z hm ij.1 ij.2
      | inr i => exact argActionStep_split_density R hR z hm i
    · simp [h]
  · have hle : z.1.2.2.1 ≤ 1 := Nat.le_of_not_gt hm
    have hk : eventKernel false R z = Measure.dirac (z.1, (z.1.1, .inl ())) := by
      rw [eventKernel_apply]
      simp [sampleStep, hle]
    rw [hk, restrict_dirac' (argActionFiber_measurable a)]
    simp [argNaturalTransition, hm, argActionFiber, argEventAction]

def argWordSet (n : ℕ) (w : ℕ → Action) : Set (ARGPrefix n) :=
  {h | ∀ j : Fin n,
    h ⟨j.val + 1, Finset.mem_Iic.mpr (by omega)⟩ ∈ argActionFiber (w j.val)}

theorem argWordSet_measurable (n : ℕ) (w : ℕ → Action) :
    MeasurableSet (argWordSet n w) := by
  simp only [argWordSet, Set.ofPred_forall]
  change MeasurableSet (⋂ j : Fin n,
    {h : ARGPrefix n | h ⟨j.val + 1, Finset.mem_Iic.mpr (by omega)⟩ ∈
      argActionFiber (w j.val)})
  exact MeasurableSet.iInter (fun j =>
    (argActionFiber_measurable (w j.val)).preimage (measurable_pi_apply _))

noncomputable def argWordPrefixLaw (R : ℝ) (z : AugmentedState)
    (n : ℕ) (w : ℕ → Action) : Measure (ARGPrefix n) :=
  (argPrefixLaw R z n).restrict (argWordSet n w)

instance argWordPrefixLaw_finite (R : ℝ) (z : AugmentedState)
    (n : ℕ) (w : ℕ → Action) : IsFiniteMeasure (argWordPrefixLaw R z n w) := by
  unfold argWordPrefixLaw
  infer_instance

theorem argWordPrefixLaw_lintegral_next (R : ℝ) (hR : 0 ≤ R)
    (z : AugmentedState) (n : ℕ) (w : ℕ → Action)
    (f : ARGPrefix n × AugmentedState → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ p, f p ∂((((eventProcess false R).pathLaw z).map
      (fun ω => ((fun k : Finset.Iic n => ω k.val), ω (n + 1)))).restrict
        (argWordSet n w ×ˢ argActionFiber (w n))) =
    ∫⁻ h, ∫⁻ y, f (h, y)
      ∂argNaturalTransition R (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩) (w n)
      ∂argWordPrefixLaw R z n w := by
  rw [argPrefixLaw_marked_next R z n _ (argWordSet_measurable n w),
    Measure.lintegral_compProd hf]
  congr 1
  funext h
  rw [Kernel.restrict_apply, Rhone.MarkovChain.DiscreteProcess.stepSeq, Kernel.comap_apply]
  change (∫⁻ y, f (h, y) ∂(eventKernel false R
    (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩)).restrict (argActionFiber (w n))) = _
  rw [eventKernel_ARG_natural_restrict R hR]

def argPrefixSplit (n : ℕ) (h : ARGPrefix (n + 1)) : ARGPrefix n × AugmentedState :=
  ((fun k : Finset.Iic n => h ⟨k.val, Finset.mem_Iic.mpr
      ((Finset.mem_Iic.mp k.property).trans (Nat.le_succ n))⟩),
    h ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩)

theorem argPrefixSplit_measurable (n : ℕ) : Measurable (argPrefixSplit n) := by
  apply Measurable.prodMk
  · exact measurable_pi_iff.mpr (fun k => measurable_pi_apply _)
  · exact measurable_pi_apply _

private theorem argWordSet_split (n : ℕ) (w : ℕ → Action) :
    argWordSet (n + 1) w =
      argPrefixSplit n ⁻¹' (argWordSet n w ×ˢ argActionFiber (w n)) := by
  ext h
  change (∀ j : Fin (n + 1), _) ↔
    (∀ j : Fin n, _) ∧ _
  constructor
  · intro hh
    constructor
    · intro j
      exact hh ⟨j.val, by omega⟩
    · exact hh ⟨n, by omega⟩
  · rintro ⟨hh, hn⟩ j
    by_cases hj : j.val < n
    · exact hh ⟨j.val, hj⟩
    · have he : j.val = n := by omega
      simpa only [argPrefixSplit, he] using hn

theorem argWordPrefixLaw_next_map (R : ℝ) (z : AugmentedState)
    (n : ℕ) (w : ℕ → Action) :
    (argWordPrefixLaw R z (n + 1) w).map (argPrefixSplit n) =
    (argWordPrefixLaw R z n w).compProd
      (((eventProcess false R).stepSeq n).restrict (argActionFiber_measurable (w n))) := by
  rw [argWordPrefixLaw, argWordSet_split,
    ← Measure.restrict_map (argPrefixSplit_measurable n)
      ((argWordSet_measurable n w).prod (argActionFiber_measurable (w n)))]
  have hmap : (argPrefixLaw R z (n + 1)).map (argPrefixSplit n) =
      ((eventProcess false R).pathLaw z).map
        (fun ω => ((fun k : Finset.Iic n => ω k.val), ω (n + 1))) := by
    rw [argPrefixLaw, Measure.map_map (argPrefixSplit_measurable n) (by fun_prop)]
    rfl
  rw [hmap, argPrefixLaw_marked_next R z n _ (argWordSet_measurable n w)]
  rfl

theorem argSplitTransition_zero (z : AugmentedState) (i : Fin z.1.2.2.1) :
    argSplitTransition 0 z i = 0 := by
  simp [argSplitTransition]

theorem eventKernel_zero_split_restrict (z : AugmentedState) (i : ℕ) :
    (eventKernel false 0 z).restrict (argActionFiber (.inr i)) = 0 := by
  classical
  rw [eventKernel_ARG_natural_restrict 0 (by positivity)]
  unfold argNaturalTransition
  split_ifs
  · apply Finset.sum_eq_zero
    intro b _
    cases b with
    | inl ij => simp [argActionNatural]
    | inr j => simp [argActionNatural, argActionTransition, argSplitTransition_zero]
  · rfl

end Rhone.Coalescent.SmcSupport
