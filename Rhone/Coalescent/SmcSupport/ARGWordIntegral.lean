/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcSupport.ARGActionTransitions

/-! # Integrating finite event words: prefix joins and the word-prefix law -/

@[expose] public section

namespace Rhone.Coalescent.SmcSupport
open IntervalProcess MeasureTheory ProbabilityTheory
open scoped ENNReal

def argPrefixJoin (n : ℕ) (p : ARGPrefix n × AugmentedState) : ARGPrefix (n + 1) :=
  fun k => if hk : k.val ≤ n then p.1 ⟨k.val, Finset.mem_Iic.mpr hk⟩ else p.2

theorem argPrefixJoin_measurable (n : ℕ) : Measurable (argPrefixJoin n) := by
  apply measurable_pi_iff.mpr
  intro k
  by_cases hk : k.val ≤ n
  · simpa only [argPrefixJoin, dite_eq_left hk, Function.comp_def] using
      (measurable_pi_apply (⟨k.val, Finset.mem_Iic.mpr hk⟩ : Finset.Iic n)).comp measurable_fst
  · simpa only [argPrefixJoin, dite_eq_right hk] using
      (measurable_snd : Measurable (fun p : ARGPrefix n × AugmentedState => p.2))

theorem argPrefixJoin_split (n : ℕ) (h : ARGPrefix (n + 1)) :
    argPrefixJoin n (argPrefixSplit n h) = h := by
  funext k
  by_cases hk : k.val ≤ n
  · simp only [argPrefixJoin, dite_eq_left hk, argPrefixSplit]
  · have he : k.val = n + 1 := by have := Finset.mem_Iic.mp k.property; omega
    simp only [argPrefixJoin, dite_eq_right hk, argPrefixSplit]
    congr 1
    exact Subtype.ext he.symm

theorem argWordPrefixLaw_zero (R : ℝ) (z : AugmentedState) (w : ℕ → Action) :
    argWordPrefixLaw R z 0 w = Measure.dirac (fun _ => z) := by
  have hw : argWordSet 0 w = Set.univ := by ext h; simp [argWordSet]
  rw [argWordPrefixLaw, hw, Measure.restrict_univ, argPrefixLaw,
    (eventProcess false R).pathLaw_eq]
  change ((Kernel.traj (X := fun _ : ℕ => AugmentedState)
    (eventProcess false R).stepSeq 0) (fun _ => z)).map (Preorder.frestrictLe 0) = _
  rw [Kernel.traj_map_frestrictLe_apply, Kernel.partialTraj_self, Kernel.id_apply]

theorem argWordPrefixLaw_lintegral_succ (R : ℝ) (hR : 0 ≤ R) (z : AugmentedState)
    (n : ℕ) (w : ℕ → Action) (f : ARGPrefix (n + 1) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ h, f h ∂argWordPrefixLaw R z (n + 1) w) =
      ∫⁻ h, ∫⁻ y, f (argPrefixJoin n (h, y))
        ∂argNaturalTransition R (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩) (w n)
        ∂argWordPrefixLaw R z n w := by
  calc
    _ = ∫⁻ p, f (argPrefixJoin n p)
        ∂(argWordPrefixLaw R z (n + 1) w).map (argPrefixSplit n) := by
      change _ = ∫⁻ p, (f ∘ argPrefixJoin n) p ∂_
      rw [lintegral_map (hf.comp (argPrefixJoin_measurable n)) (argPrefixSplit_measurable n)]
      exact (lintegral_congr fun h => congrArg f (argPrefixJoin_split n h)).symm
    _ = _ := by
      change (∫⁻ p, (f ∘ argPrefixJoin n) p ∂_) = _
      rw [argWordPrefixLaw_next_map R z n w,
        Measure.lintegral_compProd (hf.comp (argPrefixJoin_measurable n))]
      congr 1
      funext h
      rw [Kernel.restrict_apply, Rhone.MarkovChain.DiscreteProcess.stepSeq, Kernel.comap_apply]
      change (∫⁻ y, f (argPrefixJoin n (h, y)) ∂((eventKernel false R) _).restrict _) = _
      rw [eventKernel_ARG_natural_restrict R hR]
theorem argWordNextIntegral_measurable (R : ℝ) (hR : 0 ≤ R) (n : ℕ)
    (a : Action) (f : ARGPrefix (n + 1) → ℝ≥0∞) (hf : Measurable f) :
    Measurable (fun h : ARGPrefix n => ∫⁻ y, f (argPrefixJoin n (h, y))
      ∂argNaturalTransition R (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩) a) := by
  have hg := (hf.comp (argPrefixJoin_measurable n)).lintegral_kernel_prod_right'
    (κ := ((eventProcess false R).stepSeq n).restrict (argActionFiber_measurable a))
  convert hg using 1
  funext h
  rw [Kernel.restrict_apply, Rhone.MarkovChain.DiscreteProcess.stepSeq, Kernel.comap_apply]
  change _ = ∫⁻ y, f (argPrefixJoin n (h, y)) ∂((eventKernel false R) _).restrict _
  rw [eventKernel_ARG_natural_restrict R hR]
theorem argPrefixJoin_observe_measurable (n : ℕ) (h : ARGPrefix n)
    (f : ARGPrefix (n + 1) → ℝ≥0∞) (hf : Measurable f) :
    Measurable (fun y : AugmentedState => f (argPrefixJoin n (h, y))) := by
  simpa only [Function.comp_def, id_eq] using
    (hf.comp (argPrefixJoin_measurable n)).comp
      ((measurable_const (a := h)).prodMk measurable_id)
end Rhone.Coalescent.SmcSupport
