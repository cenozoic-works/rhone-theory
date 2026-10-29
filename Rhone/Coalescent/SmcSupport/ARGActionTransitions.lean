/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcSupport.ARGCoordinateDensity

/-! # Index-coded actions of the ARG recursion: valid and invalid transitions -/

@[expose] public section

namespace Rhone.Coalescent.SmcSupport
open IntervalProcess MeasureTheory

theorem argActionNatural_inj (s : State) : Function.Injective (argActionNatural (s := s)) := by
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
    | inr j =>
      simp only [argActionNatural, Sum.inr.injEq] at h
      exact congrArg Sum.inr (Fin.ext h)

theorem argNaturalTransition_selected (R : ℝ) (z : AugmentedState)
    (hm : 1 < z.1.2.2.1) (a : ActionIndex z.1) :
    argNaturalTransition R z (argActionNatural a) = argActionTransition R z a := by
  classical
  rw [argNaturalTransition, ite_eq_left hm]
  calc
    _ = (if argActionNatural a = argActionNatural a then argActionTransition R z a else 0) := by
      apply Finset.sum_eq_single a
      · intro b _ hba
        have hn : argActionNatural b ≠ argActionNatural a :=
          fun h => hba (argActionNatural_inj z.1 h)
        simp [hn]
      · intro hn
        exact False.elim (hn (Finset.mem_univ a))
    _ = _ := by simp

theorem argNaturalTransition_pair_valid (R : ℝ) (z : AugmentedState)
    (hm : 1 < z.1.2.2.1) (i j : Fin z.1.2.2.1) (hij : i.val < j.val) :
    argNaturalTransition R z (.inl (i.val, j.val)) =
      argPairTransition R z i j := by
  have h := argNaturalTransition_selected R z hm (.inl (i, j))
  simpa only [argActionNatural, argActionTransition, ite_eq_left hij] using h

theorem argNaturalTransition_split_valid (R : ℝ) (z : AugmentedState)
    (hm : 1 < z.1.2.2.1) (i : Fin z.1.2.2.1) :
    argNaturalTransition R z (.inr i.val) = argSplitTransition R z i := by
  exact argNaturalTransition_selected R z hm (.inr i)

theorem argNaturalTransition_pair_invalid (R : ℝ) (z : AugmentedState)
    (ij : ℕ × ℕ) (hinvalid : ¬ (1 < z.1.2.2.1 ∧ ij.1 < ij.2 ∧ ij.2 < z.1.2.2.1)) :
    argNaturalTransition R z (.inl ij) = 0 := by
  classical
  unfold argNaturalTransition
  split_ifs with hm
  · apply Finset.sum_eq_zero
    intro b _
    cases b with
    | inr i => simp [argActionNatural]
    | inl kl =>
      by_cases h : argActionNatural (.inl kl) = (.inl ij : Action)
      · have hv : kl.1.val = ij.1 ∧ kl.2.val = ij.2 := by
          have hp : (kl.1.val, kl.2.val) = ij := Sum.inl.inj h
          exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩
        have horder : ¬ kl.1.val < kl.2.val := by
          intro ho
          exact hinvalid ⟨hm, hv.1 ▸ hv.2 ▸ ho, hv.2 ▸ kl.2.isLt⟩
        simp [h, argActionTransition, horder]
      · simp [h]
  · rfl

theorem argNaturalTransition_split_invalid (R : ℝ) (z : AugmentedState)
    (i : ℕ) (hinvalid : ¬ (1 < z.1.2.2.1 ∧ i < z.1.2.2.1)) :
    argNaturalTransition R z (.inr i) = 0 := by
  classical
  unfold argNaturalTransition
  split_ifs with hm
  · apply Finset.sum_eq_zero
    intro b _
    cases b with
    | inl ij => simp [argActionNatural]
    | inr j =>
      have hn : j.val ≠ i := fun h => hinvalid ⟨hm, h ▸ j.isLt⟩
      simp [argActionNatural, hn]
  · rfl
end Rhone.Coalescent.SmcSupport
