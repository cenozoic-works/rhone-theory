/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeKingmanDescendants

/-! # Finite initial Kingman histories are supported on valid arrays with chronological clocks -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport MeasureTheory

def KingmanHistorySupported (N : ℕ) (h : KingmanHistory N) : Prop :=
  (∀ k : Fin N, Valid (h k).1 ∧ (h k).1.2.2.1 = N - k.val) ∧
  (∀ hN : 0 < N, h ⟨0, hN⟩ = (initialState N, (0, .inl ()))) ∧
  (∀ k : Fin (N - 1), KingmanTransition
    (h ⟨k.val, by omega⟩, h ⟨k.val + 1, by omega⟩))

theorem KingmanHistorySupported_measurable (N : ℕ) :
    MeasurableSet {h | KingmanHistorySupported N h} := by
  have hv : MeasurableSet {h : KingmanHistory N |
      ∀ k : Fin N, Valid (h k).1 ∧ (h k).1.2.2.1 = N - k.val} := by
    apply measurableSet_forall
    intro k
    exact ((validState_measurable).preimage (measurable_pi_apply k).fst).inter
      (measurableSet_eq_fun (IntervalProcess.liveCount_measurable.comp
        (measurable_pi_apply k).fst) measurable_const)
  have hi : MeasurableSet {h : KingmanHistory N |
      ∀ hN : 0 < N, h ⟨0, hN⟩ = (initialState N, (0, .inl ()))} := by
    by_cases hN : 0 < N
    · simpa only [forall_prop_of_true hN] using
        (measurableSet_eq_fun (measurable_pi_apply (⟨0, hN⟩ : Fin N))
          (measurable_const : Measurable (fun _ : KingmanHistory N =>
            ((initialState N, (0, .inl ())) : AugmentedState))))
    · simp only [forall_prop_of_false hN]
      exact MeasurableSet.univ
  have hs : MeasurableSet {h : KingmanHistory N |
      ∀ k : Fin (N - 1), KingmanTransition
        (h ⟨k.val, by omega⟩, h ⟨k.val + 1, by omega⟩)} := by
    apply measurableSet_forall
    intro k
    exact KingmanTransition_measurable.preimage
      ((measurable_pi_apply (⟨k.val, by omega⟩ : Fin N)).prodMk
        (measurable_pi_apply (⟨k.val + 1, by omega⟩ : Fin N)))
  exact hv.inter (hi.inter hs)

theorem kingmanHistoryLaw_supported (N : ℕ) :
    ∀ᵐ h ∂kingmanHistoryLaw N, KingmanHistorySupported N h := by
  unfold kingmanHistoryLaw
  apply (ae_map_iff (kingmanHistoryMap_measurable N).aemeasurable
    (KingmanHistorySupported_measurable N)).mpr
  filter_upwards [eventProcess_chronologicalAncestryPath N false 0,
    eventProcess_kingmanTransition (initialState N, (0, .inl ()))] with ω hc hs
  refine ⟨?_, ?_, ?_⟩
  · intro k
    exact ⟨hc.valid k.val, kingman_path_count N ω (congrArg Prod.fst hc.1) hs k.val k.isLt⟩
  · intro hN
    exact hc.1
  · intro k
    exact hs k.val

end Rhone.Coalescent.SmcPrime
