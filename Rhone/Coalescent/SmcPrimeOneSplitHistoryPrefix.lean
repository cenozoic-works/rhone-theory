/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitGlobalInventory

/-! # Bookkeeping of the old history prefix under extracted pair successors -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess

structure ExtractedHistoryPrefix (N : ℕ) (z : OneSplitExtractionState N) : Prop where
  bound : z.mergers < N
  current : z.oldHistory ⟨z.mergers, bound⟩ = z.old
  initial : ∀ hN : 0 < N, z.oldHistory ⟨0, hN⟩ = (initialState N, (0, .inl ()))
  records : ∀ k : Fin N, k.val ≤ z.mergers →
    Valid (z.oldHistory k).1 ∧ (z.oldHistory k).1.2.2.1 = N - k.val
  transitions : ∀ k : Fin (N - 1), k.val < z.mergers →
    KingmanTransition (z.oldHistory ⟨k.val, by omega⟩,
      z.oldHistory ⟨k.val + 1, by omega⟩)

theorem extractionInitial_history_prefix (N : ℕ) (hN : 0 < N) :
    ExtractedHistoryPrefix N (extractionInitial N) := by
  refine ⟨hN, rfl, fun _ => rfl, ?_, ?_⟩
  · intro k hk
    have he : k.val = 0 := by change k.val ≤ 0 at hk; omega
    refine ⟨SmcSupport.initialState_valid N, ?_⟩
    simp only [extractionInitial, he, Nat.sub_zero]
    rfl
  · intro k hk
    change k.val < 0 at hk
    omega

theorem ExtractedHistoryPrefix.advance {N : ℕ} {z : OneSplitExtractionState N}
    (h : ExtractedHistoryPrefix N z) (y : AugmentedState) (hb : z.mergers + 1 < N)
    (hy : Valid y.1) (hc : y.1.2.2.1 + 1 = z.old.1.2.2.1)
    (ht : KingmanTransition (z.old, y)) :
    ExtractedHistoryPrefix N
      {z with old := y
              oldHistory := Function.update z.oldHistory ⟨z.mergers + 1, hb⟩ y
              mergers := z.mergers + 1} := by
  classical
  have hcurcount := (h.records ⟨z.mergers, h.bound⟩ le_rfl).2
  rw [h.current] at hcurcount
  change z.old.1.2.2.1 = N - z.mergers at hcurcount
  refine ⟨hb, ?_, ?_, ?_, ?_⟩
  · exact Function.update_self _ _ _
  · intro hN
    dsimp only
    apply (Function.update_of_ne ?_ _ _).trans (h.initial hN)
    intro he
    have hev := congrArg Fin.val he
    change 0 = z.mergers + 1 at hev
    omega
  · intro k hk
    dsimp only at hk ⊢
    by_cases he : k.val = z.mergers + 1
    · have hek : k = ⟨z.mergers + 1, hb⟩ := Fin.ext he
      subst k
      simp only [Function.update_self]
      exact ⟨hy, by omega⟩
    · have hne : k ≠ ⟨z.mergers + 1, hb⟩ := fun hh => he (congrArg Fin.val hh)
      rw [Function.update_of_ne hne]
      exact h.records k (by change k.val ≤ z.mergers + 1 at hk; omega)
  · intro k hk
    dsimp only at hk ⊢
    change k.val < z.mergers + 1 at hk
    have hne : (⟨k.val, by omega⟩ : Fin N) ≠ ⟨z.mergers + 1, hb⟩ := by
      intro he
      have hev := congrArg Fin.val he
      change k.val = z.mergers + 1 at hev
      omega
    rw [Function.update_of_ne hne]
    by_cases he : k.val = z.mergers
    · have he' : (⟨k.val + 1, by omega⟩ : Fin N) = ⟨z.mergers + 1, hb⟩ := by
        apply Fin.ext
        change k.val + 1 = z.mergers + 1
        omega
      rw [he', Function.update_self]
      have he'' : (⟨k.val, by omega⟩ : Fin N) = ⟨z.mergers, h.bound⟩ := Fin.ext he
      rw [he'', h.current]
      exact ht
    · have hne' : (⟨k.val + 1, by omega⟩ : Fin N) ≠ ⟨z.mergers + 1, hb⟩ := by
        intro hh
        have hev := congrArg Fin.val hh
        change k.val + 1 = z.mergers + 1 at hev
        omega
      rw [Function.update_of_ne hne']
      exact h.transitions k (by omega)

theorem ExtractedHistoryPrefix.congr_fields {N : ℕ} {z z' : OneSplitExtractionState N}
    (h : ExtractedHistoryPrefix N z) (ho : z'.old = z.old)
    (hh : z'.oldHistory = z.oldHistory) (hm : z'.mergers = z.mergers) :
    ExtractedHistoryPrefix N z' := by
  have hb : z'.mergers < N := by simpa only [hm] using h.bound
  refine ⟨hb, ?_, ?_, ?_, ?_⟩
  · have he : (⟨z'.mergers, hb⟩ : Fin N) = ⟨z.mergers, h.bound⟩ := Fin.ext hm
    rw [hh, ho, he]
    exact h.current
  · intro hN
    rw [hh]
    exact h.initial hN
  · intro k hk
    rw [hh]
    exact h.records k (by rwa [hm] at hk)
  · intro k hk
    rw [hh]
    exact h.transitions k (by rwa [hm] at hk)

end Rhone.Coalescent.SmcPrime
