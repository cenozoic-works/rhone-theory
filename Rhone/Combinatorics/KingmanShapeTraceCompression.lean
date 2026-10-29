/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Combinatorics.KingmanShapeSlotCounter
public import Rhone.Combinatorics.KingmanShapeHistoryTrace
/-!
# Compress a forest trace with stalling steps into a ranked merger history

Source: andre1881, §II no. 6, pp. 170–171. -/
@[expose] public section
namespace Rhone.Combinatorics
open Finset
theorem forestTrace_compress {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (t : ℕ) (s : Finset (Fin t))
    (p : ℕ → Finset (Finset L)) (hzero : p 0 = F)
    (hstep : ∀ k : Fin t, if k ∈ s then p (k.val+1) ∈ ADR11.merges (p k.val)
      else p (k.val+1) = p k.val) :
    ∃ h : RankedForestHistory F s.card, ∀ k ≤ t,
      historyAt F s.card h ((s.filter (fun i => i.val < k)).card) = p k := by
  classical
  let c := fun k => (s.filter (fun i => i.val < k)).card
  let r := fun j : Fin (s.card+1) =>
    Classical.choose (finite_slot_count_range s j.val (by have := j.isLt; omega))
  have hr (j : Fin (s.card+1)) : r j ≤ t ∧ c (r j) = j.val :=
    Classical.choose_spec (finite_slot_count_range s j.val (by have := j.isLt; omega))
  have hstable : ∀ k : Fin t, k ∉ s → p (k.val+1) = p k.val := by
    intro k hk
    have hs := hstep k
    rwa [ite_eq_right hk] at hs
  let q : Fin (s.card+1) → Finset (Finset L) := fun j => p (r j)
  have hq0 : q 0 = F := by
    apply (finite_slot_snapshot_eq s p hstable (r 0) 0 (hr 0).1 (by omega) ?_).trans hzero
    exact (hr 0).2.trans (by simp)
  have hqstep (j : Fin s.card) : q j.succ ∈ ADR11.merges (q j.castSucc) := by
    obtain ⟨k, hk, hk1⟩ := finite_slot_count_transition s j.val j.isLt
    have hm : k ∈ s := by
      by_contra hn
      have hc := finite_slot_count_succ s k
      rw [ite_eq_right hn] at hc
      omega
    have hs := hstep k
    rw [ite_eq_left hm] at hs
    have he0 : q j.castSucc = p k.val :=
      finite_slot_snapshot_eq s p hstable _ _ (hr _).1 (by omega) ((hr _).2.trans hk.symm)
    have he1 : q j.succ = p (k.val+1) :=
      finite_slot_snapshot_eq s p hstable _ _ (hr _).1 k.isLt ((hr _).2.trans hk1.symm)
    rwa [he0, he1]
  let trace : ForestMergerTrace F s.card := ⟨q, hq0, hqstep⟩
  let h := (rankedForestHistoryTraceEquiv F s.card).symm trace
  refine ⟨h, ?_⟩
  intro k hk
  have hck : c k ≤ s.card := card_filter_le _ _
  have he := (rankedForestHistoryTraceEquiv F s.card).apply_symm_apply trace
  have heval := congrFun (congrArg Subtype.val he) ⟨c k, by omega⟩
  change historyAt F s.card h (c k) = q ⟨c k, _⟩ at heval
  exact heval.trans (finite_slot_snapshot_eq s p hstable _ k (hr _).1 hk (hr _).2)
end Rhone.Combinatorics
