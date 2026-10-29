/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Combinatorics.KingmanShapes
/-! # Ranked forest histories retain exactly their full valid merger traces -/
@[expose] public section
namespace Rhone.Combinatorics
def ForestMergerTrace {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (t : ℕ) :=
  {p : Fin (t + 1) → Finset (Finset L) // p 0 = F ∧
    ∀ k : Fin t, p k.succ ∈ ADR11.merges (p k.castSucc)}
theorem historyAt_zero {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (t : ℕ) (h : RankedForestHistory F t) :
    historyAt F t h 0 = F := by
  cases t <;> rfl
theorem historyAt_next_merge {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (t : ℕ) (h : RankedForestHistory F t)
    (k : ℕ) (hk : k < t) :
    historyAt F t h (k + 1) ∈ ADR11.merges (historyAt F t h k) := by
  induction t generalizing F k with
  | zero => omega
  | succ t ih =>
    obtain ⟨G, h⟩ := h
    cases k with
    | zero =>
      simpa only [historyAt, historyAt_zero] using G.2
    | succ k =>
      exact ih G.1 h k (by omega)
theorem historyAt_history_ext {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (t : ℕ) (h h' : RankedForestHistory F t)
    (he : ∀ k ≤ t, historyAt F t h k = historyAt F t h' k) : h = h' := by
  induction t generalizing F with
  | zero => exact @Subsingleton.elim PUnit _ h h'
  | succ t ih =>
    obtain ⟨G, h⟩ := h
    obtain ⟨H, h'⟩ := h'
    have hval : G.1 = H.1 := by
      simpa only [historyAt, historyAt_zero] using he 1 (by omega)
    have hGH : G = H := Subtype.ext hval
    subst H
    apply congrArg (fun tail => (⟨G, tail⟩ : RankedForestHistory F (t + 1)))
    apply ih G.1 h h'
    intro k hk
    exact he (k + 1) (by omega)
def rankedForestHistoryTrace {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (t : ℕ) (h : RankedForestHistory F t) :
    ForestMergerTrace F t :=
  ⟨fun k => historyAt F t h k.val,
    historyAt_zero F t h, fun k => historyAt_next_merge F t h k.val k.isLt⟩
theorem rankedForestHistoryTrace_injective {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (t : ℕ) : Function.Injective (rankedForestHistoryTrace F t) := by
  intro h h' he
  apply historyAt_history_ext F t h h'
  intro k hk
  exact congrFun (congrArg Subtype.val he) ⟨k, by omega⟩
theorem rankedForestHistoryTrace_surjective {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (t : ℕ) : Function.Surjective (rankedForestHistoryTrace F t) := by
  intro p
  induction t generalizing F with
  | zero =>
    refine ⟨PUnit.unit, Subtype.ext ?_⟩
    funext k
    have hk : k = 0 := Fin.ext (by have := k.isLt; omega)
    subst k
    exact p.2.1.symm
  | succ t ih =>
    let G := p.1 ⟨1, by omega⟩
    have hGF : G ∈ ADR11.merges F := by
      have hm := p.2.2 ⟨0, by omega⟩
      change p.1 ⟨1, _⟩ ∈ ADR11.merges (p.1 0) at hm
      rw [p.2.1] at hm
      exact hm
    let tail : ForestMergerTrace G t :=
      ⟨fun k => p.1 ⟨k.val + 1, by have := k.isLt; omega⟩,
        rfl, fun k => p.2.2 ⟨k.val + 1, by have := k.isLt; omega⟩⟩
    obtain ⟨h, hh⟩ := ih G tail
    refine ⟨⟨⟨G, hGF⟩, h⟩, Subtype.ext ?_⟩
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · exact p.2.1.symm
    · exact congrFun (congrArg Subtype.val hh) j
noncomputable def rankedForestHistoryTraceEquiv {L : Type*}
    [Fintype L] [DecidableEq L] (F : Finset (Finset L)) (t : ℕ) :
    RankedForestHistory F t ≃ ForestMergerTrace F t :=
  Equiv.ofBijective (rankedForestHistoryTrace F t)
    ⟨rankedForestHistoryTrace_injective F t, rankedForestHistoryTrace_surjective F t⟩
end Rhone.Combinatorics
