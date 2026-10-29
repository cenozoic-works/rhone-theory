/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Combinatorics.KingmanHistories
/-! # Ranked and unranked Kingman shapes as label-permutation quotients of histories -/
@[expose] public section
namespace Rhone.Combinatorics
open Finset
universe u
def forestRelabel {L : Type u} [DecidableEq L] (e : L ≃ L)
    (F : Finset (Finset L)) : Finset (Finset L) :=
  F.image (fun C => C.map e.toEmbedding)
def historyAt {L : Type u} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) : (t : ℕ) → RankedForestHistory F t → ℕ → Finset (Finset L)
  | 0, _, _ => F
  | _t + 1, _, 0 => F
  | t + 1, h, k + 1 => historyAt h.1.1 t h.2 k
def RankedShapeRel (n : ℕ) (h h' : RankedLabelledHistory n) : Prop :=
  ∃ e : Equiv.Perm (Fin n), ∀ k ≤ n - 1,
    forestRelabel e (historyAt (ADR11.singletonForest n) (n - 1) h k) =
      historyAt (ADR11.singletonForest n) (n - 1) h' k
def UnrankedShapeRel (n : ℕ) (h h' : RankedLabelledHistory n) : Prop :=
  ∃ e : Equiv.Perm (Fin n),
    forestRelabel e (historyEnd (ADR11.singletonForest n) (n - 1) h) =
      historyEnd (ADR11.singletonForest n) (n - 1) h'
private theorem forestRelabel_refl {L : Type*} [DecidableEq L]
    (F : Finset (Finset L)) : forestRelabel (Equiv.refl L) F = F := by
  simp [forestRelabel]
private theorem forestRelabel_trans {L : Type*} [DecidableEq L]
    (e f : L ≃ L) (F : Finset (Finset L)) :
    forestRelabel f (forestRelabel e F) = forestRelabel (e.trans f) F := by
  simp only [forestRelabel, image_image]
  congr 1
  funext C
  simp only [Function.comp_apply, map_map]
  rfl

theorem rankedShapeRel_equivalence (n : ℕ) : Equivalence (RankedShapeRel n) := by
  constructor
  · intro h
    exact ⟨Equiv.refl _, fun k hk => forestRelabel_refl _⟩
  · intro h h' hh
    obtain ⟨e, he⟩ := hh
    refine ⟨e.symm, fun k hk => ?_⟩
    rw [← he k hk, forestRelabel_trans]
    simpa using forestRelabel_refl
      (historyAt (ADR11.singletonForest n) (n - 1) h k)
  · intro h h' h'' hh hh'
    obtain ⟨e, he⟩ := hh
    obtain ⟨f, hf⟩ := hh'
    refine ⟨e.trans f, fun k hk => ?_⟩
    rw [← forestRelabel_trans, he k hk, hf k hk]

theorem unrankedShapeRel_equivalence (n : ℕ) : Equivalence (UnrankedShapeRel n) := by
  constructor
  · intro h
    exact ⟨Equiv.refl _, forestRelabel_refl _⟩
  · intro h h' hh
    obtain ⟨e, he⟩ := hh
    refine ⟨e.symm, ?_⟩
    rw [← he, forestRelabel_trans]
    simpa using forestRelabel_refl (historyEnd (ADR11.singletonForest n) (n - 1) h)
  · intro h h' h'' hh hh'
    obtain ⟨e, he⟩ := hh
    obtain ⟨f, hf⟩ := hh'
    refine ⟨e.trans f, ?_⟩
    rw [← forestRelabel_trans, he, hf]
def rankedShapeSetoid (n : ℕ) : Setoid (RankedLabelledHistory n) :=
  ⟨RankedShapeRel n, rankedShapeRel_equivalence n⟩
def unrankedShapeSetoid (n : ℕ) : Setoid (RankedLabelledHistory n) :=
  ⟨UnrankedShapeRel n, unrankedShapeRel_equivalence n⟩
def RankedShape (n : ℕ) := Quotient (rankedShapeSetoid n)
def UnrankedShape (n : ℕ) := Quotient (unrankedShapeSetoid n)
noncomputable instance (n : ℕ) : Fintype (RankedShape n) := by
  unfold RankedShape
  exact Fintype.ofFinite _
noncomputable instance (n : ℕ) : Fintype (UnrankedShape n) := by
  unfold UnrankedShape
  exact Fintype.ofFinite _
end Rhone.Combinatorics
