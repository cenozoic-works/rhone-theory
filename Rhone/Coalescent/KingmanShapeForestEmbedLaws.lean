/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanForestEmbedding
/-! # Forest embeddings preserve composition, union, and bijective label recovery -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
theorem forestEmbed_comp {L M N : Type*} [DecidableEq L] [DecidableEq M] [DecidableEq N]
    (e : L ↪ M) (f : M ↪ N) (F : Finset (Finset L)) :
    forestEmbed f (forestEmbed e F) = forestEmbed (e.trans f) F := by
  simp only [forestEmbed, image_image]
  congr 1
  funext C
  exact map_map e f C
theorem forestEmbed_refl {L : Type*} [DecidableEq L] (F : Finset (Finset L)) :
    forestEmbed (Function.Embedding.refl L) F = F := by
  simp [forestEmbed]
theorem forestEmbed_union {L M : Type*} [DecidableEq L] [DecidableEq M]
    (e : L ↪ M) (F G : Finset (Finset L)) :
    forestEmbed e (F ∪ G) = forestEmbed e F ∪ forestEmbed e G := by
  simp only [forestEmbed, image_union]
theorem forestEmbed_equiv_symm {L M : Type*} [DecidableEq L] [DecidableEq M]
    (e : L ≃ M) (F : Finset (Finset L)) :
    forestEmbed e.symm.toEmbedding (forestEmbed e.toEmbedding F) = F := by
  rw [forestEmbed_comp]
  have he : e.toEmbedding.trans e.symm.toEmbedding = Function.Embedding.refl L :=
    Function.Embedding.ext (fun x => e.symm_apply_apply x)
  rw [he, forestEmbed_refl]
theorem clade_map_equiv_univ {L M : Type*} [Fintype L] [Fintype M]
    (e : L ≃ M) :
    (univ : Finset L).map e.toEmbedding = (univ : Finset M) :=
  Finset.map_univ_equiv e
theorem forestEmbed_erase {L M : Type*} [DecidableEq L] [DecidableEq M]
    (e : L ↪ M) (F : Finset (Finset L)) (C : Finset L) :
    forestEmbed e (F.erase C) = (forestEmbed e F).erase (C.map e) :=
  image_erase (map_injective e) F C
end Rhone.Coalescent
