/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanShapeCladeRelabel
/-!
# Clade preimages commute with the derived restricted leaf relabelling

Source: andre1881, §II no. 6, pp. 170–171. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
theorem cladePreimage_relabel (n : ℕ) (e : Equiv.Perm (Fin n))
    (A B : Finset (Fin n)) (hAB : A.map e.toEmbedding = B) (C : Finset (Fin n)) :
    (C.map e.toEmbedding).preimage (cladeLabelEmbedding B)
        (cladeLabelEmbedding B).injective.injOn =
      (C.preimage (cladeLabelEmbedding A) (cladeLabelEmbedding A).injective.injOn).map
        (cladeRelabelEquiv n e A B hAB).toEmbedding := by
  let f := cladeRelabelEquiv n e A B hAB
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, he⟩ := mem_map.mp (mem_preimage.mp hx)
    have hz := cladeRelabelEquiv_embedding n e A B hAB (f.symm x)
    change cladeLabelEmbedding B (f (f.symm x)) = e (cladeLabelEmbedding A (f.symm x)) at hz
    rw [Equiv.apply_symm_apply] at hz
    have hyA : y = cladeLabelEmbedding A (f.symm x) := e.injective (he.trans hz)
    exact mem_map.mpr ⟨f.symm x, mem_preimage.mpr (hyA ▸ hy), f.apply_symm_apply x⟩
  · intro hx
    obtain ⟨z, hz, rfl⟩ := mem_map.mp hx
    apply mem_preimage.mpr
    change cladeLabelEmbedding B (cladeRelabelEquiv n e A B hAB z) ∈ C.map e.toEmbedding
    rw [cladeRelabelEquiv_embedding]
    exact mem_map.mpr ⟨cladeLabelEmbedding A z, mem_preimage.mp hz, rfl⟩
theorem forestPreimage_relabel_clade (n : ℕ) (e : Equiv.Perm (Fin n))
    (A B : Finset (Fin n)) (hAB : A.map e.toEmbedding = B)
    (W : Finset (Finset (Fin n))) :
    forestPreimage (cladeLabelEmbedding B) (forestEmbed e.toEmbedding W) =
      forestEmbed (cladeRelabelEquiv n e A B hAB).toEmbedding
        (forestPreimage (cladeLabelEmbedding A) W) := by
  simp only [forestPreimage, forestEmbed, image_image]
  congr 1
  funext C
  exact cladePreimage_relabel n e A B hAB C
end Rhone.Coalescent
