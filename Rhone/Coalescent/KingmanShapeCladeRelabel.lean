/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanShapeRootLabels
public import Rhone.Coalescent.KingmanShapeForestEmbedLaws
/-!
# Restrict a global leaf relabelling to the labels of its mapped clade

Source: andre1881, §II no. 6, pp. 170–171. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
noncomputable def cladeRelabelEquiv (n : ℕ) (e : Equiv.Perm (Fin n))
    (A B : Finset (Fin n)) (hAB : A.map e.toEmbedding = B) :
    Fin A.card ≃ Fin B.card := by
  let f : A ≃ B := Equiv.subtypeEquiv e (fun x => by
    constructor
    · intro hx
      rw [← hAB]
      exact mem_map.mpr ⟨x, hx, rfl⟩
    · intro hx
      rw [← hAB] at hx
      obtain ⟨y, hy, he⟩ := mem_map.mp hx
      have hyx : y = x := e.injective he
      exact hyx ▸ hy)
  exact A.equivFin.symm.trans (f.trans B.equivFin)
theorem cladeRelabelEquiv_embedding (n : ℕ) (e : Equiv.Perm (Fin n))
    (A B : Finset (Fin n)) (hAB : A.map e.toEmbedding = B) (x : Fin A.card) :
    cladeLabelEmbedding B (cladeRelabelEquiv n e A B hAB x) =
      e (cladeLabelEmbedding A x) := by
  unfold cladeRelabelEquiv
  change (B.equivFin.symm (B.equivFin _)).val = _
  rw [Equiv.symm_apply_apply]
  rfl
theorem cladeRelabel_card (n : ℕ) (e : Equiv.Perm (Fin n))
    (A B : Finset (Fin n)) (hAB : A.map e.toEmbedding = B) : A.card = B.card := by
  simpa only [card_map] using congrArg Finset.card hAB
end Rhone.Coalescent
