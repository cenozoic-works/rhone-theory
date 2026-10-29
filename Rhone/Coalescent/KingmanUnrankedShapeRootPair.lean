/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanUnrankedShapeRootDaughter
public import Mathlib.Data.Sym.Sym2
/-!
# Unordered daughter endpoint classes descend to unranked shapes

Source: wedderburn1922, §1, p. 122. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
open scoped Sym2
/-- Source: wedderburn1922, §1, p. 122. -/
noncomputable def binaryHierarchyDaughterShape (n : ℕ) (G : Combinatorics.BinaryHierarchy n)
    (A : Finset (Fin n)) (hA : A ∈ G.1) : Σ k, Combinatorics.BinaryHierarchyShape k :=
  ⟨A.card, Quotient.mk (Combinatorics.binaryHierarchyShapeSetoid A.card)
    (binaryHierarchyDaughter n G A hA)⟩
/-- Source: wedderburn1922, §1, p. 122. -/
noncomputable def binaryHierarchyRootDaughterPair (n : ℕ) (G : Combinatorics.BinaryHierarchy n)
    (A : Finset (Fin n))
    (hs : ADR11.roots (G.1.erase univ) = {A, univ \ A}) :
    Sym2 (Σ k, Combinatorics.BinaryHierarchyShape k) :=
  s(binaryHierarchyDaughterShape n G A
      (mem_of_mem_erase (ADR11.roots_subset _ (hs ▸ mem_insert_self _ _))),
    binaryHierarchyDaughterShape n G (univ \ A)
      (mem_of_mem_erase (ADR11.roots_subset _
        (hs ▸ mem_insert_of_mem (mem_singleton_self _)))))
/-- Source: wedderburn1922, §1, p. 122. -/
theorem binaryHierarchyRootDaughterPair_map (n : ℕ) (G H : Combinatorics.BinaryHierarchy n)
    (A B : Finset (Fin n))
    (hs : ADR11.roots (G.1.erase univ) = {A, univ \ A})
    (ht : ADR11.roots (H.1.erase univ) = {B, univ \ B})
    (e : Equiv.Perm (Fin n)) (he : Combinatorics.forestRelabel e G.1 = H.1) :
    binaryHierarchyRootDaughterPair n G A hs =
      binaryHierarchyRootDaughterPair n H B ht := by
  have hAr : A ∈ ADR11.roots (G.1.erase univ) := hs ▸ mem_insert_self _ _
  rcases binaryHierarchy_root_map_cases n G H A B hAr ht e he with hab | hac
  · unfold binaryHierarchyRootDaughterPair
    congr 1
    · exact binaryHierarchyDaughter_shape_map n G H A B _ _ e hab he
    · exact binaryHierarchyDaughter_shape_map n G H (univ \ A) (univ \ B) _ _ e
        (by rw [Finset.map_sdiff, clade_map_equiv_univ, hab]) he
  · unfold binaryHierarchyRootDaughterPair
    rw [Sym2.eq_swap]
    congr 1
    · exact binaryHierarchyDaughter_shape_map n G H (univ \ A) B _ _ e
        (by rw [Finset.map_sdiff, clade_map_equiv_univ, hac]; ext x; simp) he
    · exact binaryHierarchyDaughter_shape_map n G H A (univ \ B) _ _ e hac he
/-- Source: wedderburn1922, §1, p. 122. -/
noncomputable def binaryHierarchyShapeRootPair (n : ℕ) (hn : 2 ≤ n) :
    Combinatorics.BinaryHierarchyShape n → Sym2 (Σ k, Combinatorics.BinaryHierarchyShape k) := by
  classical
  let hp (G : Combinatorics.BinaryHierarchy n) := binary_hierarchy_root_pair G.1 G.2
    (by simpa using hn : 2 ≤ Fintype.card (Fin n))
  let daughter (G : Combinatorics.BinaryHierarchy n) := (hp G).choose
  let spec (G : Combinatorics.BinaryHierarchy n) := (hp G).choose_spec.2.2
  exact Quotient.lift (fun G => binaryHierarchyRootDaughterPair n G (daughter G) (spec G))
    (fun G H h => by
      obtain ⟨e, he⟩ := h
      exact binaryHierarchyRootDaughterPair_map n G H (daughter G) (daughter H)
        (spec G) (spec H) e he)
/-- Source: wedderburn1922, §1, p. 122. -/
theorem binaryHierarchyShapeRootPair_mk (n : ℕ) (hn : 2 ≤ n)
    (G : Combinatorics.BinaryHierarchy n) (A : Finset (Fin n))
    (hs : ADR11.roots (G.1.erase univ) = {A, univ \ A}) :
    binaryHierarchyShapeRootPair n hn (Quotient.mk (Combinatorics.binaryHierarchyShapeSetoid n) G) =
      binaryHierarchyRootDaughterPair n G A hs := by
  unfold binaryHierarchyShapeRootPair
  dsimp only [Quotient.lift_mk]
  apply binaryHierarchyRootDaughterPair_map n G G _ A _ hs (Equiv.refl _)
  simp [Combinatorics.forestRelabel]
/-- Source: wedderburn1922, §1, p. 122. -/
noncomputable def unrankedShapeRootPair (n : ℕ) (hn : 2 ≤ n) :
    Combinatorics.UnrankedShape n → Sym2 (Σ k, Combinatorics.BinaryHierarchyShape k) :=
  binaryHierarchyShapeRootPair n hn ∘ Combinatorics.unrankedShapeEndpoint n (by omega)
end Rhone.Coalescent
