/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanUnrankedShapeRootPair
public import Rhone.Coalescent.KingmanUnrankedShapeRootMatch
/-!
# Unordered daughter endpoint classes distinguish unranked shapes

Source: wedderburn1922, §1, p. 122. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
open scoped Sym2
/-- Source: wedderburn1922, §1, p. 122. -/
theorem binaryHierarchyShape_sigma_map_of_eq (m n : ℕ)
    (G : Combinatorics.BinaryHierarchy m) (H : Combinatorics.BinaryHierarchy n)
    (h : (⟨m, Quotient.mk (Combinatorics.binaryHierarchyShapeSetoid m) G⟩ : Σ k,
        Combinatorics.BinaryHierarchyShape k) =
      ⟨n, Quotient.mk (Combinatorics.binaryHierarchyShapeSetoid n) H⟩) :
    ∃ e : Fin m ≃ Fin n, forestEmbed e.toEmbedding G.1 = H.1 := by
  have hmn := congrArg Sigma.fst h
  dsimp only at hmn
  subst n
  have hq := (Sigma.mk.inj h).2
  exact Quotient.exact (eq_of_heq hq)
/-- Source: wedderburn1922, §1. -/
theorem binaryHierarchy_rel_of_rootPair_eq (n : ℕ) (G H : Combinatorics.BinaryHierarchy n)
    (A B : Finset (Fin n))
    (hs : ADR11.roots (G.1.erase univ) = {A, univ \ A})
    (ht : ADR11.roots (H.1.erase univ) = {B, univ \ B})
    (he : binaryHierarchyRootDaughterPair n G A hs =
      binaryHierarchyRootDaughterPair n H B ht) :
    Combinatorics.BinaryHierarchyShapeRel n G H := by
  unfold binaryHierarchyRootDaughterPair at he
  rcases Sym2.eq_iff.mp he with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · obtain ⟨f, hf⟩ := binaryHierarchyShape_sigma_map_of_eq _ _ _ _ ha
    obtain ⟨g, hg⟩ := binaryHierarchyShape_sigma_map_of_eq _ _ _ _ hb
    exact binaryHierarchy_rel_of_daughter_maps n G H A B hs ht f g hf hg
  · have hcc : univ \ (univ \ B) = B := by ext x; simp
    have ht' : ADR11.roots (H.1.erase univ) = {univ \ B, univ \ (univ \ B)} := by
      rw [hcc, pair_comm]
      exact ht
    have hb' : binaryHierarchyDaughterShape n G (univ \ A)
        (mem_of_mem_erase (ADR11.roots_subset _
          (hs ▸ mem_insert_of_mem (mem_singleton_self _)))) =
        binaryHierarchyDaughterShape n H (univ \ (univ \ B))
          (mem_of_mem_erase (ADR11.roots_subset _
            (ht' ▸ mem_insert_of_mem (mem_singleton_self _)))) := by
      simpa only [hcc] using hb
    obtain ⟨f, hf⟩ := binaryHierarchyShape_sigma_map_of_eq _ _ _ _ ha
    obtain ⟨g, hg⟩ := binaryHierarchyShape_sigma_map_of_eq _ _ _ _ hb'
    exact binaryHierarchy_rel_of_daughter_maps n G H A (univ \ B) hs ht' f g hf hg
/-- Source: wedderburn1922, §1. -/
theorem binaryHierarchyShapeRootPair_injective (n : ℕ) (hn : 2 ≤ n) :
    Function.Injective (binaryHierarchyShapeRootPair n hn) := by
  intro q r
  induction q using Quotient.inductionOn with
  | h G =>
    induction r using Quotient.inductionOn with
    | h H =>
      intro he
      obtain ⟨A, _, _, hs⟩ := binary_hierarchy_root_pair G.1 G.2
        (by simpa using hn : 2 ≤ Fintype.card (Fin n))
      obtain ⟨B, _, _, ht⟩ := binary_hierarchy_root_pair H.1 H.2
        (by simpa using hn : 2 ≤ Fintype.card (Fin n))
      rw [binaryHierarchyShapeRootPair_mk n hn G A hs,
        binaryHierarchyShapeRootPair_mk n hn H B ht] at he
      exact Quotient.sound (binaryHierarchy_rel_of_rootPair_eq n G H A B hs ht he)
/-- Source: wedderburn1922, §1, p. 122. -/
theorem unrankedShapeRootPair_injective (n : ℕ) (hn : 2 ≤ n) :
    Function.Injective (unrankedShapeRootPair n hn) :=
  (binaryHierarchyShapeRootPair_injective n hn).comp
    (Combinatorics.unrankedShapeEndpoint_injective n (by omega))
end Rhone.Coalescent
