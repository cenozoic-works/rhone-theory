/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Combinatorics.KingmanShapeEndpoint
public import Rhone.Combinatorics.KingmanShapes
/-! # Unranked history shapes are exactly relabelling classes of binary endpoints -/
@[expose] public section
namespace Rhone.Combinatorics
abbrev BinaryHierarchy (n : ℕ) :=
  {G : Finset (Finset (Fin n)) // ADR11.IsBinaryHierarchy G}
def BinaryHierarchyShapeRel (n : ℕ) (G H : BinaryHierarchy n) : Prop :=
  ∃ e : Equiv.Perm (Fin n), forestRelabel e G.1 = H.1
theorem binaryHierarchyShapeRel_equivalence (n : ℕ) :
    Equivalence (BinaryHierarchyShapeRel n) := by
  have hrefl (F : Finset (Finset (Fin n))) : forestRelabel (Equiv.refl _) F = F := by
    simp [forestRelabel]
  have htrans (e f : Equiv.Perm (Fin n)) (F : Finset (Finset (Fin n))) :
      forestRelabel f (forestRelabel e F) = forestRelabel (e.trans f) F := by
    simp only [forestRelabel, Finset.image_image]
    congr 1
    funext C
    simp only [Function.comp_apply, Finset.map_map]
    rfl
  constructor
  · intro G
    exact ⟨Equiv.refl _, hrefl G.1⟩
  · intro G H hGH
    obtain ⟨e, he⟩ := hGH
    refine ⟨e.symm, ?_⟩
    rw [← he, htrans]
    simpa using hrefl G.1
  · intro G H K hGH hHK
    obtain ⟨e, he⟩ := hGH
    obtain ⟨f, hf⟩ := hHK
    refine ⟨e.trans f, ?_⟩
    rw [← htrans, he, hf]
def binaryHierarchyShapeSetoid (n : ℕ) : Setoid (BinaryHierarchy n) :=
  ⟨BinaryHierarchyShapeRel n, binaryHierarchyShapeRel_equivalence n⟩
def BinaryHierarchyShape (n : ℕ) := Quotient (binaryHierarchyShapeSetoid n)
noncomputable instance (n : ℕ) : Fintype (BinaryHierarchyShape n) := by
  unfold BinaryHierarchyShape
  exact Fintype.ofFinite _
def unrankedShapeEndpoint (n : ℕ) (hn : 1 ≤ n) :
    UnrankedShape n → BinaryHierarchyShape n :=
  Quotient.map (fun h => ⟨historyEnd (ADR11.singletonForest n) (n - 1) h,
    historyEnd_isBinaryHierarchy n hn h⟩) (fun _ _ hrel => hrel)
theorem unrankedShapeEndpoint_injective (n : ℕ) (hn : 1 ≤ n) :
    Function.Injective (unrankedShapeEndpoint n hn) := by
  intro a b
  induction a using Quotient.inductionOn with
  | h a =>
    induction b using Quotient.inductionOn with
    | h b =>
      intro he
      apply Quotient.sound
      change Quotient.mk (binaryHierarchyShapeSetoid n)
        ⟨historyEnd (ADR11.singletonForest n) (n - 1) a, _⟩ =
        Quotient.mk (binaryHierarchyShapeSetoid n)
          ⟨historyEnd (ADR11.singletonForest n) (n - 1) b, _⟩ at he
      have hrel := Quotient.exact he
      exact hrel
theorem unrankedShapeEndpoint_surjective (n : ℕ) (hn : 1 ≤ n) :
    Function.Surjective (unrankedShapeEndpoint n hn) := by
  intro q
  induction q using Quotient.inductionOn with
  | h G =>
    obtain ⟨h, hh⟩ := historyEnd_surjective_binary n hn G.1 G.2
    refine ⟨Quotient.mk _ h, ?_⟩
    change Quotient.mk _ ⟨historyEnd (ADR11.singletonForest n) (n - 1) h, _⟩ =
      Quotient.mk _ G
    exact congrArg (Quotient.mk _) (Subtype.ext hh)
noncomputable def unrankedShapeEndpointEquiv (n : ℕ) (hn : 1 ≤ n) :
    UnrankedShape n ≃ BinaryHierarchyShape n :=
  Equiv.ofBijective (unrankedShapeEndpoint n hn)
    ⟨unrankedShapeEndpoint_injective n hn, unrankedShapeEndpoint_surjective n hn⟩
theorem card_unrankedShape_endpoint (n : ℕ) (hn : 1 ≤ n) :
    Fintype.card (UnrankedShape n) = Fintype.card (BinaryHierarchyShape n) :=
  Fintype.card_congr (unrankedShapeEndpointEquiv n hn)
end Rhone.Combinatorics
