/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanUnrankedShapeRootTargetBridge
public import Rhone.Coalescent.KingmanUnrankedShapeRootSizes
public import Rhone.Coalescent.KingmanUnrankedShapeRootJoin
/-!
# Equivalence of unranked shapes with their root decomposition

Source: wedderburn1922, §1, p. 122. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
open scoped Sym2
/-- Source: wedderburn1922, §1, p. 122. -/
private theorem binaryHierarchyShapeRootPair_realizes_classes (n m l : ℕ)
    (hn : 2 ≤ n) (hm : 1 ≤ m) (hl : 1 ≤ l) (hml : m + l = n)
    (G : Combinatorics.BinaryHierarchyShape m) (H : Combinatorics.BinaryHierarchyShape l) :
    ∃ q : Combinatorics.BinaryHierarchyShape n, binaryHierarchyShapeRootPair n hn q =
      s((⟨m,G⟩ : Σ k, Combinatorics.BinaryHierarchyShape k),(⟨l,H⟩ : Σ k,
          Combinatorics.BinaryHierarchyShape k)) := by
  obtain ⟨F,hF⟩ := binaryHierarchyShapeRootPair_surjective_pair n m l hn hm hl hml
    G.out H.out
  refine ⟨Quotient.mk (Combinatorics.binaryHierarchyShapeSetoid n) F, ?_⟩
  rw [show Quotient.mk (Combinatorics.binaryHierarchyShapeSetoid m) G.out = G from Quotient.out_eq
      G,
    show Quotient.mk (Combinatorics.binaryHierarchyShapeSetoid l) H.out = H from Quotient.out_eq H]
        at hF
  exact hF
/-- Source: wedderburn1922, §1, p. 122. -/
theorem binaryHierarchyRootTargetPair_realized (n : ℕ) (hn : 2 ≤ n)
    (t : BinaryHierarchyRootTarget n) :
    ∃ q : Combinatorics.BinaryHierarchyShape n,
      binaryHierarchyShapeRootPair n hn q = binaryHierarchyRootTargetPair n t := by
  classical
  rcases t with ⟨k,G,H⟩ | t
  · have hk := mem_Ico.mp k.property
    exact binaryHierarchyShapeRootPair_realizes_classes n k.val (n - k.val) hn hk.1
      (by omega) (by omega) G H
  · by_cases he : Even n
    · obtain ⟨⟨G,H⟩,hp⟩ := Sym2.mk_surjective (cast (by rw [ite_eq_left he]) t)
      obtain ⟨q,hq⟩ := binaryHierarchyShapeRootPair_realizes_classes n (n / 2) (n / 2) hn
        (by omega) (by omega) (by obtain ⟨v,hv⟩ := he; omega) G H
      refine ⟨q, ?_⟩
      simp only [binaryHierarchyRootTargetPair, he, ↓reduceDIte, Sum.elim_inr]
      rw [← hp]
      exact hq
    · exact (cast (by rw [ite_eq_right he]) t : Empty).elim
/-- Source: wedderburn1922, §1, p. 122. -/
noncomputable def binaryHierarchyShapeRootTargetEquiv (n : ℕ) (hn : 2 ≤ n) :
    Combinatorics.BinaryHierarchyShape n ≃ BinaryHierarchyRootTarget n := by
  classical
  have hex (q : Combinatorics.BinaryHierarchyShape n) : ∃ t : BinaryHierarchyRootTarget n,
      binaryHierarchyRootTargetPair n t = binaryHierarchyShapeRootPair n hn q := by
    obtain ⟨m,l,hm,hl,hml,G,H,hq⟩ := binaryHierarchyShapeRootPair_sizes n hn q
    obtain ⟨t,ht⟩ := binaryHierarchyRootTargetPair_surjective_sizes n m l hn hm hl hml G H
    exact ⟨t,ht.trans hq.symm⟩
  let f (q : Combinatorics.BinaryHierarchyShape n) := (hex q).choose
  have hf (q : Combinatorics.BinaryHierarchyShape n) :
      binaryHierarchyRootTargetPair n (f q) = binaryHierarchyShapeRootPair n hn q :=
    (hex q).choose_spec
  apply Equiv.ofBijective f
  constructor
  · intro q r hqr
    apply binaryHierarchyShapeRootPair_injective n hn
    rw [← hf q, ← hf r, hqr]
  · intro t
    obtain ⟨q,hq⟩ := binaryHierarchyRootTargetPair_realized n hn t
    refine ⟨q, binaryHierarchyRootTargetPair_injective n hn ?_⟩
    exact (hf q).trans hq
/-- Source: wedderburn1922, §1, p. 122. -/
noncomputable def unrankedShapeRootEquiv (n : ℕ) (hn : 2 ≤ n) :
    Combinatorics.UnrankedShape n ≃
      (Σ k : {k : ℕ // k ∈ Finset.Ico 1 ((n - 1) / 2+1)},
        Combinatorics.UnrankedShape k.val × Combinatorics.UnrankedShape (n - k.val)) ⊕
        (if Even n then Sym2 (Combinatorics.UnrankedShape (n / 2)) else Empty) :=
  ((Combinatorics.unrankedShapeEndpointEquiv n (by omega)).trans
    (binaryHierarchyShapeRootTargetEquiv n hn)).trans
      (unrankedShapeRootTargetEndpointEquiv n hn).symm
end Rhone.Coalescent
