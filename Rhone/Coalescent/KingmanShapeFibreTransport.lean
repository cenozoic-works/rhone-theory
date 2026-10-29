/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanShapeRootQuotientDescent
public import Rhone.Coalescent.KingmanShapeSlotImage
public import Rhone.Coalescent.KingmanShapeRootFibreMap
/-!
# The ranked root-fibre forward map computes on every history representative

Source: andre1881, §II no. 6, pp. 170–171. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
theorem cast_shape_eq_of_sigma_eq {m n k : ℕ} (s : Combinatorics.RankedShape m)
    (t : Combinatorics.RankedShape n)
    (hm : m = k) (hn : n = k) (he : (⟨m, s⟩ : Σ j, Combinatorics.RankedShape j) = ⟨n, t⟩) :
    Equiv.cast (congrArg Combinatorics.RankedShape hm) s = Equiv.cast
        (congrArg Combinatorics.RankedShape hn) t := by
  cases hm
  cases hn
  exact eq_of_heq (Sigma.mk.inj_iff.mp he).2
theorem cast_first_interleaving_eq_of_image_eq {a b c d x y : ℕ}
    (s : Combinatorics.FirstHistoryInterleaving a b)
        (t : Combinatorics.FirstHistoryInterleaving c d)
    (ha : a = x) (hb : b = y) (hc : c = x) (hd : d = y)
    (he : s.1.1.image Fin.val = t.1.1.image Fin.val) :
    Equiv.cast (congrArg₂ Combinatorics.FirstHistoryInterleaving ha hb) s =
      Equiv.cast (congrArg₂ Combinatorics.FirstHistoryInterleaving hc hd) t := by
  cases ha
  cases hb
  cases hc
  cases hd
  apply Subtype.ext
  apply Subtype.ext
  exact Finset.image_injective Fin.val_injective he
/-- Source: andre1881, §II no. 6, pp. 170–171. -/
noncomputable def rootHistoryFibreData (n : ℕ) (hn : 3 ≤ n)
    (k : {k : ℕ // k ∈ Ico 2 n}) (h : Combinatorics.RankedLabelledHistory n)
    (hk : (firstMergerRoot n hn h).card = k.val) :
    ((Combinatorics.RankedShape k.val × Combinatorics.RankedShape (n - k.val)) ×
      Combinatorics.FirstHistoryInterleaving (k.val - 1) (n - k.val - 1)) := by
  let A := firstMergerRoot n hn h
  let p := firstRootHistoryDecomposition n hn h
  have hB : (univ \ A).card = n - k.val := by
    have hc := rootPartition_card A
    dsimp only [A] at hc ⊢
    omega
  exact ⟨⟨Equiv.cast (congrArg Combinatorics.RankedShape hk)
      (Quotient.mk (Combinatorics.rankedShapeSetoid A.card) p.1.1),
    Equiv.cast (congrArg Combinatorics.RankedShape hB)
      (Quotient.mk (Combinatorics.rankedShapeSetoid (univ \ A).card) p.1.2)⟩,
    Equiv.cast (congrArg₂ Combinatorics.FirstHistoryInterleaving (congrArg (fun a => a - 1) hk)
      (congrArg (fun a => a - 1) hB)) p.2⟩
/-- Source: andre1881, §II no. 6, pp. 170–171. -/
theorem rootHistoryFibreData_congr (n : ℕ) (hn : 3 ≤ n)
    (k : {k : ℕ // k ∈ Ico 2 n}) (h h' : Combinatorics.RankedLabelledHistory n)
    (hk : (firstMergerRoot n hn h).card = k.val)
    (hk' : (firstMergerRoot n hn h').card = k.val)
    (he : Combinatorics.RankedShapeRel n h h') :
    rootHistoryFibreData n hn k h hk = rootHistoryFibreData n hn k h' hk' := by
  obtain ⟨e, he⟩ := he
  let A := firstMergerRoot n hn h
  let B := firstMergerRoot n hn h'
  have hAB : A.map e.toEmbedding = B := firstMergerRoot_map n hn h h' e he
  have hs := (binary_hierarchy_root_pair_at _
      (Combinatorics.historyEnd_isBinaryHierarchy n (by omega) h)
    (by simpa using (show 2 ≤ n by omega)) A (firstMergerRoot_spec n hn h).1).2.2
  have hs' := (binary_hierarchy_root_pair_at _
      (Combinatorics.historyEnd_isBinaryHierarchy n (by omega) h')
    (by simpa using (show 2 ≤ n by omega)) B (firstMergerRoot_spec n hn h').1).2.2
  have hcA := rootPartition_card A
  have hcB := rootPartition_card B
  dsimp only [A, B] at hcA hcB
  dsimp only [rootHistoryFibreData]
  apply Prod.ext
  · apply Prod.ext
    · apply cast_shape_eq_of_sigma_eq
      all_goals first | omega | exact
        rootHistoryDecomposition_left_shape_map n (by omega) h h' A B hs hs' e hAB he
    · apply cast_shape_eq_of_sigma_eq
      all_goals first | omega | exact
        rootHistoryDecomposition_right_shape_map n (by omega) h h' A B hs hs' e hAB he
  · apply cast_first_interleaving_eq_of_image_eq
    all_goals first | omega | exact
      rootHistoryDecomposition_slots_map n (by omega) h h' A B hs hs' e hAB he
/-- Source: andre1881, §II no. 6, pp. 170–171. -/
theorem rankedShapeRootFibreMap_representative (n : ℕ) (hn : 3 ≤ n)
    (k : {k : ℕ // k ∈ Ico 2 n})
    (s : {s : Combinatorics.RankedShape n // rankedShapeRootSize n hn s = k})
    (h : Combinatorics.RankedLabelledHistory n) (hk : (firstMergerRoot n hn h).card = k.val)
    (hrep : Quotient.mk (Combinatorics.rankedShapeSetoid n) h = s.1) :
    rankedShapeRootFibreMap n hn k s = rootHistoryFibreData n hn k h hk := by
  have hsize : rankedShapeRootSize n hn
      (Quotient.mk (Combinatorics.rankedShapeSetoid n) s.1.out) = k := by
    rw [show Quotient.mk (Combinatorics.rankedShapeSetoid n) s.1.out = s.1 from Quotient.out_eq s.1]
    exact s.2
  have hkOut : (firstMergerRoot n hn s.1.out).card = k.val := congrArg Subtype.val hsize
  change rootHistoryFibreData n hn k s.1.out hkOut = rootHistoryFibreData n hn k h hk
  apply rootHistoryFibreData_congr
  exact @Quotient.exact _ (Combinatorics.rankedShapeSetoid n) _ _
    ((Quotient.out_eq s.1).trans hrep.symm)
end Rhone.Coalescent
