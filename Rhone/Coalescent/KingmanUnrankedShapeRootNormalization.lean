/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanUnrankedShapeRootInjection
public import Mathlib.Data.Sym.Card
/-!
# The target of the unranked root decomposition and its map to unordered pairs

Source: wedderburn1922, §1, p. 122. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
open scoped Sym2
/-- Source: wedderburn1922, §1, p. 122. -/
abbrev BinaryHierarchyRootTarget (n : ℕ) :=
  (Σ k : {k : ℕ // k ∈ Finset.Ico 1 ((n - 1) / 2+1)},
    Combinatorics.BinaryHierarchyShape k.val × Combinatorics.BinaryHierarchyShape (n - k.val)) ⊕
    (if Even n then Sym2 (Combinatorics.BinaryHierarchyShape (n / 2)) else Empty)
/-- Source: wedderburn1922, §1, p. 122. -/
noncomputable def binaryHierarchyRootTargetPair (n : ℕ) :
    BinaryHierarchyRootTarget n → Sym2 (Σ k, Combinatorics.BinaryHierarchyShape k) := by
  classical
  exact Sum.elim
    (fun t => s((⟨t.1.val, t.2.1⟩ : Σ k, Combinatorics.BinaryHierarchyShape k),
      (⟨n-t.1.val, t.2.2⟩ : Σ k, Combinatorics.BinaryHierarchyShape k)))
    (fun p => by
      by_cases he : Even n
      · exact (Sym2.map (Sigma.mk (n / 2))) (cast (by rw [ite_eq_left he]) p)
      · exact (cast (by rw [ite_eq_right he]) p : Empty).elim)
/-- Source: wedderburn1922, §1, p. 122. -/
theorem binaryHierarchyRootTargetPair_injective (n : ℕ) (hn : 2 ≤ n) :
    Function.Injective (binaryHierarchyRootTargetPair n) := by
  classical
  intro t u he
  rcases t with ⟨k, a, b⟩ | t <;> rcases u with ⟨l, c, d⟩ | u
  · change s((⟨k.val,a⟩ : Σ i, Combinatorics.BinaryHierarchyShape i),⟨n - k.val,b⟩) =
      s((⟨l.val,c⟩ : Σ i, Combinatorics.BinaryHierarchyShape i),⟨n - l.val,d⟩) at he
    rcases Sym2.eq_iff.mp he with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · have hkl := congrArg Sigma.fst h1
      dsimp only at hkl
      have hk : k = l := Subtype.ext hkl
      subst l
      have ha := eq_of_heq (Sigma.mk.inj h1).2
      have hb := eq_of_heq (Sigma.mk.inj h2).2
      subst c
      subst d
      rfl
    · have hkl := congrArg Sigma.fst h1
      have hlk := congrArg Sigma.fst h2
      dsimp only at hkl hlk
      have hk := mem_Ico.mp k.property
      have hl := mem_Ico.mp l.property
      omega
  · by_cases hnE : Even n
    · have hhalf : n = 2 * (n / 2) := by obtain ⟨v,hv⟩ := hnE; omega
      have he' : s((⟨k.val,a⟩ : Σ i, Combinatorics.BinaryHierarchyShape i),⟨n - k.val,b⟩) =
          Sym2.map (Sigma.mk (n / 2)) (cast (by rw [ite_eq_left hnE]) u) := by
        simpa only [binaryHierarchyRootTargetPair, hnE, ↓reduceDIte, Sum.elim_inl,
          Sum.elim_inr] using he
      obtain ⟨⟨c,d⟩,hu⟩ := Sym2.mk_surjective (cast (by rw [ite_eq_left hnE]) u)
      rw [← hu] at he'
      change s((⟨k.val,a⟩ : Σ i, Combinatorics.BinaryHierarchyShape i),⟨n - k.val,b⟩) =
        s((⟨n / 2,c⟩ : Σ i, Combinatorics.BinaryHierarchyShape i),⟨n / 2,d⟩) at he'
      rcases Sym2.eq_iff.mp he' with ⟨h1,_⟩ | ⟨h1,_⟩ <;>
        have hk := congrArg Sigma.fst h1 <;>
        have hki := mem_Ico.mp k.property <;> dsimp only at hk <;> omega
    · exact (cast (by rw [ite_eq_right hnE]) u : Empty).elim
  · by_cases hnE : Even n
    · have hhalf : n = 2 * (n / 2) := by obtain ⟨v,hv⟩ := hnE; omega
      have he' : Sym2.map (Sigma.mk (n / 2)) (cast (by rw [ite_eq_left hnE]) t) =
          s((⟨l.val,c⟩ : Σ i, Combinatorics.BinaryHierarchyShape i),⟨n - l.val,d⟩) := by
        simpa only [binaryHierarchyRootTargetPair, hnE, ↓reduceDIte, Sum.elim_inl,
          Sum.elim_inr] using he
      obtain ⟨⟨a,b⟩,ht⟩ := Sym2.mk_surjective (cast (by rw [ite_eq_left hnE]) t)
      rw [← ht] at he'
      change s((⟨n / 2,a⟩ : Σ i, Combinatorics.BinaryHierarchyShape i),⟨n / 2,b⟩) =
        s((⟨l.val,c⟩ : Σ i, Combinatorics.BinaryHierarchyShape i),⟨n - l.val,d⟩) at he'
      rcases Sym2.eq_iff.mp he' with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;>
        have hk := congrArg Sigma.fst h1 <;>
        have hl := congrArg Sigma.fst h2 <;>
        have hli := mem_Ico.mp l.property <;> dsimp only at hk hl <;> omega
    · exact (cast (by rw [ite_eq_right hnE]) t : Empty).elim
  · by_cases hnE : Even n
    · have he' : Sym2.map (Sigma.mk (n / 2)) (cast (by rw [ite_eq_left hnE]) t) =
          Sym2.map (Sigma.mk (n / 2)) (cast (by rw [ite_eq_left hnE]) u) := by
        simpa [binaryHierarchyRootTargetPair, hnE] using he
      apply congrArg Sum.inr
      exact (Equiv.cast (by rw [ite_eq_left hnE])).injective
        (Sym2.map.injective (by intro x y h; exact eq_of_heq (Sigma.mk.inj h).2) he')
    · exact (cast (by rw [ite_eq_right hnE]) t : Empty).elim
/-- Source: wedderburn1922, §1, p. 122. -/
private theorem sym2_sigma_map_cast (m l : ℕ) (h : m = l)
    (p : Sym2 (Combinatorics.BinaryHierarchyShape m)) :
    Sym2.map (Sigma.mk l)
        (cast (congrArg (fun k => Sym2 (Combinatorics.BinaryHierarchyShape k)) h) p) =
      Sym2.map (Sigma.mk m) p := by
  subst l
  rfl
/-- Source: wedderburn1922, §1, p. 122. -/
theorem binaryHierarchyRootTargetPair_surjective_sizes (n m l : ℕ)
    (hn : 2 ≤ n) (hm : 1 ≤ m) (hl : 1 ≤ l) (hml : m + l = n)
    (G : Combinatorics.BinaryHierarchyShape m) (H : Combinatorics.BinaryHierarchyShape l) :
    ∃ t : BinaryHierarchyRootTarget n,
      binaryHierarchyRootTargetPair n t =
        s((⟨m, G⟩ : Σ k, Combinatorics.BinaryHierarchyShape k),
          (⟨l, H⟩ : Σ k, Combinatorics.BinaryHierarchyShape k)) := by
  classical
  by_cases hlt : m < l
  · have hln : l = n - m := by omega
    subst l
    have hmi : m ∈ Ico 1 ((n - 1) / 2+1) := mem_Ico.mpr ⟨hm, by omega⟩
    exact ⟨Sum.inl ⟨⟨m,hmi⟩,G,H⟩, rfl⟩
  · by_cases hgt : l < m
    · have hmn : m = n - l := by omega
      subst m
      have hli : l ∈ Ico 1 ((n - 1) / 2+1) := mem_Ico.mpr ⟨hl, by omega⟩
      exact ⟨Sum.inl ⟨⟨l,hli⟩,H,G⟩, Sym2.eq_swap⟩
    · have heq : m = l := by omega
      subst l
      subst n
      have hnE : Even (m + m) := ⟨m,rfl⟩
      have hhalf : (m + m) / 2 = m := by omega
      refine ⟨Sum.inr (cast (by rw [ite_eq_left hnE, hhalf]) s(G,H)), ?_⟩
      simp only [binaryHierarchyRootTargetPair, hnE, ↓reduceDIte, Sum.elim_inr]
      convert sym2_sigma_map_cast m ((m + m) / 2) hhalf.symm s(G,H) using 1
      all_goals first
        | rfl
        | exact congrArg (Sym2.map (Sigma.mk ((m + m) / 2))) (cast_cast _ _ _)

end Rhone.Coalescent
