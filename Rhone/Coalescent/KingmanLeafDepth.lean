/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanRootSampling
/-!
# Retained-clade depths under chronological Kingman merger histories

Source: kingman1982, Thm 1, eq. (1.13), (2.2). -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
noncomputable def leafCladeDepth {L : Type*} [DecidableEq L]
    (G : Finset (Finset L)) (x : L) : ℕ :=
  (G.filter (fun C => x ∈ C)).card - 1
theorem card_roots_without_leaf {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (hF : ADR11.IsForest F) (x : L)
    (hx : x ∈ ADR11.lineages F) :
    ((ADR11.roots F).filter (fun C => C ⊆ univ \ {x})).card + 1 = (ADR11.roots F).card := by
  obtain ⟨R, hR, hxR⟩ := ADR11.exists_mem_roots_of_mem_lineages hx
  have he : (ADR11.roots F).filter (fun C => C ⊆ univ \ {x}) = (ADR11.roots F).erase R := by
    ext C
    simp only [mem_filter, mem_erase]
    constructor
    · rintro ⟨hC, hc⟩
      refine ⟨?_, hC⟩
      intro hCR
      have hxC : x ∈ C := hCR.symm ▸ hxR
      exact (mem_sdiff.mp (hc hxC)).2 (mem_singleton_self x)
    · rintro ⟨hCR, hC⟩
      refine ⟨hC, ?_⟩
      intro y hy
      refine mem_sdiff.mpr ⟨mem_univ y, ?_⟩
      intro hyx
      have he := mem_singleton.mp hyx
      subst y
      exact disjoint_left.mp (hF.disjoint_of_mem_roots hC hR hCR) hy hxR
  rw [he, card_erase_add_one hR]
theorem sum_jump_leaf_depth {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (hF : ADR11.IsForest F) (x : L)
    (hx : x ∈ ADR11.lineages F) (hk : 2 ≤ (ADR11.roots F).card) :
    (∑ G ∈ ADR11.merges F, ADR11.jumpMatrix F G * (leafCladeDepth G x : ℝ)) =
      (leafCladeDepth F x : ℝ) + 2 / (ADR11.roots F).card := by
  classical
  obtain ⟨R, hR, hxR⟩ := ADR11.exists_mem_roots_of_mem_lineages hx
  have hdpos : 0 < (F.filter (fun C => x ∈ C)).card :=
    card_pos.mpr ⟨R, mem_filter.mpr ⟨ADR11.roots_subset F hR, hxR⟩⟩
  have hterm : ∀ G ∈ ADR11.merges F,
      (leafCladeDepth G x : ℝ) = (leafCladeDepth F x : ℝ) +
        (1 - if ∀ C ∈ G \ F, C ⊆ univ \ {x} then (1 : ℝ) else 0) := by
    intro G hG
    obtain ⟨B, hB, C, hC, hBC, rfl⟩ := ADR11.mem_merges.mp hG
    have hU := ADR11.union_not_mem_of_mem_roots hB hC hBC
    have he : insert (B ∪ C) F \ F = {B ∪ C} := by
      ext D
      simp only [mem_sdiff, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hD, hn⟩
        exact hD.resolve_right hn
      · intro hD
        subst D
        exact ⟨Or.inl rfl, hU⟩
    have hp : (∀ D ∈ insert (B ∪ C) F \ F, D ⊆ univ \ {x}) ↔ x ∉ B ∪ C := by
      rw [he]
      simp only [mem_singleton, forall_eq, subset_sdiff, subset_univ, true_and,
        disjoint_singleton_right]
    simp only [hp]
    by_cases hxu : x ∈ B ∪ C
    · have hc : ((insert (B ∪ C) F).filter (fun D => x ∈ D)).card =
          (F.filter (fun D => x ∈ D)).card + 1 := by
        rw [filter_insert, ite_eq_left hxu, card_insert_of_notMem]
        exact fun h => hU (mem_filter.mp h).1
      have hd : leafCladeDepth (insert (B ∪ C) F) x = leafCladeDepth F x + 1 := by
        unfold leafCladeDepth
        rw [hc]
        omega
      simp only [hxu, not_true_eq_false, ite_false, sub_zero, hd, Nat.cast_add, Nat.cast_one]
    · simp only [hxu, not_false_eq_true, ite_true, sub_self, add_zero]
      unfold leafCladeDepth
      rw [filter_insert, ite_eq_right hxu]
  have hsum : (∑ G ∈ ADR11.merges F,
      ((leafCladeDepth F x : ℝ) +
        (1 - if ∀ C ∈ G \ F, C ⊆ univ \ {x} then (1 : ℝ) else 0))) =
      ((ADR11.roots F).card.choose 2 : ℝ) * (leafCladeDepth F x : ℝ) +
        ((ADR11.roots F).card.choose 2 : ℝ) -
          ((((ADR11.roots F).filter (fun C => C ⊆ univ \ {x})).card).choose 2 : ℝ) := by
    rw [sum_add_distrib, sum_sub_distrib, ← sum_filter]
    simp only [sum_const, nsmul_eq_mul, hF.card_merges, Combinatorics.card_merges_within F hF
        (univ \ {x})]
    ring
  have hfirst : ∀ G ∈ ADR11.merges F,
      ADR11.jumpMatrix F G * (leafCladeDepth G x : ℝ) =
        ((ADR11.roots F).card.choose 2 : ℝ)⁻¹ *
          ((leafCladeDepth F x : ℝ) +
            (1 - if ∀ C ∈ G \ F, C ⊆ univ \ {x} then (1 : ℝ) else 0)) := by
    intro G hG
    rw [ADR11.jumpMatrix_apply_of_isForest (by omega), ite_eq_left hG, hterm G hG]
  rw [sum_congr rfl hfirst, ← mul_sum, hsum]
  have hr := card_roots_without_leaf F hF x hx
  have hre : ((ADR11.roots F).filter (fun C => C ⊆ univ \ {x})).card =
      (ADR11.roots F).card - 1 := by omega
  rw [hre]
  have hkc : ((ADR11.roots F).card.choose 2 : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_ne_zero hk)
  have hk0 : ((ADR11.roots F).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hk1 : ((ADR11.roots F).card : ℝ) - 1 ≠ 0 := by
    have hkr : (2 : ℝ) ≤ (ADR11.roots F).card := by exact_mod_cast hk
    linarith
  rw [Nat.cast_choose_two, Nat.cast_choose_two, Nat.cast_sub (by omega : 1 ≤ (ADR11.roots F).card)]
  simp only [Nat.cast_one]
  field_simp
  ring
end Rhone.Coalescent
