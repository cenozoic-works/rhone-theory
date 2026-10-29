/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Rhone.Coalescent.KingmanTopologyWeight

/-! # Retained internal-clade factors split multiplicatively at the binary root -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
theorem coalescent_topology_clade_product_split (n : ℕ) (hn : 2 ≤ n) (T : LabelledTopology n)
    (A : Finset (Fin n)) (hA : A.Nonempty) (hAc : (univ \ A).Nonempty)
    (hs : ADR11.roots (T.1.erase univ) = {A, univ \ A}) :
    coalescentTopologyCladeProduct T = (n - 1) *
      (∏ C ∈ (T.1.filter (fun C => C ⊆ A)).filter (fun C => 2 ≤ C.card), (C.card - 1)) *
      (∏ C ∈ (T.1.filter (fun C => C ⊆ univ \ A)).filter
        (fun C => 2 ≤ C.card), (C.card - 1)) := by
  classical
  let X := (T.1.filter (fun C => C ⊆ A)).filter (fun C => 2 ≤ C.card)
  let Y := (T.1.filter (fun C => C ⊆ univ \ A)).filter (fun C => 2 ≤ C.card)
  have hXa : ∀ C ∈ X, C ⊆ A := fun C hC => (mem_filter.mp (mem_filter.mp hC).1).2
  have hYb : ∀ C ∈ Y, C ⊆ univ \ A :=
    fun C hC => (mem_filter.mp (mem_filter.mp hC).1).2
  have hd : Disjoint X Y := by
    apply disjoint_left.mpr
    intro C hx hy
    have hc : C.Nonempty := card_pos.mp (lt_of_lt_of_le (by norm_num) (mem_filter.mp hx).2)
    obtain ⟨x, hxC⟩ := hc
    exact (mem_sdiff.mp (hYb C hy hxC)).2 (hXa C hx hxC)
  have huX : (univ : Finset (Fin n)) ∉ X := by
    intro hu
    obtain ⟨x, hx⟩ := hAc
    exact (mem_sdiff.mp hx).2 (hXa univ hu (mem_univ x))
  have huY : (univ : Finset (Fin n)) ∉ Y := by
    intro hu
    obtain ⟨x, hx⟩ := hA
    exact (mem_sdiff.mp (hYb univ hu (mem_univ x))).2 hx
  have he : T.1.filter (fun C => 2 ≤ C.card) = insert univ (X ∪ Y) := by
    ext C
    constructor
    · intro hc
      obtain ⟨hcT, hc2⟩ := mem_filter.mp hc
      rcases Combinatorics.root_split_clade_purity T.1 A hs C hcT with rfl | ha | hb
      · exact mem_insert_self _ _
      · exact mem_insert_of_mem (mem_union_left _ (mem_filter.mpr
          ⟨mem_filter.mpr ⟨hcT, ha⟩, hc2⟩))
      · exact mem_insert_of_mem (mem_union_right _ (mem_filter.mpr
          ⟨mem_filter.mpr ⟨hcT, hb⟩, hc2⟩))
    · intro hc
      rcases mem_insert.mp hc with rfl | hc
      · exact mem_filter.mpr ⟨T.2.1.1, by simpa using hn⟩
      · rcases mem_union.mp hc with hx | hy
        · exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hx).1).1,
            (mem_filter.mp hx).2⟩
        · exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hy).1).1,
            (mem_filter.mp hy).2⟩
  unfold coalescentTopologyCladeProduct
  rw [he, prod_insert (by simpa only [mem_union, not_or] using And.intro huX huY),
    prod_union hd, card_univ, Fintype.card_fin]
  ac_rfl

theorem clade_product_forestEmbed {L M : Type*} [DecidableEq L] [DecidableEq M]
    (e : L ↪ M) (G : Finset (Finset L)) :
    (∏ C ∈ (forestEmbed e G).filter (fun C => 2 ≤ C.card), (C.card - 1)) =
      ∏ C ∈ G.filter (fun C => 2 ≤ C.card), (C.card - 1) := by
  classical
  have he : (forestEmbed e G).filter (fun C => 2 ≤ C.card) =
      (G.filter (fun C => 2 ≤ C.card)).image (fun C => C.map e) := by
    ext D
    simp only [forestEmbed, mem_filter, mem_image]
    constructor
    · rintro ⟨⟨C, hC, rfl⟩, hc⟩
      exact ⟨C, ⟨hC, by simpa only [card_map] using hc⟩, rfl⟩
    · rintro ⟨C, ⟨hC, hc⟩, rfl⟩
      exact ⟨⟨C, hC, rfl⟩, by simpa only [card_map] using hc⟩
  rw [he, prod_image (fun _ _ _ _ h => Finset.map_injective e h)]
  simp only [card_map]

theorem coalescentTopologyCladeProduct_ne_zero {n : ℕ} (T : LabelledTopology n) :
    coalescentTopologyCladeProduct T ≠ 0 := by
  unfold coalescentTopologyCladeProduct
  apply prod_ne_zero_iff.mpr
  intro C hc
  have hC := (mem_filter.mp hc).2
  omega

theorem topology_clade_factor_arithmetic (a b p q : ℕ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hp : p ≠ 0) (hq : q ≠ 0) :
    (2 : ℝ) / ((a + b - 1 : ℕ) * ((a + b).choose a : ℝ)) *
      ((2 : ℝ) ^ (a - 1) / ((a.factorial : ℝ) * (p : ℝ))) *
      ((2 : ℝ) ^ (b - 1) / ((b.factorial : ℝ) * (q : ℝ))) =
    (2 : ℝ) ^ (a + b - 1) /
      (((a + b).factorial : ℝ) * (((a + b - 1) * p * q : ℕ) : ℝ)) := by
  have hf : (((a + b).choose a : ℕ) : ℝ) * (a.factorial : ℝ) * (b.factorial : ℝ) =
      ((a + b).factorial : ℝ) := by
    have h := Nat.choose_mul_factorial_mul_factorial (show a ≤ a + b by omega)
    rw [Nat.add_sub_cancel_left] at h
    exact_mod_cast h
  have hpow : (2 : ℝ) ^ (a + b - 1) = 2 * (2 : ℝ) ^ (a - 1) * (2 : ℝ) ^ (b - 1) := by
    have he : a + b - 1 = (a - 1) + (b - 1) + 1 := by omega
    rw [he, pow_add, pow_add, pow_one]
    ring
  have hp' : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp
  have hq' : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  have hn' : ((a + b - 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hc' : (((a + b).choose a : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_ne_zero (by omega))
  have ha' : (a.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a)
  have hb' : (b.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero b)
  rw [hpow, ← hf]
  simp only [Nat.cast_mul]
  field_simp
end Rhone.Coalescent
