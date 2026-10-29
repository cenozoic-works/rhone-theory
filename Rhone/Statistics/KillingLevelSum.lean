/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Statistics.KillingWeight
public import Rhone.Statistics.KillPatternWeight

/-!
# Level sums of the killing weight and the average-merge recursion

Source: durrett2008, sec. 1.3.1. -/

@[expose] public section
namespace Rhone.Statistics
open Finset Coalescent Rhone.Combinatorics MarkovChain

section powerset

variable {ι : Type*} [DecidableEq ι]

theorem sum_powerset_killPatternWeight {β : ℝ} (hβ : 0 ≤ β) {m : ℕ} {F : Finset ι}
    (hF : F.card ≤ m) (G : Finset ι → ℝ) :
    (1 + β * m) * ∑ Z ∈ F.powerset, killPatternWeight β Z.card (m - Z.card) * G Z =
      G ∅ + β * ∑ x ∈ F, ∑ Z ∈ (F.erase x).powerset,
        killPatternWeight β Z.card (m - (Z.card + 1)) * G (insert x Z) := by
  have hne : (1 + β * (m : ℝ)) ≠ 0 := (one_add_mul_pos hβ (Nat.cast_nonneg m)).ne'
  have step1 : ∀ Z ∈ F.powerset,
      (1 + β * m) * (killPatternWeight β Z.card (m - Z.card) * G Z) =
        (if Z = ∅ then G ∅ else 0) + β * ∑ x ∈ F,
          (if x ∈ Z then killPatternWeight β (Z.card - 1) (m - Z.card) * G Z else 0) := by
    intro Z hZ
    have hZF := mem_powerset.1 hZ
    have hle : Z.card ≤ m := (card_le_card hZF).trans hF
    rcases Z.eq_empty_or_nonempty with rfl | hZne
    · have h0 : ∀ v : ℝ, ∑ x ∈ F, (if x ∈ (∅ : Finset ι) then v else 0) = 0 := fun v =>
        Finset.sum_eq_zero fun x _ => ite_eq_right (Finset.notMem_empty x)
      rw [ite_eq_left rfl, h0, mul_zero, add_zero, Finset.card_empty, Nat.sub_zero,
        killPatternWeight_zero]
      field_simp
    · rw [ite_eq_right hZne.ne_empty, zero_add, ← Finset.sum_filter,
        Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hZF, Finset.sum_const, nsmul_eq_mul]
      obtain ⟨d, hd⟩ : ∃ d, Z.card = d + 1 :=
        ⟨Z.card - 1, by have := Finset.card_pos.2 hZne; omega⟩
      have hcast : ((m - (d + 1) : ℕ) : ℝ) + d + 1 = m := by
        rw [Nat.cast_sub (by omega)]
        push_cast
        ring
      rw [hd, Nat.add_sub_cancel, killPatternWeight_succ hβ, hcast]
      push_cast
      field_simp
  have step2 : ∀ x ∈ F, ∑ Z ∈ F.powerset,
      (if x ∈ Z then killPatternWeight β (Z.card - 1) (m - Z.card) * G Z else 0) =
      ∑ Z ∈ (F.erase x).powerset,
        killPatternWeight β Z.card (m - (Z.card + 1)) * G (insert x Z) := by
    intro x hx
    have hins : F.powerset = (insert x (F.erase x)).powerset := by rw [Finset.insert_erase hx]
    have hz : ∑ Z ∈ (F.erase x).powerset,
        (if x ∈ Z then killPatternWeight β (Z.card - 1) (m - Z.card) * G Z else 0) = 0 :=
      Finset.sum_eq_zero fun Z hZ => ite_eq_right fun hxZ =>
        Finset.notMem_erase x F (mem_powerset.1 hZ hxZ)
    rw [hins, Finset.sum_powerset_insert (Finset.notMem_erase x F), hz, zero_add]
    refine Finset.sum_congr rfl fun Z hZ => ?_
    have hxZ : x ∉ Z := fun hxZ => Finset.notMem_erase x F (mem_powerset.1 hZ hxZ)
    rw [ite_eq_left (mem_insert_self x Z), Finset.card_insert_of_notMem hxZ,
      Nat.add_sub_cancel]
  rw [Finset.mul_sum, Finset.sum_congr rfl step1, Finset.sum_add_distrib,
    Finset.sum_eq_single_of_mem ∅ (Finset.empty_mem_powerset F) (fun Z _ hZ => ite_eq_right hZ),
    ite_eq_left rfl, ← Finset.mul_sum, Finset.sum_comm, Finset.sum_congr rfl step2]

end powerset

variable {α κ : Type*} [Fintype α] [DecidableEq α] [DecidableEq κ] {θ : ℝ}
  {π : Finpartition (univ : Finset α)} {A : Finset α} {c : α → κ}

def fullBlocks (π : Finpartition (univ : Finset α)) (A : Finset α) (c : α → κ) :
    Finset (Finset α) :=
  π.parts.filter (labelFull π.parts (blockLabels A c))

theorem fullBlocks_sdiff {x : Finset α} (hx : x ∈ fullBlocks π A c) :
    fullBlocks π (A \ x) c = fullBlocks π A c := by
  obtain ⟨hxp, hxf⟩ := mem_filter.1 hx
  ext y
  simp only [fullBlocks, mem_filter]
  refine and_congr_right fun hy => ?_
  rw [labelFull_congr (fun B hB => blockLabels_sdiff hxp hB) hy,
    labelFull_update_empty hxf hy]

noncomputable def avgMerge (θ : ℝ) (π : Finpartition (univ : Finset α)) (A : Finset α)
    (c : α → κ) : ℝ :=
  ((π.parts.card.choose 2 : ℕ) : ℝ)⁻¹ * ∑ σ ∈ merges π, killingWeight θ σ A c

noncomputable def levelSum (θ : ℝ) (π : Finpartition (univ : Finset α)) (A : Finset α)
    (c : α → κ) : ℝ :=
  ∑ Z ∈ (fullBlocks π A c).powerset,
    killPatternWeight (θ / ((π.parts.card : ℝ) * ((π.parts.card : ℝ) - 1))) Z.card
      (π.parts.card - Z.card) * avgMerge θ π (A \ Z.sup id) c

theorem killingWeight_eq_avgMerge_add (hθ : 0 < θ) (hm : 2 ≤ π.parts.card) (A : Finset α)
    (c : α → κ) :
    (1 + θ / ((π.parts.card : ℝ) * ((π.parts.card : ℝ) - 1)) * (π.parts.card : ℝ)) *
        killingWeight θ π A c =
      avgMerge θ π A c + θ / ((π.parts.card : ℝ) * ((π.parts.card : ℝ) - 1)) *
        ∑ x ∈ fullBlocks π A c, killingWeight θ π (A \ x) c := by
  have h := killingWeight_recursion hθ π A c
  have hm2 : (2 : ℝ) ≤ (π.parts.card : ℝ) := by exact_mod_cast hm
  have hm0 : (π.parts.card : ℝ) ≠ 0 := by linarith
  have hm1 : (π.parts.card : ℝ) - 1 ≠ 0 := by linarith
  unfold avgMerge fullBlocks
  rw [sum_merges, Nat.cast_choose_two]
  field_simp
  linear_combination h

theorem levelSum_eq (hθ : 0 < θ) (hm : 2 ≤ π.parts.card) (c : α → κ) (A : Finset α) :
    levelSum θ π A c = killingWeight θ π A c := by
  induction A using Finset.strongInduction with
  | H A ih =>
    have hm2 : (2 : ℝ) ≤ (π.parts.card : ℝ) := by exact_mod_cast hm
    have hβ : 0 ≤ θ / ((π.parts.card : ℝ) * ((π.parts.card : ℝ) - 1)) :=
      div_nonneg hθ.le (mul_nonneg (by linarith) (by linarith))
    have hFm : (fullBlocks π A c).card ≤ π.parts.card := card_le_card (filter_subset _ _)
    have h1 := sum_powerset_killPatternWeight hβ hFm
      (fun Z => avgMerge θ π (A \ Z.sup id) c)
    have h2 : ∀ x ∈ fullBlocks π A c, ∑ Z ∈ ((fullBlocks π A c).erase x).powerset,
        killPatternWeight (θ / ((π.parts.card : ℝ) * ((π.parts.card : ℝ) - 1))) Z.card
          (π.parts.card - (Z.card + 1)) * avgMerge θ π (A \ (insert x Z).sup id) c =
        levelSum θ π (A \ x) c := by
      intro x hx
      have hins : (fullBlocks π A c).powerset =
          (insert x ((fullBlocks π A c).erase x)).powerset := by rw [Finset.insert_erase hx]
      unfold levelSum
      rw [fullBlocks_sdiff hx, hins,
        Finset.sum_powerset_insert (Finset.notMem_erase x (fullBlocks π A c)),
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun Z hZ => ?_
      have hZs := mem_powerset.1 hZ
      have hxZ : x ∉ Z := fun hxZ => Finset.notMem_erase x _ (hZs hxZ)
      have hZc : Z.card < π.parts.card := by
        have h3 := card_le_card hZs
        have h4 := Finset.card_erase_lt_of_mem hx
        omega
      have hs1 : (A \ x) \ Z.sup id = A \ (insert x Z).sup id := by
        rw [Finset.sup_insert, id, sdiff_sdiff_left]
      have hs2 : (A \ x) \ (insert x Z).sup id = A \ (insert x Z).sup id := by
        rw [Finset.sup_insert, id, sdiff_sdiff_left, ← sup_assoc, sup_idem]
      have hsplit := killPatternWeight_split hβ Z.card (π.parts.card - (Z.card + 1))
      have hsub : π.parts.card - (Z.card + 1) + 1 = π.parts.card - Z.card := by omega
      rw [hsub] at hsplit
      rw [hs1, hs2, Finset.card_insert_of_notMem hxZ, hsplit]
      ring
    have h3 := killingWeight_eq_avgMerge_add hθ hm A c
    have h4 : ∀ x ∈ fullBlocks π A c,
        levelSum θ π (A \ x) c - killingWeight θ π (A \ x) c =
          if A \ x = A then levelSum θ π A c - killingWeight θ π A c else 0 := by
      intro x _
      by_cases hAx : A \ x = A
      · rw [ite_eq_left hAx, hAx]
      · rw [ite_eq_right hAx, ih (A \ x) (Finset.sdiff_subset.ssubset_of_ne hAx), sub_self]
    have h5 : ∑ x ∈ fullBlocks π A c,
        (levelSum θ π (A \ x) c - killingWeight θ π (A \ x) c) =
        (((fullBlocks π A c).filter fun x => A \ x = A).card : ℝ) *
          (levelSum θ π A c - killingWeight θ π A c) := by
      rw [Finset.sum_congr rfl h4, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hd : (((fullBlocks π A c).filter fun x => A \ x = A).card : ℝ) ≤
        (π.parts.card : ℝ) := by
      exact_mod_cast (card_le_card (filter_subset _ _)).trans hFm
    rw [Finset.sum_sub_distrib] at h5
    beta_reduce at h1
    rw [Finset.sup_empty, Finset.bot_eq_empty, Finset.sdiff_empty,
      Finset.sum_congr rfl h2] at h1
    have h6 : (levelSum θ π A c - killingWeight θ π A c) *
        (1 + θ / ((π.parts.card : ℝ) * ((π.parts.card : ℝ) - 1)) * ((π.parts.card : ℝ) -
          (((fullBlocks π A c).filter fun x => A \ x = A).card : ℝ))) = 0 := by
      have h1' : (1 + θ / ((π.parts.card : ℝ) * ((π.parts.card : ℝ) - 1)) *
          (π.parts.card : ℝ)) * levelSum θ π A c = avgMerge θ π A c +
            θ / ((π.parts.card : ℝ) * ((π.parts.card : ℝ) - 1)) *
              ∑ x ∈ fullBlocks π A c, levelSum θ π (A \ x) c := h1
      linear_combination h1' - h3 +
        θ / ((π.parts.card : ℝ) * ((π.parts.card : ℝ) - 1)) * h5
    have hpos : 0 < 1 + θ / ((π.parts.card : ℝ) * ((π.parts.card : ℝ) - 1)) *
        ((π.parts.card : ℝ) - (((fullBlocks π A c).filter fun x => A \ x = A).card : ℝ)) :=
      one_add_mul_pos hβ (by linarith)
    exact sub_eq_zero.1 ((mul_eq_zero.1 h6).resolve_right hpos.ne')

end Rhone.Statistics
