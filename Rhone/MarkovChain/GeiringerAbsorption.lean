/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.GeiringerTrajectory
public import Mathlib.Tactic.Push

/-! # Structural absorption of the partition fragmentation chain under a separating mask -/

@[expose] public section
namespace Rhone.MarkovChain.Geiringer
open Finset

theorem split_partition_le {κ : Type*} [Fintype κ] [DecidableEq κ]
    (π : Finpartition (Finset.univ : Finset κ)) (masks : π.parts → Finset κ) :
    splitPartition π masks ≤ π := by
  intro C hC
  obtain ⟨B, hB, hCB⟩ := Finpartition.mem_bind.mp hC
  exact ⟨B, hB, (Finpartition.atomise B {masks ⟨B, hB⟩}).le hCB⟩

theorem split_partition_bottom {κ : Type*} [Fintype κ] [DecidableEq κ]
    (masks : (⊥ : Finpartition (Finset.univ : Finset κ)).parts → Finset κ) :
    splitPartition ⊥ masks = ⊥ :=
  le_antisymm (split_partition_le ⊥ masks) bot_le

theorem atomise_singleton_card_pos {κ : Type*} [DecidableEq κ]
    (B mask : Finset κ) (hB : B.Nonempty) :
    1 ≤ (Finpartition.atomise B {mask}).parts.card := by
  have hne : (Finpartition.atomise B {mask}).parts ≠ ∅ := by
    intro heq
    exact hB.ne_empty (Finpartition.parts_eq_empty_iff.mp heq)
  exact Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hne)

theorem atomise_singleton_card_gt_one {κ : Type*} [DecidableEq κ]
    (B mask : Finset κ) (hfirst : (B ∩ mask).Nonempty) (hsecond : (B \ mask).Nonempty) :
    1 < (Finpartition.atomise B {mask}).parts.card := by
  rw [atomise_singleton_parts]
  apply Finset.one_lt_card.mpr
  refine ⟨B ∩ mask, ?_, B \ mask, ?_, ?_⟩
  · simp [hfirst.ne_empty]
  · simp [hsecond.ne_empty]
  · intro heq
    obtain ⟨i, hi⟩ := hfirst
    have hi' : i ∈ B \ mask := heq ▸ hi
    exact (mem_sdiff.mp hi').2 (mem_inter.mp hi).2

theorem fragmentation_constant_mask_positive
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (ρ : Finset κ → ℝ) (hρ0 : ∀ mask, 0 ≤ ρ mask)
    (π : Finpartition (Finset.univ : Finset κ)) (mask : Finset κ)
    (hmask : 0 < ρ mask) :
    0 < fragmentationMatrix ρ π (splitPartition π (fun _ => mask)) := by
  classical
  unfold fragmentationMatrix
  have hpos : 0 < (∏ B : π.parts, ρ ((fun _ : π.parts => mask) B))*
      (if splitPartition π (fun _ => mask)=splitPartition π (fun _ => mask) then 1 else 0) := by
    simp only [ite_true, mul_one]
    exact prod_pos fun _ _ => hmask
  apply lt_of_lt_of_le hpos
  apply single_le_sum (f := fun masks : π.parts → Finset κ =>
    (∏ B, ρ (masks B))*
      (if splitPartition π masks=splitPartition π (fun _ => mask) then 1 else 0))
    (a := fun _ => mask)
  · intro masks _
    exact mul_nonneg (prod_nonneg fun B _ => hρ0 (masks B)) (by positivity)
  · exact mem_univ _

theorem separating_mask_exists {κ : Type*} [Fintype κ] [DecidableEq κ]
    (ρ : Finset κ → ℝ) (hρ0 : ∀ mask, 0 ≤ ρ mask) (i j : κ)
    (hsep : 0 < separationProbability ρ i j) :
    ∃ mask, 0 < ρ mask ∧
      ((i ∈ mask ∧ j ∉ mask) ∨ (i ∉ mask ∧ j ∈ mask)) := by
  classical
  unfold separationProbability at hsep
  obtain ⟨mask, _, hterm⟩ := (sum_pos_iff_of_nonneg (fun mask _ =>
    mul_nonneg (hρ0 mask) (by positivity))).mp hsep
  by_cases hs : (i ∈ mask ∧ j ∉ mask) ∨ (i ∉ mask ∧ j ∈ mask)
  · exact ⟨mask, by simpa only [ite_eq_left hs, mul_one] using hterm, hs⟩
  · simp only [ite_eq_right hs, mul_zero, lt_self_iff_false] at hterm

theorem split_partition_card_gt {κ : Type*} [Fintype κ] [DecidableEq κ]
    (π : Finpartition (Finset.univ : Finset κ)) (mask B : Finset κ)
    (hB : B ∈ π.parts) (hfirst : (B ∩ mask).Nonempty) (hsecond : (B \ mask).Nonempty) :
    π.parts.card < (splitPartition π (fun _ => mask)).parts.card := by
  classical
  unfold splitPartition
  rw [Finpartition.card_bind]
  have hle (D : π.parts) : 1 ≤ (Finpartition.atomise D.val {mask}).parts.card :=
    atomise_singleton_card_pos D.val mask
      (Finset.nonempty_iff_ne_empty.mpr (π.ne_bot D.property))
  have hstrict : ∃ D ∈ π.parts.attach,
      1 < (Finpartition.atomise D.val {mask}).parts.card :=
    ⟨⟨B, hB⟩, mem_attach _ _, atomise_singleton_card_gt_one B mask hfirst hsecond⟩
  have hlt := sum_lt_sum (s := π.parts.attach) (f := fun _ : π.parts => (1 : ℕ))
    (g := fun D : π.parts => (Finpartition.atomise D.val {mask}).parts.card)
    (fun D _ => hle D) hstrict
  simpa only [sum_const, card_attach, smul_eq_mul, mul_one] using hlt

theorem exists_nonsingleton_block {κ : Type*} [Fintype κ] [DecidableEq κ]
    (π : Finpartition (Finset.univ : Finset κ)) (hπ : π ≠ ⊥) :
    ∃ B ∈ π.parts, 1 < B.card := by
  by_contra hn
  push Not at hn
  apply hπ
  apply le_antisymm _ bot_le
  intro B hB
  obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr (π.ne_bot hB)
  refine ⟨{i}, Finpartition.mem_bot_iff.mpr ⟨i, mem_univ _, rfl⟩, ?_⟩
  intro j hj
  exact mem_singleton.mpr (Finset.card_le_one.mp (hn B hB) j hj i hi)

theorem fragmentation_increases_parts {κ : Type*} [Fintype κ] [DecidableEq κ]
    (ρ : Finset κ → ℝ) (hρ0 : ∀ mask, 0 ≤ ρ mask)
    (π : Finpartition (Finset.univ : Finset κ)) (hπ : π ≠ ⊥)
    (hsep : ∀ i j, i ≠ j → 0 < separationProbability ρ i j) :
    ∃ σ, 0 < fragmentationMatrix ρ π σ ∧ π.parts.card < σ.parts.card := by
  obtain ⟨B, hB, hcard⟩ := exists_nonsingleton_block π hπ
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hcard
  obtain ⟨mask, hm, hsplit⟩ := separating_mask_exists ρ hρ0 i j (hsep i j hij)
  refine ⟨splitPartition π (fun _ => mask),
    fragmentation_constant_mask_positive ρ hρ0 π mask hm, ?_⟩
  rcases hsplit with ⟨him, hjm⟩ | ⟨him, hjm⟩
  · exact split_partition_card_gt π mask B hB
      ⟨i, mem_inter.mpr ⟨hi, him⟩⟩ ⟨j, mem_sdiff.mpr ⟨hj, hjm⟩⟩
  · exact split_partition_card_gt π mask B hB
      ⟨j, mem_inter.mpr ⟨hj, hjm⟩⟩ ⟨i, mem_sdiff.mpr ⟨hi, him⟩⟩

theorem fragmentation_bottom_absorbing {κ : Type*} [Fintype κ] [DecidableEq κ]
    (ρ : Finset κ → ℝ) (hρ0 : ∀ mask, 0 ≤ ρ mask) (hρ : ∑ mask, ρ mask = 1) :
    (fragmentationChain ρ hρ0 hρ).IsAbsorbing ⊥ := by
  classical
  change fragmentationMatrix ρ ⊥ ⊥ = 1
  unfold fragmentationMatrix
  simp_rw [split_partition_bottom]
  simp only [ite_true, mul_one]
  have h := Fintype.prod_sum
    (fun (_ : (⊥ : Finpartition (Finset.univ : Finset κ)).parts) (mask : Finset κ) => ρ mask)
  simpa only [hρ, prod_const_one] using h.symm

theorem fragmentation_reaches_bottom {κ : Type*} [Fintype κ] [DecidableEq κ]
    (ρ : Finset κ → ℝ) (hρ0 : ∀ mask, 0 ≤ ρ mask) (hρ : ∑ mask, ρ mask = 1)
    (hsep : ∀ i j, i ≠ j → 0 < separationProbability ρ i j) :
    (fragmentationChain ρ hρ0 hρ).Reaches {⊥} := by
  classical
  apply Rhone.MarkovChain.FinChain.reaches_of_rank _ _
    (fun π => Fintype.card κ-π.parts.card)
  intro π hπ
  have hne : π ≠ ⊥ := by simpa only [mem_singleton] using hπ
  obtain ⟨σ, hpos, hcard⟩ := fragmentation_increases_parts ρ hρ0 π hne hsep
  refine ⟨σ, hpos, ?_⟩
  have hbound := σ.card_parts_le_card
  simp only [card_univ] at hbound
  omega

end Rhone.MarkovChain.Geiringer
