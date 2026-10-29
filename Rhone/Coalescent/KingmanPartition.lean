/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.Ancestral
public import Rhone.MarkovChain.RateLumping
public import Rhone.Coalescent.KingmanChain

/-! # Kingman's coalescent on partitions of the sample -/

@[expose] public section

namespace Rhone.Coalescent

open Finset MeasureTheory MarkovChain
open scoped ENNReal

variable {α : Type*} [Fintype α] [DecidableEq α]

def mergeBlocksOf (π : Finpartition (univ : Finset α)) (s : Finset (Finset α))
    (hs : s ⊆ π.parts) (hne : s.Nonempty) : Finpartition (univ : Finset α) :=
  (π.ofSubset (sdiff_subset : π.parts \ s ⊆ π.parts) rfl).extend (b := s.sup id)
    (by
      obtain ⟨a, ha⟩ := hne
      exact fun h => π.ne_bot (hs ha) (le_bot_iff.1 (h ▸ Finset.le_sup (f := id) ha)))
    (Finset.disjoint_sup_left.2 fun i hi =>
      π.supIndep hs (mem_sdiff.1 hi).1 (mem_sdiff.1 hi).2)
    (by
      rw [← Finset.sup_union, sdiff_union_of_subset hs]
      exact π.sup_parts)

def mergeBlocks (π : Finpartition (univ : Finset α)) (s : Finset (Finset α)) :
    Finpartition (univ : Finset α) :=
  if h : s ⊆ π.parts ∧ s.Nonempty then mergeBlocksOf π s h.1 h.2 else π

variable {π σ : Finpartition (univ : Finset α)} {s : Finset (Finset α)}

theorem parts_mergeBlocks (hs : s ⊆ π.parts) (hne : s.Nonempty) :
    (mergeBlocks π s).parts = insert (s.sup id) (π.parts \ s) := by
  rw [mergeBlocks, dite_eq_left ⟨hs, hne⟩]
  rfl

theorem le_mergeBlocks (π : Finpartition (univ : Finset α)) (s : Finset (Finset α)) :
    π ≤ mergeBlocks π s := by
  by_cases h : s ⊆ π.parts ∧ s.Nonempty
  · intro b hb
    rw [parts_mergeBlocks h.1 h.2]
    by_cases hbs : b ∈ s
    · exact ⟨s.sup id, mem_insert_self _ _, Finset.le_sup (f := id) hbs⟩
    · exact ⟨b, mem_insert_of_mem (mem_sdiff.2 ⟨hb, hbs⟩), le_rfl⟩
  · rw [mergeBlocks, dite_eq_right h]

theorem sup_notMem_parts (hs : s ⊆ π.parts) (hc : s.card = 2) : s.sup id ∉ π.parts := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hc
  have ha : a ∈ π.parts := hs (by simp)
  have hb : b ∈ π.parts := hs (by simp)
  have hsup : ({a, b} : Finset (Finset α)).sup id = a ∪ b := by simp
  rw [hsup]
  intro hmem
  have h1 : a ∪ b = a := by
    by_contra hne
    have hd : Disjoint (a ∪ b) a := π.disjoint hmem ha hne
    exact π.ne_bot ha (hd.eq_bot_of_ge subset_union_left)
  have h2 : a ∪ b = b := by
    by_contra hne
    have hd : Disjoint (a ∪ b) b := π.disjoint hmem hb hne
    exact π.ne_bot hb (hd.eq_bot_of_ge subset_union_right)
  exact hab (h1.symm.trans h2)

theorem card_parts_mergeBlocks (hs : s ⊆ π.parts) (hc : s.card = 2) :
    (mergeBlocks π s).parts.card + 1 = π.parts.card := by
  have hne : s.Nonempty := card_pos.1 (by omega)
  have hx : s.sup id ∉ π.parts \ s := fun h => sup_notMem_parts hs hc (mem_sdiff.1 h).1
  have hle : s.card ≤ π.parts.card := card_le_card hs
  rw [parts_mergeBlocks hs hne, card_insert_of_notMem hx, card_sdiff_of_subset hs]
  omega

theorem parts_sdiff_parts_mergeBlocks (hs : s ⊆ π.parts) (hc : s.card = 2) :
    π.parts \ (mergeBlocks π s).parts = s := by
  have hne : s.Nonempty := card_pos.1 (by omega)
  have hx := sup_notMem_parts hs hc
  rw [parts_mergeBlocks hs hne]
  ext c
  simp only [mem_sdiff, mem_insert, not_or, not_and, not_not]
  constructor
  · rintro ⟨hcπ, -, h⟩
    exact h hcπ
  · intro hcs
    exact ⟨hs hcs, fun h => hx (h ▸ hs hcs), fun _ => hcs⟩

def merges (π : Finpartition (univ : Finset α)) : Finset (Finpartition (univ : Finset α)) :=
  (powersetCard 2 π.parts).image (mergeBlocks π)

theorem le_of_mem_merges (h : σ ∈ merges π) : π ≤ σ := by
  obtain ⟨s, -, rfl⟩ := mem_image.1 h
  exact le_mergeBlocks π s

theorem card_parts_of_mem_merges (h : σ ∈ merges π) : σ.parts.card + 1 = π.parts.card := by
  obtain ⟨s, hs, rfl⟩ := mem_image.1 h
  rw [mem_powersetCard] at hs
  exact card_parts_mergeBlocks hs.1 hs.2

theorem self_notMem_merges (π : Finpartition (univ : Finset α)) : π ∉ merges π := fun h => by
  have := card_parts_of_mem_merges h
  omega

theorem card_merges (π : Finpartition (univ : Finset α)) :
    (merges π).card = (π.parts.card).choose 2 := by
  rw [merges, card_image_of_injOn, card_powersetCard]
  intro s hs t ht hst
  rw [mem_coe, mem_powersetCard] at hs ht
  rw [← parts_sdiff_parts_mergeBlocks hs.1 hs.2, ← parts_sdiff_parts_mergeBlocks ht.1 ht.2]
  exact congrArg (fun ρ : Finpartition (univ : Finset α) => π.parts \ ρ.parts) hst

noncomputable def partitionQ :
    Matrix (Finpartition (univ : Finset α)) (Finpartition (univ : Finset α)) ℝ := fun π σ =>
  (if σ ∈ merges π then 1 else 0) - if σ = π then (coalRate π.parts.card : ℝ) else 0

theorem coalRate_cast_eq_choose (k : ℕ) : (coalRate k : ℝ) = (k.choose 2 : ℕ) := by
  rw [Nat.cast_choose_two, coalRate]
  push_cast
  ring

variable (α) in
noncomputable def partitionChain : RateChain (Finpartition (univ : Finset α)) where
  Q := partitionQ
  off_diag_nonneg π σ h := by
    simp only [partitionQ, h.symm, ↓reduceIte, sub_zero]
    split_ifs <;> norm_num
  row_sum π := by
    simp only [partitionQ]
    rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_ite_eq', ite_eq_left (mem_univ π),
      coalRate_cast_eq_choose, ← card_merges, sub_eq_zero]
    exact congrArg (fun t : Finset (Finpartition (univ : Finset α)) => (t.card : ℝ))
      (by ext σ; simp)

theorem partitionChain_Q : (partitionChain α).Q = partitionQ := rfl

theorem mem_merges_of_Q_ne_zero (hne : π ≠ σ) (h : (partitionChain α).Q π σ ≠ 0) :
    σ ∈ merges π := by
  by_contra hσ
  exact h (by simp [partitionChain_Q, partitionQ, hσ, Ne.symm hne])

variable (α) in
noncomputable def kingmanAncestral : AncestralProcess α where
  toRateChain := partitionChain α
  coarsens _ _ hne h := le_of_mem_merges (mem_merges_of_Q_ne_zero hne h)

def blockCount (π : Finpartition (univ : Finset α)) : Fin (Fintype.card α + 1) :=
  ⟨π.parts.card, Nat.lt_succ_of_le (by simpa using π.card_parts_le_card)⟩

@[simp]
theorem coe_blockCount (π : Finpartition (univ : Finset α)) :
    (blockCount π : ℕ) = π.parts.card := rfl

theorem blockCount_bot :
    blockCount (⊥ : Finpartition (univ : Finset α)) = Fin.last (Fintype.card α) :=
  Fin.ext (by simp)

theorem card_merges_filter (π : Finpartition (univ : Finset α)) (t : Fin (Fintype.card α + 1)) :
    ((merges π).filter fun σ => blockCount σ = t).card =
      if (t : ℕ) + 1 = π.parts.card then (π.parts.card).choose 2 else 0 := by
  split_ifs with h
  · rw [filter_true_of_mem, card_merges]
    intro σ hσ
    have := card_parts_of_mem_merges hσ
    exact Fin.ext (by rw [coe_blockCount]; omega)
  · rw [filter_false_of_mem, card_empty]
    intro σ hσ hσt
    have := card_parts_of_mem_merges hσ
    exact h (by rw [← hσt, coe_blockCount]; omega)

theorem partitionChain_lumps :
    (partitionChain α).Lumps blockCount (blockChain (Fintype.card α)) := by
  intro π t
  have h1 : ∑ σ with blockCount σ = t, (if σ ∈ merges π then (1 : ℝ) else 0) =
      (((merges π).filter fun σ => blockCount σ = t).card : ℝ) := by
    rw [Finset.sum_boole]
    exact congrArg (fun u : Finset (Finpartition (univ : Finset α)) => (u.card : ℝ))
      (by ext σ; simp [and_comm])
  have h2 : ∑ σ with blockCount σ = t,
      (if σ = π then (coalRate π.parts.card : ℝ) else 0) =
        if blockCount π = t then (coalRate π.parts.card : ℝ) else 0 := by
    rw [Finset.sum_ite_eq']
    simp
  rw [partitionChain_Q]
  simp only [partitionQ]
  rw [Finset.sum_sub_distrib, h1, h2, card_merges_filter, blockChain_Q, blockQ, coe_blockCount,
    coalRate_cast_eq_choose]
  by_cases ht : (t : ℕ) + 1 = π.parts.card
  · have hne : blockCount π ≠ t := fun h => by
      have := congrArg Fin.val h
      rw [coe_blockCount] at this
      omega
    simp [ht, hne, Ne.symm hne]
  · by_cases ht' : blockCount π = t
    · simp [ht, ht']
    · simp [ht, ht', Ne.symm ht']

theorem partitionChain_Q_eq_zero_of_blockCount_eq (hne : π ≠ σ)
    (h : blockCount π = blockCount σ) : (partitionChain α).Q π σ = 0 := by
  by_contra hQ
  have h1 := card_parts_of_mem_merges (mem_merges_of_Q_ne_zero hne hQ)
  have h2 := congrArg Fin.val h
  rw [coe_blockCount, coe_blockCount] at h2
  omega

theorem partitionChain_rate (π : Finpartition (univ : Finset α)) :
    (partitionChain α).rate π = (coalRate π.parts.card : ℝ) := by
  rw [partitionChain_lumps.rate_eq fun _ _ => partitionChain_Q_eq_zero_of_blockCount_eq,
    blockChain_rate, coe_blockCount]

variable (α) in
def coalescedPartitions : Finset (Finpartition (univ : Finset α)) :=
  preimageFinset blockCount (coalesced (Fintype.card α))

theorem mem_coalescedPartitions : π ∈ coalescedPartitions α ↔ π.parts.card ≤ 1 := by
  rw [coalescedPartitions, mem_preimageFinset, mem_coalesced, coe_blockCount]

noncomputable def partitionTmrca
    (p : (ℕ → Finpartition (univ : Finset α)) × (ℕ → ℝ)) : ℝ≥0∞ :=
  (partitionChain α).timeBefore (coalescedPartitions α) p

noncomputable def partitionTreeLength
    (p : (ℕ → Finpartition (univ : Finset α)) × (ℕ → ℝ)) : ℝ≥0∞ :=
  (partitionChain α).costBefore (coalescedPartitions α) (fun π => (π.parts.card : ℝ)) p

variable (α)

theorem map_partitionTmrca :
    ((partitionChain α).jumpHoldLaw ⊥).map partitionTmrca =
      ((blockChain (Fintype.card α)).jumpHoldLaw (Fin.last (Fintype.card α))).map
        (tmrca (Fintype.card α)) := by
  have h := partitionChain_lumps.map_costBefore
    (fun _ _ => partitionChain_Q_eq_zero_of_blockCount_eq) (coalesced (Fintype.card α))
    (fun _ => 1) (⊥ : Finpartition (univ : Finset α))
  rw [blockCount_bot] at h
  exact h

theorem map_partitionTreeLength :
    ((partitionChain α).jumpHoldLaw ⊥).map partitionTreeLength =
      ((blockChain (Fintype.card α)).jumpHoldLaw (Fin.last (Fintype.card α))).map
        (treeLength (Fintype.card α)) := by
  have h := partitionChain_lumps.map_costBefore
    (fun _ _ => partitionChain_Q_eq_zero_of_blockCount_eq) (coalesced (Fintype.card α))
    (fun k => ((k : ℕ) : ℝ)) (⊥ : Finpartition (univ : Finset α))
  rw [blockCount_bot] at h
  exact h

theorem lintegral_partitionTmrca :
    ∫⁻ p, partitionTmrca p ∂(partitionChain α).jumpHoldLaw ⊥ =
      ENNReal.ofReal (expTMRCA (Fintype.card α) : ℝ) := by
  have h := partitionChain_lumps.lintegral_costBefore_preimage
    (fun _ _ => partitionChain_Q_eq_zero_of_blockCount_eq) (coalesced (Fintype.card α))
    (fun _ => 1) (⊥ : Finpartition (univ : Finset α))
  rw [blockCount_bot] at h
  exact h.trans (lintegral_tmrca (Fintype.card α))

theorem lintegral_partitionTreeLength :
    ∫⁻ p, partitionTreeLength p ∂(partitionChain α).jumpHoldLaw ⊥ =
      ENNReal.ofReal (expLength (Fintype.card α) : ℝ) := by
  have h := partitionChain_lumps.lintegral_costBefore_preimage
    (fun _ _ => partitionChain_Q_eq_zero_of_blockCount_eq) (coalesced (Fintype.card α))
    (fun k => ((k : ℕ) : ℝ)) (⊥ : Finpartition (univ : Finset α))
  rw [blockCount_bot] at h
  exact h.trans (lintegral_treeLength (Fintype.card α))

end Rhone.Coalescent
