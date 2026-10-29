/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.LambdaBlockChain
public import Rhone.Coalescent.KingmanSamplingConsistency

/-! # The Λ-coalescent on the partitions of a finite sample -/

@[expose] public section

namespace Rhone.Coalescent

open MeasureTheory Set Finset MarkovChain

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem sup_notMem_parts_of_two_le {π : Finpartition (univ : Finset α)}
    {s : Finset (Finset α)} (hs : s ⊆ π.parts) (hc : 2 ≤ s.card) : s.sup id ∉ π.parts := by
  intro hmem
  have key : ∀ a ∈ s, a = s.sup id := by
    intro a ha
    by_contra hne
    have hd : Disjoint (s.sup id) a := π.disjoint hmem (hs ha) (Ne.symm hne)
    exact π.ne_bot (hs ha) (hd.eq_bot_of_ge (Finset.le_sup (f := id) ha))
  obtain ⟨a, ha, c, hc', hac⟩ := Finset.one_lt_card.1 hc
  exact hac ((key a ha).trans (key c hc').symm)

theorem card_parts_mergeBlocks_add {π : Finpartition (univ : Finset α)}
    {s : Finset (Finset α)} (hs : s ⊆ π.parts) (hc : 2 ≤ s.card) :
    (mergeBlocks π s).parts.card + s.card = π.parts.card + 1 := by
  have hne : s.Nonempty := card_pos.1 (by omega)
  have hx : s.sup id ∉ π.parts \ s := fun h => sup_notMem_parts_of_two_le hs hc (mem_sdiff.1 h).1
  have hle : s.card ≤ π.parts.card := card_le_card hs
  rw [parts_mergeBlocks hs hne, card_insert_of_notMem hx, card_sdiff_of_subset hs]
  omega

def mergeSets (π : Finpartition (univ : Finset α)) : Finset (Finset (Finset α)) :=
  π.parts.powerset.filter fun s => 2 ≤ s.card

theorem mem_mergeSets {π : Finpartition (univ : Finset α)} {s : Finset (Finset α)} :
    s ∈ mergeSets π ↔ s ⊆ π.parts ∧ 2 ≤ s.card := by
  simp [mergeSets]

theorem sum_mergeSets_card (π : Finpartition (univ : Finset α)) (g : ℕ → ℝ) :
    ∑ s ∈ mergeSets π, g s.card =
      ∑ k ∈ Finset.Icc 2 π.parts.card, (π.parts.card.choose k : ℝ) * g k := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := Finset.card) (t := Finset.Icc 2 π.parts.card)
    (fun s hs => by
      obtain ⟨h1, h2⟩ := mem_mergeSets.1 hs
      exact Finset.mem_Icc.2 ⟨h2, card_le_card h1⟩)]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hset : (mergeSets π).filter (fun s => s.card = k) = powersetCard k π.parts := by
    ext s
    rw [mem_filter, mem_mergeSets, mem_powersetCard]
    have := (Finset.mem_Icc.1 hk).1
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      exact ⟨⟨h1, by omega⟩, h3⟩
  rw [Finset.sum_congr rfl (fun s hs => by rw [(mem_filter.1 hs).2]), hset, sum_const,
    card_powersetCard]
  simp

variable (Λ : Measure ℝ)

noncomputable def lambdaPartitionRate (π : Finpartition (univ : Finset α)) : ℝ :=
  ∑ s ∈ mergeSets π, lambdaRate Λ π.parts.card s.card

theorem lambdaPartitionRate_eq (π : Finpartition (univ : Finset α)) :
    lambdaPartitionRate Λ π = lambdaTotalRate Λ π.parts.card := by
  rw [lambdaPartitionRate, sum_mergeSets_card π (fun k => lambdaRate Λ π.parts.card k)]
  rfl

noncomputable def lambdaPartitionQ :
    Matrix (Finpartition (univ : Finset α)) (Finpartition (univ : Finset α)) ℝ := fun π σ =>
  (∑ s ∈ mergeSets π, if mergeBlocks π s = σ then lambdaRate Λ π.parts.card s.card else 0)
    - if σ = π then lambdaPartitionRate Λ π else 0

variable (α) in
noncomputable def lambdaPartitionChain : RateChain (Finpartition (univ : Finset α)) where
  Q := lambdaPartitionQ Λ
  off_diag_nonneg π σ h := by
    unfold lambdaPartitionQ
    rw [ite_eq_right (Ne.symm h), sub_zero]
    refine Finset.sum_nonneg fun s _ => ?_
    split_ifs
    · exact lambdaRate_nonneg _ _
    · exact le_rfl
  row_sum π := by
    unfold lambdaPartitionQ
    rw [Finset.sum_sub_distrib, Finset.sum_comm]
    simp [lambdaPartitionRate]

theorem lambdaPartitionChain_Q : (lambdaPartitionChain α Λ).Q = lambdaPartitionQ Λ := rfl

theorem sum_mergeSets_dirac_zero (π : Finpartition (univ : Finset α))
    (f : Finset (Finset α) → ℝ) :
    ∑ s ∈ mergeSets π, f s * lambdaRate (Measure.dirac 0) π.parts.card s.card =
      ∑ s ∈ powersetCard 2 π.parts, f s := by
  have h : ∀ s ∈ mergeSets π, f s * lambdaRate (Measure.dirac 0) π.parts.card s.card =
      if s.card = 2 then f s else 0 := by
    intro s hs
    have h2 := (mem_mergeSets.1 hs).2
    rw [lambdaRate_dirac_zero]
    by_cases hc : s.card = 2
    · rw [ite_eq_left hc, hc]
      simp
    · rw [ite_eq_right hc, zero_pow (by omega)]
      simp
  rw [Finset.sum_congr rfl h, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext s
  rw [mem_filter, mem_mergeSets, mem_powersetCard]
  constructor
  · rintro ⟨⟨h1, _⟩, h3⟩
    exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩
    exact ⟨⟨h1, by omega⟩, h3⟩

theorem lambdaPartitionQ_dirac_zero :
    lambdaPartitionQ (Measure.dirac 0) = (partitionQ : Matrix (Finpartition (univ : Finset α))
      (Finpartition (univ : Finset α)) ℝ) := by
  ext π σ
  rw [partitionQ_eq_sum]
  unfold lambdaPartitionQ lambdaPartitionRate
  have h1 := sum_mergeSets_dirac_zero π (fun s => if mergeBlocks π s = σ then (1 : ℝ) else 0)
  have h2 := sum_mergeSets_dirac_zero π (fun _ => (1 : ℝ))
  simp only [ite_mul, one_mul, zero_mul] at h1 h2
  rw [Finset.sum_sub_distrib, h1, h2]
  simp only [sum_const, card_powersetCard, nsmul_eq_mul, mul_one]
  split_ifs <;> simp

theorem lambdaPartitionChain_dirac_zero :
    (lambdaPartitionChain α (Measure.dirac 0)).Q = (partitionChain α).Q :=
  lambdaPartitionQ_dirac_zero

theorem blockCount_mergeBlocks_eq_iff {π : Finpartition (univ : Finset α)}
    {s : Finset (Finset α)} (hs : s ∈ mergeSets π) (t : Fin (Fintype.card α + 1)) :
    blockCount (mergeBlocks π s) = t ↔ π.parts.card + 1 = (t : ℕ) + s.card := by
  obtain ⟨h1, h2⟩ := mem_mergeSets.1 hs
  have := card_parts_mergeBlocks_add h1 h2
  rw [Fin.ext_iff, coe_blockCount]
  omega

theorem lambdaPartitionChain_lumps :
    (lambdaPartitionChain α Λ).Lumps blockCount (lambdaBlockChain Λ (Fintype.card α)) := by
  intro π t
  rw [lambdaPartitionChain_Q, lambdaBlockChain_Q]
  unfold lambdaPartitionQ lambdaBlockQ
  have hb : π.parts.card ≤ Fintype.card α := by simpa using π.card_parts_le_card
  rw [Finset.sum_sub_distrib]
  have hA : ∑ σ with blockCount σ = t,
      (∑ s ∈ mergeSets π, if mergeBlocks π s = σ then lambdaRate Λ π.parts.card s.card else 0) =
      ∑ s ∈ mergeSets π, if π.parts.card + 1 = (t : ℕ) + s.card then
        lambdaRate Λ π.parts.card s.card else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [Finset.sum_ite_eq]
    simp only [mem_filter]
    exact if_congr ((and_iff_right (Finset.mem_univ _)).trans
      (blockCount_mergeBlocks_eq_iff hs t)) rfl rfl
  have hB : ∑ σ with blockCount σ = t, (if σ = π then lambdaPartitionRate Λ π else 0) =
      if blockCount π = t then lambdaPartitionRate Λ π else 0 := by
    rw [Finset.sum_ite_eq']
    simp
  rw [hA, hB, sum_mergeSets_card π
    (fun k => if π.parts.card + 1 = (t : ℕ) + k then lambdaRate Λ π.parts.card k else 0),
    coe_blockCount, sum_lambdaMergeRate Λ _ hb, lambdaPartitionRate_eq]
  have hiff : blockCount π = t ↔ t = (⟨π.parts.card, by omega⟩ : Fin (Fintype.card α + 1)) := by
    rw [Fin.ext_iff, Fin.ext_iff, coe_blockCount]
    exact ⟨Eq.symm, Eq.symm⟩
  refine congrArg₂ _ ?_ ?_
  · unfold lambdaMergeRate
    by_cases ht : 1 ≤ (t : ℕ) ∧ (t : ℕ) < π.parts.card
    · rw [ite_eq_left ht]
      rw [Finset.sum_eq_single_of_mem (π.parts.card - (t : ℕ) + 1)]
      · rw [ite_eq_left (by omega)]
      · rw [Finset.mem_Icc]
        omega
      · intro k hk hne
        rw [Finset.mem_Icc] at hk
        rw [ite_eq_right (by omega), mul_zero]
    · rw [ite_eq_right ht]
      refine Finset.sum_eq_zero fun k hk => ?_
      rw [Finset.mem_Icc] at hk
      rw [ite_eq_right (by omega), mul_zero]
  · exact if_congr hiff rfl rfl

end Rhone.Coalescent
