/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.KingmanPartition

/-!
# Sampling consistency of Kingman's coalescent

Source: kingman1982, Thm 3. -/

@[expose] public section

namespace Rhone.Coalescent

open Finset MeasureTheory MarkovChain
open scoped ENNReal

section General

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {π ρ : Finpartition (univ : Finset α)} {s : Finset (Finset α)}

theorem eq_of_part_eq (h : ∀ a, π.part a = ρ.part a) : π = ρ := by
  have key : ∀ {π ρ : Finpartition (univ : Finset α)}, (∀ a, π.part a = ρ.part a) →
      π.parts ⊆ ρ.parts := by
    intro π ρ h t ht
    obtain ⟨a, ha⟩ := π.nonempty_of_mem_parts ht
    rw [← π.part_eq_of_mem ht ha, h a]
    exact ρ.part_mem.2 (mem_univ a)
  exact Finpartition.ext (Finset.Subset.antisymm (key h) (key fun a => (h a).symm))

theorem part_mergeBlocks (hs : s ⊆ π.parts) (hne : s.Nonempty) (a : α) :
    (mergeBlocks π s).part a = if π.part a ∈ s then s.sup id else π.part a := by
  refine Finpartition.part_eq_of_mem _ ?_ ?_
  · rw [parts_mergeBlocks hs hne]
    split_ifs with h
    · exact mem_insert_self _ _
    · exact mem_insert_of_mem (mem_sdiff.2 ⟨π.part_mem.2 (mem_univ a), h⟩)
  · split_ifs with h
    · exact Finset.mem_sup.2 ⟨π.part a, h, π.mem_part (mem_univ a)⟩
    · exact π.mem_part (mem_univ a)

theorem mergeBlocks_injOn (π : Finpartition (univ : Finset α)) :
    Set.InjOn (mergeBlocks π) (↑(powersetCard 2 π.parts) : Set (Finset (Finset α))) := by
  intro s hs t ht hst
  rw [mem_coe, mem_powersetCard] at hs ht
  rw [← parts_sdiff_parts_mergeBlocks hs.1 hs.2, ← parts_sdiff_parts_mergeBlocks ht.1 ht.2]
  exact congrArg (fun ρ : Finpartition (univ : Finset α) => π.parts \ ρ.parts) hst

theorem partitionQ_eq_sum (π ρ : Finpartition (univ : Finset α)) :
    partitionQ π ρ = ∑ s ∈ powersetCard 2 π.parts,
      ((if mergeBlocks π s = ρ then (1 : ℝ) else 0) - if ρ = π then 1 else 0) := by
  have h1 : ∑ s ∈ powersetCard 2 π.parts, (if mergeBlocks π s = ρ then (1 : ℝ) else 0) =
      if ρ ∈ merges π then 1 else 0 :=
    (Finset.sum_image (f := fun τ => if τ = ρ then (1 : ℝ) else 0)
      (mergeBlocks_injOn π)).symm.trans (Finset.sum_ite_eq' _ _ _)
  have h2 : ∑ _s ∈ powersetCard 2 π.parts, (if ρ = π then (1 : ℝ) else 0) =
      if ρ = π then (coalRate π.parts.card : ℝ) else 0 := by
    rw [Finset.sum_const, card_powersetCard, coalRate_cast_eq_choose]
    split_ifs <;> simp
  rw [Finset.sum_sub_distrib, h1, h2]
  rfl

end General

def restrictSetoid {n : ℕ} (π : Finpartition (univ : Finset (Fin (n + 1)))) : Setoid (Fin n) where
  r := fun a b => π.part (Fin.castSucc a) = π.part (Fin.castSucc b)
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

instance instDecidableRelRestrictSetoid {n : ℕ}
    (π : Finpartition (univ : Finset (Fin (n + 1)))) : DecidableRel (restrictSetoid π).r :=
  fun a b => inferInstanceAs (Decidable (π.part (Fin.castSucc a) = π.part (Fin.castSucc b)))

def restrictLast {n : ℕ} (π : Finpartition (univ : Finset (Fin (n + 1)))) :
    Finpartition (univ : Finset (Fin n)) :=
  Finpartition.ofSetoid (restrictSetoid π)

def restrictBlock {n : ℕ} (B : Finset (Fin (n + 1))) : Finset (Fin n) :=
  univ.filter fun a => Fin.castSucc a ∈ B

variable {n : ℕ} {π : Finpartition (univ : Finset (Fin (n + 1)))}
  {s : Finset (Finset (Fin (n + 1)))}

theorem mem_restrictBlock {B : Finset (Fin (n + 1))} {a : Fin n} :
    a ∈ restrictBlock B ↔ Fin.castSucc a ∈ B := by
  simp only [restrictBlock, mem_filter, mem_univ, true_and]

theorem part_restrictLast (π : Finpartition (univ : Finset (Fin (n + 1)))) (a : Fin n) :
    (restrictLast π).part a = restrictBlock (π.part (Fin.castSucc a)) := by
  ext b
  rw [restrictLast, Finpartition.mem_part_ofSetoid_iff_rel, mem_restrictBlock,
    π.mem_part_iff_part_eq_part (mem_univ _) (mem_univ _)]
  exact eq_comm

theorem part_castSucc_ne_singleton_last (π : Finpartition (univ : Finset (Fin (n + 1))))
    (a : Fin n) : π.part (Fin.castSucc a) ≠ {Fin.last n} := by
  intro h
  have ha := π.mem_part (mem_univ (Fin.castSucc a))
  rw [h, mem_singleton] at ha
  exact Fin.castSucc_ne_last a ha

theorem exists_part_castSucc_eq {B : Finset (Fin (n + 1))} (hB : B ∈ π.parts)
    (hL : B ≠ {Fin.last n}) : ∃ a : Fin n, π.part (Fin.castSucc a) = B := by
  have hx : ∃ x ∈ B, x ≠ Fin.last n := by
    by_contra hcon
    push Not at hcon
    exact hL (Finset.eq_singleton_iff_nonempty_unique_mem.2 ⟨π.nonempty_of_mem_parts hB, hcon⟩)
  obtain ⟨x, hxB, hxl⟩ := hx
  obtain ⟨a, rfl⟩ := Fin.exists_castSucc_eq.2 hxl
  exact ⟨a, π.part_eq_of_mem hB hxB⟩

theorem part_castSucc_eq_of_restrictBlock_eq {a b : Fin n}
    (h : restrictBlock (π.part (Fin.castSucc a)) = restrictBlock (π.part (Fin.castSucc b))) :
    π.part (Fin.castSucc a) = π.part (Fin.castSucc b) := by
  have ha : a ∈ restrictBlock (π.part (Fin.castSucc a)) :=
    mem_restrictBlock.2 (π.mem_part (mem_univ _))
  rw [h] at ha
  exact (π.mem_part_iff_part_eq_part (mem_univ _) (mem_univ _)).1 (mem_restrictBlock.1 ha)

theorem restrictBlock_injOn (π : Finpartition (univ : Finset (Fin (n + 1)))) :
    Set.InjOn restrictBlock
      (↑(π.parts.erase {Fin.last n}) : Set (Finset (Fin (n + 1)))) := by
  intro B hB B' hB' h
  rw [mem_coe, mem_erase] at hB hB'
  obtain ⟨a, rfl⟩ := exists_part_castSucc_eq hB.2 hB.1
  obtain ⟨b, rfl⟩ := exists_part_castSucc_eq hB'.2 hB'.1
  exact part_castSucc_eq_of_restrictBlock_eq h

theorem parts_restrictLast (π : Finpartition (univ : Finset (Fin (n + 1)))) :
    (restrictLast π).parts = (π.parts.erase {Fin.last n}).image restrictBlock := by
  ext B'
  constructor
  · intro hB'
    obtain ⟨a, ha⟩ := (restrictLast π).nonempty_of_mem_parts hB'
    rw [← (restrictLast π).part_eq_of_mem hB' ha, part_restrictLast]
    exact mem_image_of_mem _
      (mem_erase.2 ⟨part_castSucc_ne_singleton_last π a, π.part_mem.2 (mem_univ _)⟩)
  · intro hB'
    obtain ⟨B, hB, rfl⟩ := mem_image.1 hB'
    rw [mem_erase] at hB
    obtain ⟨a, rfl⟩ := exists_part_castSucc_eq hB.2 hB.1
    rw [← part_restrictLast]
    exact (restrictLast π).part_mem.2 (mem_univ a)

theorem restrictBlock_sup (s : Finset (Finset (Fin (n + 1)))) :
    restrictBlock (s.sup id) = (s.image restrictBlock).sup id := by
  rw [Finset.sup_image]
  ext a
  simp only [mem_restrictBlock, Finset.mem_sup, Function.comp_apply, id_eq]

theorem restrictLast_bot (n : ℕ) :
    restrictLast (⊥ : Finpartition (univ : Finset (Fin (n + 1)))) = ⊥ := by
  have hbot : ∀ {m : ℕ} (x : Fin m), (⊥ : Finpartition (univ : Finset (Fin m))).part x = {x} :=
    fun x => Finpartition.part_eq_of_mem _
      (Finpartition.mem_bot_iff.2 ⟨x, mem_univ x, rfl⟩) (mem_singleton_self x)
  refine eq_of_part_eq fun a => ?_
  rw [part_restrictLast, hbot, hbot]
  ext b
  rw [mem_restrictBlock, mem_singleton, mem_singleton, Fin.castSucc_inj]

theorem restrictLast_mergeBlocks_of_notMem (hs : s ⊆ π.parts) (hne : s.Nonempty)
    (hL : {Fin.last n} ∉ s) :
    restrictLast (mergeBlocks π s) = mergeBlocks (restrictLast π) (s.image restrictBlock) := by
  have hse : s ⊆ π.parts.erase {Fin.last n} := fun B hB =>
    mem_erase.2 ⟨fun h => hL (h ▸ hB), hs hB⟩
  have hs' : s.image restrictBlock ⊆ (restrictLast π).parts := by
    rw [parts_restrictLast]
    exact image_subset_image hse
  refine eq_of_part_eq fun a => ?_
  rw [part_restrictLast, part_mergeBlocks hs hne, part_mergeBlocks hs' (hne.image _),
    part_restrictLast]
  have hiff : restrictBlock (π.part (Fin.castSucc a)) ∈ s.image restrictBlock ↔
      π.part (Fin.castSucc a) ∈ s := by
    refine ⟨fun h => ?_, fun h => mem_image_of_mem _ h⟩
    obtain ⟨B, hB, hBe⟩ := mem_image.1 h
    have hBa : B = π.part (Fin.castSucc a) := restrictBlock_injOn π (mem_coe.2 (hse hB))
      (mem_coe.2 (mem_erase.2 ⟨part_castSucc_ne_singleton_last π a,
        π.part_mem.2 (mem_univ _)⟩)) hBe
    exact hBa ▸ hB
  by_cases h : π.part (Fin.castSucc a) ∈ s
  · rw [ite_eq_left h, ite_eq_left (hiff.2 h), restrictBlock_sup]
  · rw [ite_eq_right h, ite_eq_right (mt hiff.1 h)]

theorem restrictLast_mergeBlocks_of_mem (hs : s ⊆ π.parts) (hc : s.card = 2)
    (hL : {Fin.last n} ∈ s) : restrictLast (mergeBlocks π s) = restrictLast π := by
  have hne : s.Nonempty := ⟨_, hL⟩
  refine eq_of_part_eq fun a => ?_
  rw [part_restrictLast, part_mergeBlocks hs hne, part_restrictLast]
  split_ifs with h
  · have key : ∀ v ∈ s, v ≠ {Fin.last n} → v = π.part (Fin.castSucc a) := by
      intro v hv hvL
      by_contra hvP
      have hsub : ({{Fin.last n}, π.part (Fin.castSucc a), v} :
          Finset (Finset (Fin (n + 1)))) ⊆ s := by
        intro w hw
        simp only [mem_insert, mem_singleton] at hw
        rcases hw with rfl | rfl | rfl
        · exact hL
        · exact h
        · exact hv
      have h3 : ({{Fin.last n}, π.part (Fin.castSucc a), v} :
          Finset (Finset (Fin (n + 1)))).card = 3 :=
        Finset.card_eq_three.2 ⟨_, _, _, (part_castSucc_ne_singleton_last π a).symm,
          Ne.symm hvL, Ne.symm hvP, rfl⟩
      have := card_le_card hsub
      omega
    ext b
    rw [mem_restrictBlock, mem_restrictBlock, Finset.mem_sup]
    constructor
    · rintro ⟨v, hv, hb⟩
      have hvL : v ≠ {Fin.last n} := by
        rintro rfl
        exact Fin.castSucc_ne_last b (mem_singleton.1 hb)
      rw [← key v hv hvL]
      exact hb
    · intro hb
      exact ⟨_, h, hb⟩
  · rfl

/-- Source: kingman1982, Thm 3, eq. (2.7). -/
theorem partitionChain_lumps_restrictLast (n : ℕ) :
    (partitionChain (Fin (n + 1))).Lumps restrictLast (partitionChain (Fin n)) := by
  intro π σ
  rw [partitionChain_Q, partitionChain_Q, partitionQ_eq_sum (restrictLast π) σ]
  have h1 : ∑ ρ with restrictLast ρ = σ, partitionQ π ρ =
      ∑ s ∈ powersetCard 2 π.parts,
        ((if restrictLast (mergeBlocks π s) = σ then (1 : ℝ) else 0) -
          if σ = restrictLast π then 1 else 0) := by
    simp only [partitionQ_eq_sum π]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq']
    simp only [mem_filter, mem_univ, true_and]
    exact congrArg₂ _ rfl (if_congr eq_comm rfl rfl)
  rw [h1]
  refine (Finset.sum_subset (powersetCard_mono (erase_subset {Fin.last n} π.parts))
    fun s hs hs' => ?_).symm.trans ?_
  · rw [mem_powersetCard] at hs hs'
    have hL : {Fin.last n} ∈ s := by
      by_contra hL
      exact hs' ⟨fun B hB => mem_erase.2 ⟨fun h => hL (h ▸ hB), hs.1 hB⟩, hs.2⟩
    rw [restrictLast_mergeBlocks_of_mem hs.1 hs.2 hL]
    exact sub_eq_zero.2 (if_congr eq_comm rfl rfl)
  · refine Finset.sum_bij (fun s _ => s.image restrictBlock) ?_ ?_ ?_ ?_
    · intro s hs
      rw [mem_powersetCard] at hs ⊢
      refine ⟨?_, ?_⟩
      · rw [parts_restrictLast]
        exact image_subset_image hs.1
      · rw [card_image_of_injOn ((restrictBlock_injOn π).mono (coe_subset.2 hs.1)), hs.2]
    · have key : ∀ s t : Finset (Finset (Fin (n + 1))), s ⊆ π.parts.erase {Fin.last n} →
          t ⊆ π.parts.erase {Fin.last n} → s.image restrictBlock = t.image restrictBlock →
          s ⊆ t := by
        intro s t hs ht hst B hB
        have hBt : restrictBlock B ∈ t.image restrictBlock := hst ▸ mem_image_of_mem _ hB
        obtain ⟨B', hB', hBe⟩ := mem_image.1 hBt
        exact restrictBlock_injOn π (mem_coe.2 (ht hB')) (mem_coe.2 (hs hB)) hBe ▸ hB'
      intro s hs t ht hst
      rw [mem_powersetCard] at hs ht
      exact Finset.Subset.antisymm (key s t hs.1 ht.1 hst) (key t s ht.1 hs.1 hst.symm)
    · intro s' hs'
      rw [mem_powersetCard, parts_restrictLast] at hs'
      obtain ⟨s, hs, rfl⟩ := Finset.subset_image_iff.1 hs'.1
      refine ⟨s, mem_powersetCard.2 ⟨hs, ?_⟩, rfl⟩
      rw [← card_image_of_injOn ((restrictBlock_injOn π).mono (coe_subset.2 hs)), hs'.2]
    · intro s hs
      rw [mem_powersetCard] at hs
      have hne : s.Nonempty := card_pos.1 (by omega)
      have hL : {Fin.last n} ∉ s := fun h => (mem_erase.1 (hs.1 h)).1 rfl
      rw [restrictLast_mergeBlocks_of_notMem (fun B hB => (mem_erase.1 (hs.1 hB)).2) hne hL]

/-- Source: kingman1982, Thm 3, eq. (2.7). -/
theorem partitionChain_semigroup_restrictLast (n : ℕ) (t : ℝ)
    (π : Finpartition (univ : Finset (Fin (n + 1))))
    (σ : Finpartition (univ : Finset (Fin n))) :
    ∑ ρ with restrictLast ρ = σ, (partitionChain (Fin (n + 1))).semigroup t π ρ =
      (partitionChain (Fin n)).semigroup t (restrictLast π) σ :=
  (partitionChain_lumps_restrictLast n).sum_semigroup_fibre t π σ

end Rhone.Coalescent
