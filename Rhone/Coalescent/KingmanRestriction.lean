/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.RateLumpingLaw
public import Rhone.Coalescent.KingmanSamplingConsistency

/-!
# Restriction of Kingman's coalescent along a map of labels

Source: kingman1982, Thm 3. -/

@[expose] public section

namespace Rhone.Coalescent

open Finset MeasureTheory MarkovChain

variable {α β γ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ]

def restrictAlongSetoid (f : α → β) (π : Finpartition (univ : Finset β)) : Setoid α where
  r := fun a b => π.part (f a) = π.part (f b)
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

instance instDecidableRelRestrictAlongSetoid (f : α → β)
    (π : Finpartition (univ : Finset β)) : DecidableRel (restrictAlongSetoid f π).r :=
  fun a b => inferInstanceAs (Decidable (π.part (f a) = π.part (f b)))

def restrictAlong (f : α → β) (π : Finpartition (univ : Finset β)) :
    Finpartition (univ : Finset α) :=
  Finpartition.ofSetoid (restrictAlongSetoid f π)

def pullBlock (f : α → β) (B : Finset β) : Finset α :=
  univ.filter fun a => f a ∈ B

def visibleParts (f : α → β) (π : Finpartition (univ : Finset β)) : Finset (Finset β) :=
  π.parts.filter fun B => (pullBlock f B).Nonempty

variable {f : α → β} {π : Finpartition (univ : Finset β)} {s : Finset (Finset β)}

omit [DecidableEq α] [Fintype β] in
theorem mem_pullBlock {B : Finset β} {a : α} : a ∈ pullBlock f B ↔ f a ∈ B := by
  simp only [pullBlock, mem_filter, mem_univ, true_and]

theorem part_restrictAlong (f : α → β) (π : Finpartition (univ : Finset β)) (a : α) :
    (restrictAlong f π).part a = pullBlock f (π.part (f a)) := by
  ext b
  rw [restrictAlong, Finpartition.mem_part_ofSetoid_iff_rel, mem_pullBlock,
    π.mem_part_iff_part_eq_part (mem_univ _) (mem_univ _)]
  exact eq_comm

omit [DecidableEq α] in
theorem visibleParts_subset (f : α → β) (π : Finpartition (univ : Finset β)) :
    visibleParts f π ⊆ π.parts :=
  filter_subset _ _

omit [DecidableEq α] in
theorem part_mem_visibleParts (f : α → β) (π : Finpartition (univ : Finset β)) (a : α) :
    π.part (f a) ∈ visibleParts f π :=
  mem_filter.2 ⟨π.part_mem.2 (mem_univ _), a, mem_pullBlock.2 (π.mem_part (mem_univ _))⟩

omit [DecidableEq α] in
theorem exists_part_eq_of_mem_visibleParts {B : Finset β} (hB : B ∈ visibleParts f π) :
    ∃ a : α, π.part (f a) = B := by
  obtain ⟨hB, a, ha⟩ := mem_filter.1 hB
  exact ⟨a, π.part_eq_of_mem hB (mem_pullBlock.1 ha)⟩

omit [DecidableEq α] in
theorem part_eq_of_pullBlock_eq {a b : α}
    (h : pullBlock f (π.part (f a)) = pullBlock f (π.part (f b))) :
    π.part (f a) = π.part (f b) := by
  have ha : a ∈ pullBlock f (π.part (f a)) := mem_pullBlock.2 (π.mem_part (mem_univ _))
  rw [h] at ha
  exact (π.mem_part_iff_part_eq_part (mem_univ _) (mem_univ _)).1 (mem_pullBlock.1 ha)

omit [DecidableEq α] in
theorem pullBlock_injOn (f : α → β) (π : Finpartition (univ : Finset β)) :
    Set.InjOn (pullBlock f) (↑(visibleParts f π) : Set (Finset β)) := by
  intro B hB B' hB' h
  rw [mem_coe] at hB hB'
  obtain ⟨a, rfl⟩ := exists_part_eq_of_mem_visibleParts hB
  obtain ⟨b, rfl⟩ := exists_part_eq_of_mem_visibleParts hB'
  exact part_eq_of_pullBlock_eq h

theorem parts_restrictAlong (f : α → β) (π : Finpartition (univ : Finset β)) :
    (restrictAlong f π).parts = (visibleParts f π).image (pullBlock f) := by
  ext B'
  constructor
  · intro hB'
    obtain ⟨a, ha⟩ := (restrictAlong f π).nonempty_of_mem_parts hB'
    rw [← (restrictAlong f π).part_eq_of_mem hB' ha, part_restrictAlong]
    exact mem_image_of_mem _ (part_mem_visibleParts f π a)
  · intro hB'
    obtain ⟨B, hB, rfl⟩ := mem_image.1 hB'
    obtain ⟨a, rfl⟩ := exists_part_eq_of_mem_visibleParts hB
    rw [← part_restrictAlong]
    exact (restrictAlong f π).part_mem.2 (mem_univ a)

omit [Fintype β] in
theorem pullBlock_sup (f : α → β) (s : Finset (Finset β)) :
    pullBlock f (s.sup id) = (s.image (pullBlock f)).sup id := by
  rw [Finset.sup_image]
  ext a
  simp only [mem_pullBlock, Finset.mem_sup, Function.comp_apply, id_eq]

theorem part_bot (x : α) : (⊥ : Finpartition (univ : Finset α)).part x = {x} :=
  Finpartition.part_eq_of_mem _ (Finpartition.mem_bot_iff.2 ⟨x, mem_univ x, rfl⟩)
    (mem_singleton_self x)

theorem restrictAlong_id (π : Finpartition (univ : Finset α)) : restrictAlong id π = π := by
  refine eq_of_part_eq fun a => ?_
  rw [part_restrictAlong]
  ext b
  exact mem_pullBlock

theorem restrictAlong_comp (f : α → β) (g : β → γ) (π : Finpartition (univ : Finset γ)) :
    restrictAlong (g ∘ f) π = restrictAlong f (restrictAlong g π) := by
  refine eq_of_part_eq fun a => ?_
  simp only [part_restrictAlong]
  ext b
  simp only [mem_pullBlock, Function.comp_apply]

theorem restrictAlong_bot {f : α → β} (hf : Function.Injective f) :
    restrictAlong f (⊥ : Finpartition (univ : Finset β)) = ⊥ := by
  refine eq_of_part_eq fun a => ?_
  rw [part_restrictAlong, part_bot, part_bot]
  ext b
  rw [mem_pullBlock, mem_singleton, mem_singleton, hf.eq_iff]

theorem restrictLast_eq_restrictAlong {n : ℕ} (π : Finpartition (univ : Finset (Fin (n + 1)))) :
    restrictLast π = restrictAlong Fin.castSucc π := by
  refine eq_of_part_eq fun a => ?_
  rw [part_restrictLast, part_restrictAlong]
  rfl

theorem restrictAlong_equiv_injective (e : α ≃ β) :
    Function.Injective (restrictAlong (e : α → β)) := by
  refine Function.LeftInverse.injective (g := restrictAlong (e.symm : β → α)) fun π => ?_
  have h : (e : α → β) ∘ (e.symm : β → α) = id := funext fun b => e.apply_symm_apply b
  rw [← restrictAlong_comp, h, restrictAlong_id]

theorem restrictAlong_mergeBlocks_of_subset (hs : s ⊆ visibleParts f π) (hne : s.Nonempty) :
    restrictAlong f (mergeBlocks π s) =
      mergeBlocks (restrictAlong f π) (s.image (pullBlock f)) := by
  have hsp : s ⊆ π.parts := hs.trans (visibleParts_subset f π)
  have hs' : s.image (pullBlock f) ⊆ (restrictAlong f π).parts := by
    rw [parts_restrictAlong]
    exact image_subset_image hs
  refine eq_of_part_eq fun a => ?_
  rw [part_restrictAlong, part_mergeBlocks hsp hne, part_mergeBlocks hs' (hne.image _),
    part_restrictAlong]
  have hiff : pullBlock f (π.part (f a)) ∈ s.image (pullBlock f) ↔ π.part (f a) ∈ s := by
    refine ⟨fun h => ?_, fun h => mem_image_of_mem _ h⟩
    obtain ⟨B, hB, hBe⟩ := mem_image.1 h
    have hBa : B = π.part (f a) := pullBlock_injOn f π (mem_coe.2 (hs hB))
      (mem_coe.2 (part_mem_visibleParts f π a)) hBe
    exact hBa ▸ hB
  by_cases h : π.part (f a) ∈ s
  · rw [ite_eq_left h, ite_eq_left (hiff.2 h), pullBlock_sup]
  · rw [ite_eq_right h, ite_eq_right (mt hiff.1 h)]

theorem restrictAlong_mergeBlocks_of_not_subset (hs : s ⊆ π.parts) (hc : s.card = 2)
    (hv : ¬s ⊆ visibleParts f π) : restrictAlong f (mergeBlocks π s) = restrictAlong f π := by
  obtain ⟨w, hws, hwv⟩ := Finset.not_subset.1 hv
  have hw : pullBlock f w = ∅ := by
    by_contra h
    exact hwv (mem_filter.2 ⟨hs hws, nonempty_iff_ne_empty.2 h⟩)
  have hne : s.Nonempty := ⟨w, hws⟩
  refine eq_of_part_eq fun a => ?_
  rw [part_restrictAlong, part_mergeBlocks hs hne, part_restrictAlong]
  split_ifs with h
  · have hPw : π.part (f a) ≠ w := fun h' => hwv (h' ▸ part_mem_visibleParts f π a)
    have key : ∀ v ∈ s, v ≠ w → v = π.part (f a) := by
      intro v hv hvw
      by_contra hvP
      have hsub : ({w, π.part (f a), v} : Finset (Finset β)) ⊆ s := by
        intro u hu
        simp only [mem_insert, mem_singleton] at hu
        rcases hu with rfl | rfl | rfl
        · exact hws
        · exact h
        · exact hv
      have h3 : ({w, π.part (f a), v} : Finset (Finset β)).card = 3 :=
        Finset.card_eq_three.2 ⟨_, _, _, Ne.symm hPw, Ne.symm hvw, Ne.symm hvP, rfl⟩
      have := card_le_card hsub
      omega
    ext b
    rw [mem_pullBlock, mem_pullBlock, Finset.mem_sup]
    constructor
    · rintro ⟨v, hv, hb⟩
      have hvw : v ≠ w := by
        rintro rfl
        have hbv : b ∈ pullBlock f v := mem_pullBlock.2 hb
        rw [hw] at hbv
        exact absurd hbv (notMem_empty b)
      rw [← key v hv hvw]
      exact hb
    · intro hb
      exact ⟨_, h, hb⟩
  · rfl

/-- Source: kingman1982, Thm 3. -/
theorem partitionChain_lumps_restrictAlong (f : α → β) :
    (partitionChain β).Lumps (restrictAlong f) (partitionChain α) := by
  intro π σ
  rw [partitionChain_Q, partitionChain_Q, partitionQ_eq_sum (restrictAlong f π) σ]
  have h1 : ∑ ρ with restrictAlong f ρ = σ, partitionQ π ρ =
      ∑ s ∈ powersetCard 2 π.parts,
        ((if restrictAlong f (mergeBlocks π s) = σ then (1 : ℝ) else 0) -
          if σ = restrictAlong f π then 1 else 0) := by
    simp only [partitionQ_eq_sum π]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq']
    simp only [mem_filter, mem_univ, true_and]
    exact congrArg₂ _ rfl (if_congr eq_comm rfl rfl)
  rw [h1]
  refine (Finset.sum_subset (powersetCard_mono (visibleParts_subset f π))
    fun s hs hs' => ?_).symm.trans ?_
  · rw [mem_powersetCard] at hs hs'
    have hv : ¬s ⊆ visibleParts f π := fun h => hs' ⟨h, hs.2⟩
    rw [restrictAlong_mergeBlocks_of_not_subset hs.1 hs.2 hv]
    exact sub_eq_zero.2 (if_congr eq_comm rfl rfl)
  · refine Finset.sum_bij (fun s _ => s.image (pullBlock f)) ?_ ?_ ?_ ?_
    · intro s hs
      rw [mem_powersetCard] at hs ⊢
      refine ⟨?_, ?_⟩
      · rw [parts_restrictAlong]
        exact image_subset_image hs.1
      · rw [card_image_of_injOn ((pullBlock_injOn f π).mono (coe_subset.2 hs.1)), hs.2]
    · have key : ∀ s t : Finset (Finset β), s ⊆ visibleParts f π →
          t ⊆ visibleParts f π → s.image (pullBlock f) = t.image (pullBlock f) →
          s ⊆ t := by
        intro s t hs ht hst B hB
        have hBt : pullBlock f B ∈ t.image (pullBlock f) := hst ▸ mem_image_of_mem _ hB
        obtain ⟨B', hB', hBe⟩ := mem_image.1 hBt
        exact pullBlock_injOn f π (mem_coe.2 (ht hB')) (mem_coe.2 (hs hB)) hBe ▸ hB'
      intro s hs t ht hst
      rw [mem_powersetCard] at hs ht
      exact Finset.Subset.antisymm (key s t hs.1 ht.1 hst) (key t s ht.1 hs.1 hst.symm)
    · intro s' hs'
      rw [mem_powersetCard, parts_restrictAlong] at hs'
      obtain ⟨s, hs, rfl⟩ := Finset.subset_image_iff.1 hs'.1
      refine ⟨s, mem_powersetCard.2 ⟨hs, ?_⟩, rfl⟩
      rw [← card_image_of_injOn ((pullBlock_injOn f π).mono (coe_subset.2 hs)), hs'.2]
    · intro s hs
      rw [mem_powersetCard] at hs
      have hne : s.Nonempty := card_pos.1 (by omega)
      rw [restrictAlong_mergeBlocks_of_subset hs.1 hne]

/-- Source: kingman1982, Thm 3. -/
theorem partitionChain_semigroup_restrictAlong (f : α → β) (t : ℝ)
    (π : Finpartition (univ : Finset β)) (σ : Finpartition (univ : Finset α)) :
    ∑ ρ with restrictAlong f ρ = σ, (partitionChain β).semigroup t π ρ =
      (partitionChain α).semigroup t (restrictAlong f π) σ :=
  (partitionChain_lumps_restrictAlong f).sum_semigroup_fibre t π σ

theorem partitionChain_semigroup_relabel (e : α ≃ β) (t : ℝ)
    (π ρ : Finpartition (univ : Finset β)) :
    (partitionChain β).semigroup t π ρ =
      (partitionChain α).semigroup t (restrictAlong e π) (restrictAlong e ρ) :=
  (partitionChain_lumps_restrictAlong (e : α → β)).semigroup_apply_of_injective
    (restrictAlong_equiv_injective e) t π ρ

theorem map_partitionChain_law_restrictAlong (f : α → β) {t : ℝ} (ht : 0 ≤ t)
    (π : Finpartition (univ : Finset β)) :
    (((partitionChain β).semigroupChain t ht).kernel π).map (restrictAlong f) =
      ((partitionChain α).semigroupChain t ht).kernel (restrictAlong f π) :=
  (partitionChain_lumps_restrictAlong f).map_semigroupChain_kernel t ht π

/-- Source: kingman1982, Thm 3. -/
theorem map_partitionChain_law_bot {f : α → β} (hf : Function.Injective f) {t : ℝ}
    (ht : 0 ≤ t) :
    (((partitionChain β).semigroupChain t ht).kernel ⊥).map (restrictAlong f) =
      ((partitionChain α).semigroupChain t ht).kernel ⊥ := by
  have h := map_partitionChain_law_restrictAlong f ht ⊥
  rwa [restrictAlong_bot hf] at h

/-- Source: kingman1982, Thm 3. -/
theorem map_partitionChain_law_restrictLast (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (((partitionChain (Fin (n + 1))).semigroupChain t ht).kernel ⊥).map restrictLast =
      ((partitionChain (Fin n)).semigroupChain t ht).kernel ⊥ := by
  have h : (restrictLast : Finpartition (univ : Finset (Fin (n + 1))) → _) =
      restrictAlong Fin.castSucc := funext restrictLast_eq_restrictAlong
  rw [h]
  exact map_partitionChain_law_bot (Fin.castSucc_injective n) ht

theorem map_partitionChain_skeleton_bot {f : α → β} (hf : Function.Injective f) {t : ℝ}
    (ht : 0 ≤ t) :
    (((partitionChain β).semigroupChain t ht).pathLaw ⊥).map
        (fun ω k => restrictAlong f (ω k)) =
      ((partitionChain α).semigroupChain t ht).pathLaw ⊥ := by
  have h := (partitionChain_lumps_restrictAlong f).map_semigroupChain_pathLaw t ht ⊥
  rwa [restrictAlong_bot hf] at h

end Rhone.Coalescent
