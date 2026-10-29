/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SeedBankPair
public import Rhone.Coalescent.KingmanRestriction
public import Rhone.MarkovChain.FiniteDimLaw

/-!
# The seed-bank coalescent: restriction of the label set

Source: blath_etal2016, Remark 3.3. -/

@[expose] public section

namespace Rhone.Coalescent.SeedBank

open Finset MeasureTheory MarkovChain

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

def restrict (f : α → β) (x : Marked β) : Marked α where
  partition := restrictAlong f x.partition
  dormant := fun a => x.dormant (f a)
  dormant_eq' := by
    intro B hB a ha b hb
    rw [parts_restrictAlong] at hB
    obtain ⟨B', hB', rfl⟩ := mem_image.1 hB
    exact x.dormant_eq (visibleParts_subset f x.partition hB') (mem_pullBlock.1 ha)
      (mem_pullBlock.1 hb)

variable {f : α → β} {x : Marked β} {B : Finset β} {s : Finset (Finset β)}

private theorem partsWith_restrict (f : α → β) (x : Marked β) (b : Bool) :
    ((restrict f x).partition.parts.filter fun B => ∀ a ∈ B, (restrict f x).dormant a = b) =
      ((x.partition.parts.filter fun B => ∀ a ∈ B, x.dormant a = b).filter
        fun B => (pullBlock f B).Nonempty).image (pullBlock f) := by
  ext B'
  simp only [mem_filter, mem_image]
  constructor
  · rintro ⟨hB', hd⟩
    change B' ∈ (restrictAlong f x.partition).parts at hB'
    rw [parts_restrictAlong] at hB'
    obtain ⟨B, hBV, rfl⟩ := mem_image.1 hB'
    obtain ⟨hB, a₀, ha₀⟩ := mem_filter.1 hBV
    refine ⟨B, ⟨⟨hB, fun a ha => ?_⟩, a₀, ha₀⟩, rfl⟩
    exact (x.dormant_eq hB ha (mem_pullBlock.1 ha₀)).trans (hd a₀ ha₀)
  · rintro ⟨B, ⟨⟨hB, hd⟩, hne⟩, rfl⟩
    refine ⟨?_, fun a ha => hd (f a) (mem_pullBlock.1 ha)⟩
    change pullBlock f B ∈ (restrictAlong f x.partition).parts
    rw [parts_restrictAlong]
    exact mem_image_of_mem _ (mem_filter.2 ⟨hB, hne⟩)

theorem activeParts_restrict (f : α → β) (x : Marked β) :
    activeParts (restrict f x) =
      ((activeParts x).filter fun B => (pullBlock f B).Nonempty).image (pullBlock f) :=
  partsWith_restrict f x false

theorem dormantParts_restrict (f : α → β) (x : Marked β) :
    dormantParts (restrict f x) =
      ((dormantParts x).filter fun B => (pullBlock f B).Nonempty).image (pullBlock f) :=
  partsWith_restrict f x true

theorem restrict_flipBlock_of_nonempty (hB : B ∈ x.partition.parts)
    (hne : (pullBlock f B).Nonempty) :
    restrict f (flipBlock x B) = flipBlock (restrict f x) (pullBlock f B) := by
  have hB' : pullBlock f B ∈ (restrict f x).partition.parts := by
    change pullBlock f B ∈ (restrictAlong f x.partition).parts
    rw [parts_restrictAlong]
    exact mem_image_of_mem _ (mem_filter.2 ⟨hB, hne⟩)
  refine Marked.ext ?_ (funext fun a => ?_)
  · change restrictAlong f (flipBlock x B).partition = _
    rw [flipBlock_partition, flipBlock_partition]
    rfl
  · change (flipBlock x B).dormant (f a) = _
    rw [flipBlock_dormant hB, flipBlock_dormant hB']
    simp only [mem_pullBlock]
    rfl

theorem restrict_flipBlock_of_not_nonempty (hB : B ∈ x.partition.parts)
    (hne : ¬(pullBlock f B).Nonempty) : restrict f (flipBlock x B) = restrict f x := by
  refine Marked.ext ?_ (funext fun a => ?_)
  · change restrictAlong f (flipBlock x B).partition = _
    rw [flipBlock_partition]
    rfl
  · change (flipBlock x B).dormant (f a) = x.dormant (f a)
    have ha : f a ∉ B := fun h => hne ⟨a, mem_pullBlock.2 h⟩
    rw [flipBlock_dormant hB, ite_eq_right ha]

theorem restrict_mergeActive_of_visible (hs : s ∈ powersetCard 2 (activeParts x))
    (hv : ∀ B ∈ s, (pullBlock f B).Nonempty) :
    restrict f (mergeActive x s) = mergeActive (restrict f x) (s.image (pullBlock f)) := by
  rw [mem_powersetCard] at hs
  have hne : s.Nonempty := card_pos.1 (by omega)
  have hs' : s ⊆ visibleParts f x.partition := fun B hB =>
    mem_filter.2 ⟨activeParts_subset x (hs.1 hB), hv B hB⟩
  have himg : s.image (pullBlock f) ⊆ activeParts (restrict f x) := by
    rw [activeParts_restrict]
    exact image_subset_image fun B hB => mem_filter.2 ⟨hs.1 hB, hv B hB⟩
  refine Marked.ext ?_ ?_
  · change restrictAlong f (mergeActive x s).partition = _
    rw [mergeActive_partition hs.1, mergeActive_partition himg,
      restrictAlong_mergeBlocks_of_subset hs' hne]
    rfl
  · change (fun a => (mergeActive x s).dormant (f a)) = _
    rw [mergeActive_dormant, mergeActive_dormant]
    rfl

theorem restrict_mergeActive_of_not_visible (hs : s ∈ powersetCard 2 (activeParts x))
    (hv : ¬∀ B ∈ s, (pullBlock f B).Nonempty) :
    restrict f (mergeActive x s) = restrict f x := by
  rw [mem_powersetCard] at hs
  have hsp : s ⊆ x.partition.parts := hs.1.trans (activeParts_subset x)
  have hv' : ¬s ⊆ visibleParts f x.partition := fun h =>
    hv fun B hB => (mem_filter.1 (h hB)).2
  refine Marked.ext ?_ ?_
  · change restrictAlong f (mergeActive x s).partition = _
    rw [mergeActive_partition hs.1, restrictAlong_mergeBlocks_of_not_subset hsp hs.2 hv']
    rfl
  · change (fun a => (mergeActive x s).dormant (f a)) = _
    rw [mergeActive_dormant]
    rfl

private theorem sum_powersetCard_image {γ δ : Type*} [DecidableEq δ]
    (t : Finset γ) (φ : γ → δ) (hφ : Set.InjOn φ (↑t : Set γ)) (k : ℕ) (H : Finset δ → ℝ) :
    ∑ s ∈ powersetCard k (t.image φ), H s = ∑ s ∈ powersetCard k t, H (s.image φ) := by
  symm
  refine Finset.sum_bij (fun s _ => s.image φ) ?_ ?_ ?_ ?_
  · intro s hs
    rw [mem_powersetCard] at hs ⊢
    exact ⟨image_subset_image hs.1,
      by rw [card_image_of_injOn (hφ.mono (coe_subset.2 hs.1)), hs.2]⟩
  · have key : ∀ s u : Finset γ, s ⊆ t → u ⊆ t → s.image φ = u.image φ → s ⊆ u := by
      intro s u hs hu hsu B hB
      have hBu : φ B ∈ u.image φ := hsu ▸ mem_image_of_mem _ hB
      obtain ⟨B', hB', hBe⟩ := mem_image.1 hBu
      exact hφ (mem_coe.2 (hu hB')) (mem_coe.2 (hs hB)) hBe ▸ hB'
    intro s hs u hu hsu
    rw [mem_powersetCard] at hs hu
    exact Finset.Subset.antisymm (key s u hs.1 hu.1 hsu) (key u s hu.1 hs.1 hsu.symm)
  · intro s' hs'
    rw [mem_powersetCard] at hs'
    obtain ⟨s, hs, rfl⟩ := Finset.subset_image_iff.1 hs'.1
    refine ⟨s, mem_powersetCard.2 ⟨hs, ?_⟩, rfl⟩
    rw [← card_image_of_injOn (hφ.mono (coe_subset.2 hs)), hs'.2]
  · intro s _
    rfl

omit [DecidableEq α] in
private theorem pullBlock_injOn_filter (f : α → β) (x : Marked β) (t : Finset (Finset β))
    (ht : t ⊆ x.partition.parts) :
    Set.InjOn (pullBlock f) (↑(t.filter fun B => (pullBlock f B).Nonempty) : Set (Finset β)) :=
  (pullBlock_injOn f x.partition).mono fun B hB => by
    rw [mem_coe, mem_filter] at hB
    exact mem_coe.2 (mem_filter.2 ⟨ht hB.1, hB.2⟩)

private theorem sum_flip_restrict (f : α → β) (x : Marked β) (b : Bool) (ρ : ℝ)
    (g : Marked α → ℝ) :
    ∑ B ∈ x.partition.parts.filter fun B => ∀ a ∈ B, x.dormant a = b,
        ρ * (g (restrict f (flipBlock x B)) - g (restrict f x)) =
      ∑ B' ∈ (restrict f x).partition.parts.filter
          fun B => ∀ a ∈ B, (restrict f x).dormant a = b,
        ρ * (g (flipBlock (restrict f x) B') - g (restrict f x)) := by
  rw [partsWith_restrict, Finset.sum_image fun B hB B' hB' h =>
    pullBlock_injOn_filter f x _ (filter_subset _ _) (mem_coe.2 hB) (mem_coe.2 hB') h,
    Finset.sum_filter (fun B => (pullBlock f B).Nonempty)]
  refine Finset.sum_congr rfl fun B hB => ?_
  have hBp := (mem_filter.1 hB).1
  split_ifs with hv
  · rw [restrict_flipBlock_of_nonempty hBp hv]
  · rw [restrict_flipBlock_of_not_nonempty hBp hv, sub_self, mul_zero]

private theorem sum_merge_restrict (f : α → β) (x : Marked β) (g : Marked α → ℝ) :
    ∑ s ∈ powersetCard 2 (activeParts x),
        (g (restrict f (mergeActive x s)) - g (restrict f x)) =
      ∑ s' ∈ powersetCard 2 (activeParts (restrict f x)),
        (g (mergeActive (restrict f x) s') - g (restrict f x)) := by
  have hpc : powersetCard 2 ((activeParts x).filter fun B => (pullBlock f B).Nonempty) =
      (powersetCard 2 (activeParts x)).filter fun s => ∀ B ∈ s, (pullBlock f B).Nonempty := by
    ext s
    simp only [mem_powersetCard, mem_filter, subset_iff]
    constructor
    · rintro ⟨h, hc⟩
      exact ⟨⟨fun B hB => (h hB).1, hc⟩, fun B hB => (h hB).2⟩
    · rintro ⟨⟨h, hc⟩, hv⟩
      exact ⟨fun B hB => ⟨h hB, hv B hB⟩, hc⟩
  rw [activeParts_restrict, sum_powersetCard_image _ _
    (pullBlock_injOn_filter f x _ (activeParts_subset x)), hpc, Finset.sum_filter]
  refine Finset.sum_congr rfl fun s hs => ?_
  split_ifs with hv
  · rw [restrict_mergeActive_of_visible hs hv]
  · rw [restrict_mergeActive_of_not_visible hs hv, sub_self]

variable {c K : ℝ}

/-- Source: blath_etal2016, Remark 3.3. -/
theorem chain_lumps_restrict (hc : 0 ≤ c) (hK : 0 ≤ K) (f : α → β) :
    (chain β c K hc hK).Lumps (restrict f) (chain α c K hc hK) := by
  refine lumps_of_forall_sum fun g x => ?_
  rw [sum_chain_Q_mul hc hK x fun y => g (restrict f y),
    sum_chain_Q_mul hc hK (restrict f x) g]
  congr 1
  · congr 1
    · exact sum_flip_restrict f x false c g
    · exact sum_flip_restrict f x true (c * K) g
  · exact sum_merge_restrict f x g

theorem chain_semigroup_restrict (hc : 0 ≤ c) (hK : 0 ≤ K) (f : α → β) (t : ℝ)
    (x : Marked β) (y : Marked α) :
    ∑ z with restrict f z = y, (chain β c K hc hK).semigroup t x z =
      (chain α c K hc hK).semigroup t (restrict f x) y :=
  (chain_lumps_restrict hc hK f).sum_semigroup_fibre t x y

theorem map_chain_fdd_restrict (hc : 0 ≤ c) (hK : 0 ≤ K) (f : α → β) {k : ℕ} {t : Fin k → ℝ}
    (hmono : Monotone t) (h0 : ∀ i, 0 ≤ t i) (x : Marked β) :
    ((chain β c K hc hK).fdd x t).map (fun y i => restrict f (y i)) =
      (chain α c K hc hK).fdd (restrict f x) t :=
  (chain_lumps_restrict hc hK f).map_fdd x hmono h0

theorem restrict_allActive {f : α → β} (hf : Function.Injective f) :
    restrict f (allActive β) = allActive α :=
  Marked.ext (restrictAlong_bot hf) rfl

theorem map_chain_fdd_allActive (hc : 0 ≤ c) (hK : 0 ≤ K) {f : α → β}
    (hf : Function.Injective f) {k : ℕ} {t : Fin k → ℝ} (hmono : Monotone t)
    (h0 : ∀ i, 0 ≤ t i) :
    ((chain β c K hc hK).fdd (allActive β) t).map (fun y i => restrict f (y i)) =
      (chain α c K hc hK).fdd (allActive α) t := by
  have h := map_chain_fdd_restrict hc hK f hmono h0 (allActive β)
  rwa [restrict_allActive hf] at h

theorem map_chain_fdd_count (hc : 0 ≤ c) (hK : 0 ≤ K) {k : ℕ} {t : Fin k → ℝ}
    (hmono : Monotone t) (h0 : ∀ i, 0 ≤ t i) (x : Marked α) :
    ((chain α c K hc hK).fdd x t).map (fun y i => count (y i)) =
      (countChain (Fintype.card α) c K hc hK).fdd (count x) t :=
  (chain_lumps_count hc hK).map_fdd x hmono h0

end Rhone.Coalescent.SeedBank
