/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Statistics.EwensLabelRecursion
public import Rhone.Coalescent.KingmanPartition

/-!
# Killing weight of a block partition and its merge recursion

Source: durrett2008, sec. 1.3.1. -/

@[expose] public section
namespace Rhone.Statistics
open Finset Coalescent Rhone.Combinatorics MarkovChain

section pairs

variable {ι : Type*} [DecidableEq ι]

theorem sum_erase_pair_eq_two_mul (T : Finset ι) (F : Finset ι → ℝ) :
    ∑ i ∈ T, ∑ k ∈ T.erase i, F {i, k} = 2 * ∑ s ∈ powersetCard 2 T, F s := by
  have h1 : ∀ i ∈ T, ∑ k ∈ T.erase i, F {i, k} =
      ∑ s ∈ (powersetCard 2 T).filter (fun s => i ∈ s), F s := by
    intro i hi
    have himg : (powersetCard 2 T).filter (fun s => i ∈ s) =
        (T.erase i).image (fun k => ({i, k} : Finset ι)) := by
      ext s
      simp only [mem_filter, mem_powersetCard, mem_image, mem_erase]
      constructor
      · rintro ⟨⟨hsT, hc⟩, his⟩
        obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hc
        rcases mem_insert.1 his with rfl | h
        · exact ⟨b, ⟨hab.symm, hsT (by simp)⟩, rfl⟩
        · rw [mem_singleton] at h
          subst h
          exact ⟨a, ⟨hab, hsT (by simp)⟩, Finset.pair_comm _ _⟩
      · rintro ⟨k, ⟨hki, hkT⟩, rfl⟩
        refine ⟨⟨?_, Finset.card_pair hki.symm⟩, mem_insert_self _ _⟩
        intro x hx
        rcases mem_insert.1 hx with rfl | hx
        · exact hi
        · rw [mem_singleton.1 hx]
          exact hkT
    rw [himg, Finset.sum_image]
    intro k hk k' _ h
    have hk1 : k ∈ T.erase i := hk
    have hk2 : k ∈ ({i, k} : Finset ι) := by simp
    have h' : ({i, k} : Finset ι) = {i, k'} := h
    rw [h'] at hk2
    rcases mem_insert.1 hk2 with h3 | h3
    · exact absurd h3 (mem_erase.1 hk1).1
    · exact mem_singleton.1 h3
  calc ∑ i ∈ T, ∑ k ∈ T.erase i, F {i, k}
      = ∑ i ∈ T, ∑ s ∈ (powersetCard 2 T).filter (fun s => i ∈ s), F s :=
        Finset.sum_congr rfl h1
    _ = ∑ s ∈ powersetCard 2 T, ∑ _i ∈ s, F s := by
        refine Finset.sum_comm' fun i s => ?_
        simp only [mem_filter, mem_powersetCard]
        exact ⟨fun h => ⟨h.2.2, h.2.1⟩, fun h => ⟨h.2.1 h.1, h.2, h.1⟩⟩
    _ = ∑ s ∈ powersetCard 2 T, 2 * F s := by
        refine Finset.sum_congr rfl fun s hs => ?_
        rw [Finset.sum_const, (mem_powersetCard.1 hs).2, two_nsmul, two_mul]
    _ = 2 * ∑ s ∈ powersetCard 2 T, F s := (Finset.mul_sum _ _ _).symm

variable {κ : Type*} [DecidableEq κ]

omit [DecidableEq κ] in
theorem labelFull_update_empty {T : Finset ι} {ℓ : ι → Finset κ} {x : ι}
    (hx : labelFull T ℓ x) {y : ι} (hy : y ∈ T) :
    labelFull T (Function.update ℓ x ∅) y ↔ labelFull T ℓ y := by
  by_cases hyx : y = x
  · rw [hyx]
    refine iff_of_true ⟨?_, fun k _ _ => ?_⟩ hx
    · rw [Function.update_self]
      simp
    · rw [Function.update_self]
      exact Finset.disjoint_empty_left _
  · unfold labelFull
    rw [Function.update_of_ne hyx]
    refine and_congr_right fun _ => forall₃_congr fun k hk hky => ?_
    by_cases hkx : k = x
    · rw [hkx, Function.update_self]
      exact iff_of_true (Finset.disjoint_empty_right _) ((hx.2 y hy hyx).symm)
    · rw [Function.update_of_ne hkx]

omit [DecidableEq ι] [DecidableEq κ] in
theorem labelFull_congr {T : Finset ι} {ℓ ℓ' : ι → Finset κ} (h : ∀ i ∈ T, ℓ i = ℓ' i) {y : ι}
    (hy : y ∈ T) : labelFull T ℓ y ↔ labelFull T ℓ' y := by
  unfold labelFull
  rw [h y hy]
  exact and_congr_right fun _ => forall₃_congr fun k hk _ => by rw [h k hk]

theorem labelWeight_val_of_card_le_one {θ : ℝ} (hθ : 0 < θ) {s : Finset κ} (hs : s.card ≤ 1) :
    labelWeight θ s.val = 1 := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨t, ht⟩
  · rw [Finset.empty_val, labelWeight_zero]
  · have hst : s = {t} := Finset.eq_singleton_iff_unique_mem.2
      ⟨ht, fun y hy => Finset.card_le_one.1 hs y hy t ht⟩
    have h := labelWeight_cons_of_notMem hθ (Multiset.notMem_zero t)
    rw [labelWeight_zero, Multiset.card_zero, Nat.cast_zero, add_zero, mul_one,
      Multiset.cons_zero] at h
    rw [hst, Finset.singleton_val]
    exact mul_right_cancel₀ hθ.ne' (h.trans (one_mul θ).symm)

end pairs

variable {α κ : Type*} [Fintype α] [DecidableEq α] [DecidableEq κ] {θ : ℝ}
  {π : Finpartition (univ : Finset α)} {A : Finset α} {c : α → κ}

def blockLabels (A : Finset α) (c : α → κ) (B : Finset α) : Finset κ :=
  (B ∩ A).image c

omit [Fintype α] in
theorem blockLabels_union (A : Finset α) (c : α → κ) (B B' : Finset α) :
    blockLabels A c (B ∪ B') = blockLabels A c B ∪ blockLabels A c B' := by
  unfold blockLabels
  rw [Finset.union_inter_distrib_right, Finset.image_union]

noncomputable def killingWeight (θ : ℝ) (π : Finpartition (univ : Finset α)) (A : Finset α)
    (c : α → κ) : ℝ :=
  cfgWeight θ π.parts (blockLabels A c)

theorem blockLabels_sdiff {x B : Finset α} (hx : x ∈ π.parts) (hB : B ∈ π.parts) :
    blockLabels (A \ x) c B = Function.update (blockLabels A c) x ∅ B := by
  by_cases hBx : B = x
  · rw [hBx, Function.update_self]
    unfold blockLabels
    rw [Finset.inter_sdiff_self, Finset.image_empty]
  · rw [Function.update_of_ne hBx]
    unfold blockLabels
    have hd : Disjoint B x := π.disjoint hB hx hBx
    congr 1
    ext a
    simp only [mem_inter, mem_sdiff]
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, Finset.disjoint_left.1 hd h.1⟩⟩

theorem killingWeight_sdiff {x : Finset α} (hx : x ∈ π.parts) :
    killingWeight θ π (A \ x) c =
      cfgWeight θ π.parts (Function.update (blockLabels A c) x ∅) :=
  cfgWeight_congr θ fun _ hB => blockLabels_sdiff hx hB

theorem killingWeight_mergeBlocks {i k : Finset α} (hi : i ∈ π.parts)
    (hk : k ∈ π.parts.erase i) :
    killingWeight θ (mergeBlocks π {i, k}) A c =
      cfgWeight θ π.parts (mergeLabels (blockLabels A c) i k) := by
  have hki : k ≠ i := (mem_erase.1 hk).1
  have hkT : k ∈ π.parts := mem_of_mem_erase hk
  have hs : ({i, k} : Finset (Finset α)) ⊆ π.parts := by
    intro B hB
    rcases mem_insert.1 hB with rfl | hB
    · exact hi
    · rw [mem_singleton.1 hB]
      exact hkT
  have hc : ({i, k} : Finset (Finset α)).card = 2 := Finset.card_pair hki.symm
  have hsup : ({i, k} : Finset (Finset α)).sup id = i ∪ k := by simp
  have hR : π.parts \ {i, k} = (π.parts.erase i).erase k := by
    ext B
    simp only [mem_sdiff, mem_insert, mem_singleton, mem_erase]
    tauto
  have hnot : i ∪ k ∉ (π.parts.erase i).erase k := by
    rw [← hR, ← hsup]
    exact fun h => sup_notMem_parts hs hc (mem_sdiff.1 h).1
  unfold killingWeight
  rw [parts_mergeBlocks hs ⟨i, mem_insert_self _ _⟩, hsup, hR]
  refine cfgWeight_congr' θ ?_ ?_
  · rw [valid_mergeLabels hi hk, Finset.forall_mem_insert, blockLabels_union]
  · rw [sum_mergeLabels hi hk, Finset.sum_insert hnot, blockLabels_union]

theorem mergeBlocks_injOn_powersetCard (π : Finpartition (univ : Finset α)) :
    Set.InjOn (mergeBlocks π) (powersetCard 2 π.parts : Set (Finset (Finset α))) := by
  intro s hs t ht hst
  rw [mem_coe, mem_powersetCard] at hs ht
  rw [← parts_sdiff_parts_mergeBlocks hs.1 hs.2, ← parts_sdiff_parts_mergeBlocks ht.1 ht.2]
  exact congrArg (fun ρ : Finpartition (univ : Finset α) => π.parts \ ρ.parts) hst

theorem sum_merges (π : Finpartition (univ : Finset α))
    (f : Finpartition (univ : Finset α) → ℝ) :
    ∑ σ ∈ merges π, f σ = ∑ s ∈ powersetCard 2 π.parts, f (mergeBlocks π s) := by
  rw [merges, Finset.sum_image (mergeBlocks_injOn_powersetCard π)]

theorem killingWeight_recursion (hθ : 0 < θ) (π : Finpartition (univ : Finset α))
    (A : Finset α) (c : α → κ) :
    (π.parts.card : ℝ) * ((π.parts.card : ℝ) - 1 + θ) * killingWeight θ π A c =
      2 * ∑ s ∈ powersetCard 2 π.parts, killingWeight θ (mergeBlocks π s) A c +
        θ * ∑ x ∈ π.parts.filter (labelFull π.parts (blockLabels A c)),
          killingWeight θ π (A \ x) c := by
  have h := cfgWeight_recursion hθ π.parts (blockLabels A c)
  have h1 : ∑ i ∈ π.parts, ∑ k ∈ π.parts.erase i,
      cfgWeight θ π.parts (mergeLabels (blockLabels A c) i k) =
      2 * ∑ s ∈ powersetCard 2 π.parts, killingWeight θ (mergeBlocks π s) A c := by
    rw [← sum_erase_pair_eq_two_mul π.parts fun s => killingWeight θ (mergeBlocks π s) A c]
    exact Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun k hk =>
      (killingWeight_mergeBlocks hi hk).symm
  have h2 : ∑ x ∈ π.parts.filter (labelFull π.parts (blockLabels A c)),
      cfgWeight θ π.parts (Function.update (blockLabels A c) x ∅) =
      ∑ x ∈ π.parts.filter (labelFull π.parts (blockLabels A c)),
        killingWeight θ π (A \ x) c :=
    Finset.sum_congr rfl fun x hx => (killingWeight_sdiff (mem_filter.1 hx).1).symm
  rw [h1, h2] at h
  exact h

theorem killingWeight_of_card_le_one (hθ : 0 < θ) (hπ : π.parts.card ≤ 1) (A : Finset α)
    (c : α → κ) :
    killingWeight θ π A c = if ∀ a ∈ A, ∀ b ∈ A, c a = c b then 1 else 0 := by
  by_cases hn : π.parts = ∅
  · have huniv : (univ : Finset α) = ∅ := by
      rw [← π.sup_parts, hn, Finset.sup_empty]
      rfl
    have hall : ∀ a ∈ A, ∀ b ∈ A, c a = c b := fun a _ => by
      have ha := mem_univ a
      rw [huniv] at ha
      exact absurd ha (Finset.notMem_empty a)
    rw [ite_eq_left hall]
    unfold killingWeight cfgWeight
    rw [hn]
    simp [labelWeight_zero]
  · obtain ⟨B, hB⟩ := Finset.card_eq_one.1
      (le_antisymm hπ (Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hn)))
    have hBu : B = univ := by
      have h := π.sup_parts
      rwa [hB, Finset.sup_singleton] at h
    have hl : blockLabels A c B = A.image c := by
      unfold blockLabels
      rw [hBu, Finset.univ_inter]
    have hval : (∀ i ∈ π.parts, (blockLabels A c i).card ≤ 1) ↔ (A.image c).card ≤ 1 := by
      rw [hB, ← hl]
      simp only [mem_singleton, forall_eq]
    have hiff : (A.image c).card ≤ 1 ↔ ∀ a ∈ A, ∀ b ∈ A, c a = c b := by
      rw [Finset.card_le_one]
      constructor
      · exact fun h a ha b hb => h _ (mem_image_of_mem c ha) _ (mem_image_of_mem c hb)
      · intro h u hu v hv
        obtain ⟨a, ha, rfl⟩ := mem_image.1 hu
        obtain ⟨b, hb, rfl⟩ := mem_image.1 hv
        exact h a ha b hb
    by_cases hc : (A.image c).card ≤ 1
    · rw [ite_eq_left (hiff.1 hc)]
      unfold killingWeight
      rw [cfgWeight_of_valid θ (hval.2 hc), hB, Finset.sum_singleton, hl]
      exact labelWeight_val_of_card_le_one hθ hc
    · rw [ite_eq_right (fun h => hc (hiff.2 h))]
      exact ite_eq_right fun h => hc (hval.1 h)

end Rhone.Statistics
