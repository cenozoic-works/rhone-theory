/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.LambdaPartitionChain
public import Rhone.Coalescent.KingmanRestriction

/-! # Restriction consistency of the Λ-coalescent, and the Bolthausen–Sznitman chain -/

@[expose] public section

namespace Rhone.Coalescent

open MeasureTheory Finset MarkovChain

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- Source: pitman1999, Lemma 18, eq. (22). -/
theorem lambdaRate_eq_sum_choose {Λ : Measure ℝ} (hΛ : Λ (Set.Icc 0 1) ≠ ⊤) {b k : ℕ}
    (hk : 2 ≤ k) (hkb : k ≤ b) (h : ℕ) :
    lambdaRate Λ b k =
      ∑ m ∈ Finset.range (h + 1), (h.choose m : ℝ) * lambdaRate Λ (b + h) (k + m) := by
  unfold lambdaRate
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ fun m _ => (integrableOn_lambdaIntegrand hΛ _ _).const_mul _]
  refine setIntegral_congr_fun measurableSet_Icc fun x _ => ?_
  have hbin : ∑ m ∈ Finset.range (h + 1), x ^ m * (1 - x) ^ (h - m) * (h.choose m : ℝ) = 1 := by
    rw [← add_pow]
    simp
  calc x ^ (k - 2) * (1 - x) ^ (b - k)
      = x ^ (k - 2) * (1 - x) ^ (b - k) *
          ∑ m ∈ Finset.range (h + 1), x ^ m * (1 - x) ^ (h - m) * (h.choose m : ℝ) := by
        rw [hbin, mul_one]
    _ = ∑ m ∈ Finset.range (h + 1),
          (h.choose m : ℝ) * (x ^ (k + m - 2) * (1 - x) ^ (b + h - (k + m))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m hm => ?_
        have hm' : m ≤ h := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
        have e1 : k + m - 2 = (k - 2) + m := by omega
        have e2 : b + h - (k + m) = (b - k) + (h - m) := by omega
        rw [e1, e2, pow_add, pow_add]
        ring

theorem mergeBlocks_singleton {π : Finpartition (univ : Finset α)} {B : Finset α}
    (hB : B ∈ π.parts) : mergeBlocks π {B} = π := by
  refine eq_of_part_eq fun a => ?_
  rw [part_mergeBlocks (singleton_subset_iff.2 hB) (singleton_nonempty B)]
  split_ifs with h
  · rw [Finset.sup_singleton, id, Finset.mem_singleton.1 h]
  · rfl

variable {f : α → β} {π : Finpartition (univ : Finset β)} {s : Finset (Finset β)}

theorem restrictAlong_mergeBlocks_inter_visibleParts (hs : s ⊆ π.parts)
    (hne : (s ∩ visibleParts f π).Nonempty) :
    restrictAlong f (mergeBlocks π s) =
      restrictAlong f (mergeBlocks π (s ∩ visibleParts f π)) := by
  have hs' : s ∩ visibleParts f π ⊆ π.parts := inter_subset_left.trans hs
  have hne' : s.Nonempty := hne.mono inter_subset_left
  refine eq_of_part_eq fun a => ?_
  rw [part_restrictAlong, part_restrictAlong, part_mergeBlocks hs hne',
    part_mergeBlocks hs' hne]
  have hiff : π.part (f a) ∈ s ∩ visibleParts f π ↔ π.part (f a) ∈ s :=
    ⟨fun h => (mem_inter.1 h).1, fun h => mem_inter.2 ⟨h, part_mem_visibleParts f π a⟩⟩
  by_cases h : π.part (f a) ∈ s
  · rw [ite_eq_left h, ite_eq_left (hiff.2 h)]
    ext c
    simp only [mem_pullBlock, Finset.mem_sup, id]
    constructor
    · rintro ⟨B, hB, hc⟩
      refine ⟨B, mem_inter.2 ⟨hB, ?_⟩, hc⟩
      rw [← π.part_eq_of_mem (hs hB) hc]
      exact part_mem_visibleParts f π c
    · rintro ⟨B, hB, hc⟩
      exact ⟨B, (mem_inter.1 hB).1, hc⟩
  · rw [ite_eq_right h, ite_eq_right (mt hiff.1 h)]

theorem restrictAlong_mergeBlocks_of_inter_eq_empty (hs : s ⊆ π.parts)
    (he : s ∩ visibleParts f π = ∅) :
    restrictAlong f (mergeBlocks π s) = restrictAlong f π := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · have h0 : mergeBlocks π ∅ = π := by simp [mergeBlocks]
    rw [h0]
  · refine eq_of_part_eq fun a => ?_
    rw [part_restrictAlong, part_restrictAlong, part_mergeBlocks hs hne]
    have h : π.part (f a) ∉ s := fun h => by
      have hm : π.part (f a) ∈ s ∩ visibleParts f π :=
        mem_inter.2 ⟨h, part_mem_visibleParts f π a⟩
      rw [he] at hm
      exact absurd hm (notMem_empty _)
    rw [ite_eq_right h]

theorem restrictAlong_mergeBlocks_of_card_inter_le_one (hs : s ⊆ π.parts)
    (hc : (s ∩ visibleParts f π).card ≤ 1) :
    restrictAlong f (mergeBlocks π s) = restrictAlong f π := by
  rcases Nat.lt_or_ge (s ∩ visibleParts f π).card 1 with h0 | h1
  · exact restrictAlong_mergeBlocks_of_inter_eq_empty hs (card_eq_zero.1 (by omega))
  · obtain ⟨B, hB⟩ := card_eq_one.1 (le_antisymm hc h1)
    have hBs : B ∈ s ∩ visibleParts f π := hB ▸ mem_singleton_self B
    rw [restrictAlong_mergeBlocks_inter_visibleParts hs ⟨B, hBs⟩, hB,
      mergeBlocks_singleton (hs (mem_inter.1 hBs).1)]

theorem restrictAlong_mergeBlocks_of_two_le_card_inter (hs : s ⊆ π.parts)
    (hc : 2 ≤ (s ∩ visibleParts f π).card) :
    restrictAlong f (mergeBlocks π s) =
      mergeBlocks (restrictAlong f π) ((s ∩ visibleParts f π).image (pullBlock f)) := by
  have hne : (s ∩ visibleParts f π).Nonempty := card_pos.1 (by omega)
  rw [restrictAlong_mergeBlocks_inter_visibleParts hs hne,
    restrictAlong_mergeBlocks_of_subset inter_subset_right hne]

private theorem sum_powerset_union {ι : Type*} [DecidableEq ι] (V H : Finset ι)
    (hd : Disjoint V H) {U : Finset ι} (hU : V ∪ H = U) (F : Finset ι → ℝ) :
    ∑ s ∈ U.powerset, F s = ∑ t ∈ V.powerset, ∑ w ∈ H.powerset, F (t ∪ w) := by
  subst hU
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun s => (s ∩ V, s ∩ H)) (fun p => p.1 ∪ p.2) ?_ ?_ ?_ ?_ ?_
  · intro s _
    exact mem_product.2 ⟨mem_powerset.2 inter_subset_right, mem_powerset.2 inter_subset_right⟩
  · intro p hp
    obtain ⟨h1, h2⟩ := mem_product.1 hp
    exact mem_powerset.2 (union_subset_union (mem_powerset.1 h1) (mem_powerset.1 h2))
  · intro s hs
    change s ∩ V ∪ s ∩ H = s
    rw [← inter_union_distrib_left, inter_eq_left.2 (mem_powerset.1 hs)]
  · intro p hp
    obtain ⟨h1, h2⟩ := mem_product.1 hp
    have h1' := mem_powerset.1 h1
    have h2' := mem_powerset.1 h2
    refine Prod.ext ?_ ?_
    · change (p.1 ∪ p.2) ∩ V = p.1
      rw [union_inter_distrib_right, inter_eq_left.2 h1',
        disjoint_iff_inter_eq_empty.1 (hd.symm.mono_left h2'), union_empty]
    · change (p.1 ∪ p.2) ∩ H = p.2
      rw [union_inter_distrib_right, inter_eq_left.2 h2',
        disjoint_iff_inter_eq_empty.1 (hd.mono_left h1'), empty_union]
  · intro s hs
    change F s = F (s ∩ V ∪ s ∩ H)
    rw [← inter_union_distrib_left, inter_eq_left.2 (mem_powerset.1 hs)]

theorem lambdaPartitionQ_eq_sum (Λ : Measure ℝ) (π ρ : Finpartition (univ : Finset α)) :
    lambdaPartitionQ Λ π ρ = ∑ s ∈ mergeSets π, lambdaRate Λ π.parts.card s.card *
      ((if mergeBlocks π s = ρ then (1 : ℝ) else 0) - if ρ = π then 1 else 0) := by
  unfold lambdaPartitionQ lambdaPartitionRate
  simp only [mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib]
  congr 1
  split_ifs <;> simp

/-- Source: pitman1999, Thm 6. -/
theorem lambdaPartitionChain_lumps_restrictAlong {Λ : Measure ℝ} (hΛ : Λ (Set.Icc 0 1) ≠ ⊤)
    (f : α → β) :
    (lambdaPartitionChain β Λ).Lumps (restrictAlong f) (lambdaPartitionChain α Λ) := by
  intro π σ
  rw [lambdaPartitionChain_Q, lambdaPartitionChain_Q,
    lambdaPartitionQ_eq_sum Λ (restrictAlong f π) σ]
  have hVsub : visibleParts f π ⊆ π.parts := visibleParts_subset f π
  have hVH : visibleParts f π ∪ (π.parts \ visibleParts f π) = π.parts :=
    union_sdiff_of_subset hVsub
  have hdisj : Disjoint (visibleParts f π) (π.parts \ visibleParts f π) := disjoint_sdiff
  have hcard : π.parts.card = (visibleParts f π).card + (π.parts \ visibleParts f π).card := by
    rw [← card_union_of_disjoint hdisj, hVH]
  have hσ0 : (restrictAlong f π).parts.card = (visibleParts f π).card := by
    rw [parts_restrictAlong, card_image_of_injOn (pullBlock_injOn f π)]
  have h1 : ∑ ρ with restrictAlong f ρ = σ, lambdaPartitionQ Λ π ρ =
      ∑ s ∈ mergeSets π, lambdaRate Λ π.parts.card s.card *
        ((if restrictAlong f (mergeBlocks π s) = σ then (1 : ℝ) else 0) -
          if restrictAlong f π = σ then 1 else 0) := by
    simp only [lambdaPartitionQ_eq_sum Λ π]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq']
    simp only [mem_filter, mem_univ, true_and]
  rw [h1, mergeSets, Finset.sum_filter,
    sum_powerset_union (visibleParts f π) (π.parts \ visibleParts f π) hdisj hVH]
  have h3 : ∀ t ∈ (visibleParts f π).powerset,
      ∑ w ∈ (π.parts \ visibleParts f π).powerset,
        (if 2 ≤ (t ∪ w).card then lambdaRate Λ π.parts.card (t ∪ w).card *
          ((if restrictAlong f (mergeBlocks π (t ∪ w)) = σ then (1 : ℝ) else 0) -
            if restrictAlong f π = σ then 1 else 0) else 0) =
      if 2 ≤ t.card then lambdaRate Λ (visibleParts f π).card t.card *
        ((if mergeBlocks (restrictAlong f π) (t.image (pullBlock f)) = σ then (1 : ℝ) else 0) -
          if restrictAlong f π = σ then 1 else 0) else 0 := by
    intro t ht
    have htV : t ⊆ visibleParts f π := mem_powerset.1 ht
    have hinter : ∀ w ∈ (π.parts \ visibleParts f π).powerset,
        (t ∪ w) ∩ visibleParts f π = t := by
      intro w hw
      rw [union_inter_distrib_right, inter_eq_left.2 htV,
        disjoint_iff_inter_eq_empty.1 (hdisj.symm.mono_left (mem_powerset.1 hw)), union_empty]
    have hsub : ∀ w ∈ (π.parts \ visibleParts f π).powerset, t ∪ w ⊆ π.parts := fun w hw =>
      union_subset (htV.trans hVsub) ((mem_powerset.1 hw).trans sdiff_subset)
    have hcardu : ∀ w ∈ (π.parts \ visibleParts f π).powerset,
        (t ∪ w).card = t.card + w.card := fun w hw =>
      card_union_of_disjoint (hdisj.mono htV (mem_powerset.1 hw))
    by_cases hc : 2 ≤ t.card
    · rw [ite_eq_left hc]
      have hterm : ∀ w ∈ (π.parts \ visibleParts f π).powerset,
          (if 2 ≤ (t ∪ w).card then lambdaRate Λ π.parts.card (t ∪ w).card *
            ((if restrictAlong f (mergeBlocks π (t ∪ w)) = σ then (1 : ℝ) else 0) -
              if restrictAlong f π = σ then 1 else 0) else 0) =
          lambdaRate Λ ((visibleParts f π).card + (π.parts \ visibleParts f π).card)
              (t.card + w.card) *
            ((if mergeBlocks (restrictAlong f π) (t.image (pullBlock f)) = σ
              then (1 : ℝ) else 0) - if restrictAlong f π = σ then 1 else 0) := by
        intro w hw
        rw [ite_eq_left (by rw [hcardu w hw]; omega), hcardu w hw, ← hcard,
          restrictAlong_mergeBlocks_of_two_le_card_inter (hsub w hw)
            (by rw [hinter w hw]; exact hc), hinter w hw]
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul,
        Finset.sum_powerset_apply_card (fun m => lambdaRate Λ
          ((visibleParts f π).card + (π.parts \ visibleParts f π).card) (t.card + m))]
      simp only [nsmul_eq_mul]
      rw [← lambdaRate_eq_sum_choose hΛ hc (card_le_card htV)
        (π.parts \ visibleParts f π).card]
    · rw [ite_eq_right hc]
      refine Finset.sum_eq_zero fun w hw => ?_
      rw [restrictAlong_mergeBlocks_of_card_inter_le_one (hsub w hw)
        (by rw [hinter w hw]; omega), sub_self, mul_zero, ite_self]
  rw [Finset.sum_congr rfl h3, ← Finset.sum_filter, hσ0]
  refine Finset.sum_bij (fun t _ => t.image (pullBlock f)) ?_ ?_ ?_ ?_
  · intro t ht
    obtain ⟨ht1, ht2⟩ := mem_filter.1 ht
    have htV := mem_powerset.1 ht1
    rw [mem_mergeSets, parts_restrictAlong]
    refine ⟨image_subset_image htV, ?_⟩
    rw [card_image_of_injOn ((pullBlock_injOn f π).mono (coe_subset.2 htV))]
    exact ht2
  · have key : ∀ s t : Finset (Finset β), s ⊆ visibleParts f π →
        t ⊆ visibleParts f π → s.image (pullBlock f) = t.image (pullBlock f) →
        s ⊆ t := by
      intro s t hs ht hst B hB
      have hBt : pullBlock f B ∈ t.image (pullBlock f) := hst ▸ mem_image_of_mem _ hB
      obtain ⟨B', hB', hBe⟩ := mem_image.1 hBt
      exact pullBlock_injOn f π (mem_coe.2 (ht hB')) (mem_coe.2 (hs hB)) hBe ▸ hB'
    intro s hs t ht hst
    have hs' := mem_powerset.1 (mem_filter.1 hs).1
    have ht' := mem_powerset.1 (mem_filter.1 ht).1
    exact Finset.Subset.antisymm (key s t hs' ht' hst) (key t s ht' hs' hst.symm)
  · intro u hu
    rw [mem_mergeSets, parts_restrictAlong] at hu
    obtain ⟨t, ht, rfl⟩ := Finset.subset_image_iff.1 hu.1
    refine ⟨t, mem_filter.2 ⟨mem_powerset.2 ht, ?_⟩, rfl⟩
    rw [← card_image_of_injOn ((pullBlock_injOn f π).mono (coe_subset.2 ht))]
    exact hu.2
  · intro t ht
    have htV := mem_powerset.1 (mem_filter.1 ht).1
    rw [card_image_of_injOn ((pullBlock_injOn f π).mono (coe_subset.2 htV))]
    exact congrArg₂ _ rfl (congrArg₂ _ rfl (if_congr eq_comm rfl rfl))

theorem lambdaPartitionChain_semigroup_restrictAlong {Λ : Measure ℝ}
    (hΛ : Λ (Set.Icc 0 1) ≠ ⊤) (f : α → β) (t : ℝ)
    (π : Finpartition (univ : Finset β)) (σ : Finpartition (univ : Finset α)) :
    ∑ ρ with restrictAlong f ρ = σ, (lambdaPartitionChain β Λ).semigroup t π ρ =
      (lambdaPartitionChain α Λ).semigroup t (restrictAlong f π) σ :=
  (lambdaPartitionChain_lumps_restrictAlong hΛ f).sum_semigroup_fibre t π σ

theorem map_lambdaPartitionChain_law_restrictAlong {Λ : Measure ℝ}
    (hΛ : Λ (Set.Icc 0 1) ≠ ⊤) (f : α → β) {t : ℝ} (ht : 0 ≤ t)
    (π : Finpartition (univ : Finset β)) :
    (((lambdaPartitionChain β Λ).semigroupChain t ht).kernel π).map (restrictAlong f) =
      ((lambdaPartitionChain α Λ).semigroupChain t ht).kernel (restrictAlong f π) :=
  (lambdaPartitionChain_lumps_restrictAlong hΛ f).map_semigroupChain_kernel t ht π

variable (α) in
noncomputable def bolthausenSznitmanChain : RateChain (Finpartition (univ : Finset α)) :=
  lambdaPartitionChain α (volume.restrict (Set.Icc 0 1))

theorem volume_restrict_Icc_ne_top :
    (volume.restrict (Set.Icc (0 : ℝ) 1)) (Set.Icc 0 1) ≠ ⊤ := by
  rw [Measure.restrict_apply measurableSet_Icc, Set.inter_self, Real.volume_Icc]
  exact ENNReal.ofReal_ne_top

/-- Source: bolthausen_sznitman1998, Prop. 1.3, eq. (1.33). -/
theorem bolthausenSznitmanChain_Q_of_ne {π σ : Finpartition (univ : Finset α)} (h : σ ≠ π) :
    (bolthausenSznitmanChain α).Q π σ = ∑ s ∈ mergeSets π, if mergeBlocks π s = σ then
      ((s.card - 2).factorial * (π.parts.card - s.card).factorial : ℝ) /
        ((π.parts.card - 1).factorial : ℝ) else 0 := by
  rw [bolthausenSznitmanChain, lambdaPartitionChain_Q, lambdaPartitionQ, ite_eq_right h,
    sub_zero]
  refine Finset.sum_congr rfl fun s hs => ?_
  obtain ⟨h1, h2⟩ := mem_mergeSets.1 hs
  rw [lambdaRate_lebesgue h2 (card_le_card h1)]

theorem bolthausenSznitmanChain_rate (π : Finpartition (univ : Finset α)) :
    (bolthausenSznitmanChain α).rate π = ((π.parts.card - 1 : ℕ) : ℝ) := by
  have hz : ∑ s ∈ mergeSets π, (if mergeBlocks π s = π then
      lambdaRate (volume.restrict (Set.Icc 0 1)) π.parts.card s.card else 0) = 0 := by
    refine Finset.sum_eq_zero fun s hs => ?_
    obtain ⟨h1, h2⟩ := mem_mergeSets.1 hs
    have hcard := card_parts_mergeBlocks_add h1 h2
    refine ite_eq_right fun he => ?_
    rw [he] at hcard
    omega
  rw [RateChain.rate, bolthausenSznitmanChain, lambdaPartitionChain_Q, lambdaPartitionQ, hz,
    ite_eq_left rfl, lambdaPartitionRate_eq, lambdaTotalRate]
  rcases Nat.eq_zero_or_pos π.parts.card with h0 | hpos
  · simp [h0]
  · rw [sum_choose_mul_lambdaRate_lebesgue _ hpos, Nat.cast_sub hpos]
    simp

theorem bolthausenSznitmanChain_lumps_restrictAlong (f : α → β) :
    (bolthausenSznitmanChain β).Lumps (restrictAlong f) (bolthausenSznitmanChain α) :=
  lambdaPartitionChain_lumps_restrictAlong volume_restrict_Icc_ne_top f

theorem bolthausenSznitmanChain_lumps_blockCount :
    (bolthausenSznitmanChain α).Lumps blockCount
      (lambdaBlockChain (volume.restrict (Set.Icc 0 1)) (Fintype.card α)) :=
  lambdaPartitionChain_lumps _

end Rhone.Coalescent
