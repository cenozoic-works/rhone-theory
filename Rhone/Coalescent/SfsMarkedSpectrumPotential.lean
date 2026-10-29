/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.SfsMarkedSpectrumCoeff
public import Rhone.Coalescent.TajimaFiniteMoments

/-!
# Expected branch length by block for the labelled Kingman partition chain

Source: fu1995, eq. 22; kingman1982, sec. 1, eq. (1.1)–(1.4), (1.7). -/

@[expose] public section
namespace Rhone.Coalescent
open MeasureTheory ProbabilityTheory Finset Rhone.Combinatorics MarkovChain Filter

variable {n : ℕ}

def CladeSaturated (π : Finpartition (Finset.univ : Finset (Fin n)))
    (A : Finset (Fin n)) : Prop :=
  ∀ B ∈ π.parts, B ⊆ A ∨ Disjoint B A

instance (π : Finpartition (Finset.univ : Finset (Fin n))) (A : Finset (Fin n)) :
    Decidable (CladeSaturated π A) := by
  unfold CladeSaturated
  infer_instance

def cladeInside (π : Finpartition (Finset.univ : Finset (Fin n)))
    (A : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  π.parts.filter (· ⊆ A)

/-- Source: fu1995, eq. 22. -/
noncomputable def sfsCladeTerm (π : Finpartition (Finset.univ : Finset (Fin n)))
    (A : Finset (Fin n)) : ℝ :=
  if CladeSaturated π A then sfsCladeCoeff π.parts.card (cladeInside π A).card else 0

/-- Source: fu1995, eq. 22. -/
noncomputable def blockWeightReward (w : Finset (Fin n) → ℝ)
    (π : Finpartition (Finset.univ : Finset (Fin n))) : ℝ :=
  ∑ B ∈ π.parts, w B

/-- Source: fu1995, eq. 22. -/
noncomputable def sfsWeightPotential (w : Finset (Fin n) → ℝ)
    (π : Finpartition (Finset.univ : Finset (Fin n))) : ℝ :=
  ∑ A : Finset (Fin n), w A * sfsCladeTerm π A

/-- Source: fu1995, eq. 22. -/
theorem blockWeightReward_nonneg {w : Finset (Fin n) → ℝ} (hw : ∀ B, 0 ≤ w B)
    (π : Finpartition (Finset.univ : Finset (Fin n))) : 0 ≤ blockWeightReward w π :=
  Finset.sum_nonneg fun B _ => hw B

theorem not_cladeSaturated_mergeBlocks {π : Finpartition (Finset.univ : Finset (Fin n))}
    {A : Finset (Fin n)} (h : ¬ CladeSaturated π A) (s : Finset (Finset (Fin n))) :
    ¬ CladeSaturated (mergeBlocks π s) A := by
  intro hsat
  apply h
  intro B hB
  obtain ⟨B', hB', hle⟩ := le_mergeBlocks π s hB
  rcases hsat B' hB' with h1 | h1
  · exact Or.inl (hle.trans h1)
  · exact Or.inr (h1.mono_left hle)

theorem cladeSaturated_mergeBlocks_inside {π : Finpartition (Finset.univ : Finset (Fin n))}
    {A : Finset (Fin n)} (hsat : CladeSaturated π A) {s : Finset (Finset (Fin n))}
    (hs : s ⊆ π.parts) (hc : s.card = 2) (hin : s ⊆ cladeInside π A) :
    CladeSaturated (mergeBlocks π s) A ∧
      (cladeInside (mergeBlocks π s) A).card + 1 = (cladeInside π A).card := by
  have hne : s.Nonempty := Finset.card_pos.mp (by omega)
  have hparts := parts_mergeBlocks hs hne
  have hsup : s.sup id ⊆ A :=
    Finset.sup_le fun b hb => (Finset.mem_filter.mp (hin hb)).2
  refine ⟨?_, ?_⟩
  · intro B hB
    rw [hparts, Finset.mem_insert] at hB
    rcases hB with rfl | hB
    · exact Or.inl hsup
    · exact hsat B (Finset.mem_sdiff.mp hB).1
  · have he : cladeInside (mergeBlocks π s) A = insert (s.sup id) (cladeInside π A \ s) := by
      unfold cladeInside
      rw [hparts]
      ext B
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_sdiff]
      constructor
      · rintro ⟨hB | ⟨hB, hBs⟩, hBA⟩
        · exact Or.inl hB
        · exact Or.inr ⟨⟨hB, hBA⟩, hBs⟩
      · rintro (rfl | ⟨⟨hB, hBA⟩, hBs⟩)
        · exact ⟨Or.inl rfl, hsup⟩
        · exact ⟨Or.inr ⟨hB, hBs⟩, hBA⟩
    have hnot : s.sup id ∉ cladeInside π A \ s := fun h =>
      sup_notMem_parts hs hc (Finset.mem_filter.mp (Finset.mem_sdiff.mp h).1).1
    have hle := Finset.card_le_card hin
    rw [he, Finset.card_insert_of_notMem hnot, Finset.card_sdiff_of_subset hin]
    omega

theorem cladeSaturated_mergeBlocks_outside {π : Finpartition (Finset.univ : Finset (Fin n))}
    {A : Finset (Fin n)} (hsat : CladeSaturated π A) {s : Finset (Finset (Fin n))}
    (hs : s ⊆ π.parts) (hne : s.Nonempty) (hout : ∀ b ∈ s, ¬ b ⊆ A) :
    CladeSaturated (mergeBlocks π s) A ∧
      cladeInside (mergeBlocks π s) A = cladeInside π A := by
  have hparts := parts_mergeBlocks hs hne
  have hdis : ∀ b ∈ s, Disjoint b A := fun b hb =>
    (hsat b (hs hb)).resolve_left (hout b hb)
  have hsupd : Disjoint (s.sup id) A := Finset.disjoint_sup_left.2 fun b hb => hdis b hb
  have hsupn : ¬ s.sup id ⊆ A := by
    obtain ⟨b, hb⟩ := hne
    exact fun h => hout b hb ((Finset.le_sup (f := id) hb).trans h)
  refine ⟨?_, ?_⟩
  · intro B hB
    rw [hparts, Finset.mem_insert] at hB
    rcases hB with rfl | hB
    · exact Or.inr hsupd
    · exact hsat B (Finset.mem_sdiff.mp hB).1
  · unfold cladeInside
    rw [hparts]
    ext B
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_sdiff]
    constructor
    · rintro ⟨rfl | ⟨hB, -⟩, hBA⟩
      · exact absurd hBA hsupn
      · exact ⟨hB, hBA⟩
    · rintro ⟨hB, hBA⟩
      exact ⟨Or.inr ⟨hB, fun hBs => hout B hBs hBA⟩, hBA⟩

theorem not_cladeSaturated_mergeBlocks_mixed {π : Finpartition (Finset.univ : Finset (Fin n))}
    {A : Finset (Fin n)} {s : Finset (Finset (Fin n))} (hs : s ⊆ π.parts)
    {a b : Finset (Fin n)} (ha : a ∈ s) (haA : a ⊆ A) (hb : b ∈ s) (hbA : ¬ b ⊆ A) :
    ¬ CladeSaturated (mergeBlocks π s) A := by
  intro hsat
  have hu : s.sup id ∈ (mergeBlocks π s).parts := by
    rw [parts_mergeBlocks hs ⟨a, ha⟩]
    exact Finset.mem_insert_self _ _
  rcases hsat _ hu with h | h
  · exact hbA ((Finset.le_sup (f := id) hb).trans h)
  · have hd : Disjoint a A := h.mono_left (Finset.le_sup (f := id) ha)
    obtain ⟨x, hx⟩ := π.nonempty_of_mem_parts (hs ha)
    exact (Finset.disjoint_left.mp hd) hx (haA hx)

theorem mem_parts_iff_cladeSaturated_card (π : Finpartition (Finset.univ : Finset (Fin n)))
    (A : Finset (Fin n)) :
    A ∈ π.parts ↔ CladeSaturated π A ∧ (cladeInside π A).card = 1 := by
  constructor
  · intro hA
    have hsat : CladeSaturated π A := by
      intro B hB
      by_cases hBA : B = A
      · exact Or.inl hBA.le
      · exact Or.inr (π.disjoint hB hA hBA)
    refine ⟨hsat, ?_⟩
    have he : cladeInside π A = {A} := by
      ext B
      simp only [cladeInside, Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hB, hBA⟩
        by_contra hne
        have hd : Disjoint B A := π.disjoint hB hA hne
        obtain ⟨x, hx⟩ := π.nonempty_of_mem_parts hB
        exact (Finset.disjoint_left.mp hd) hx (hBA hx)
      · rintro rfl
        exact ⟨hA, subset_rfl⟩
    rw [he, Finset.card_singleton]
  · rintro ⟨hsat, hcard⟩
    obtain ⟨B, hB⟩ := Finset.card_eq_one.mp hcard
    have hBmem : B ∈ cladeInside π A := by rw [hB]; exact Finset.mem_singleton_self B
    have hBp : B ∈ π.parts := (Finset.mem_filter.mp hBmem).1
    have hBA : B ⊆ A := (Finset.mem_filter.mp hBmem).2
    have hAB : A ⊆ B := by
      intro x hx
      have hxp : π.part x ∈ π.parts := π.part_mem.2 (Finset.mem_univ x)
      have hxx : x ∈ π.part x := π.mem_part (Finset.mem_univ x)
      have hsub : π.part x ⊆ A := by
        rcases hsat _ hxp with h | h
        · exact h
        · exact absurd hx ((Finset.disjoint_left.mp h) hxx)
      have hin : π.part x ∈ cladeInside π A := Finset.mem_filter.mpr ⟨hxp, hsub⟩
      rw [hB, Finset.mem_singleton] at hin
      rw [← hin]
      exact hxx
    rw [show A = B from Finset.Subset.antisymm hAB hBA]
    exact hBp

/-- Source: fu1995, eq. 22. -/
theorem sum_sfsCladeTerm_mergeBlocks {π : Finpartition (Finset.univ : Finset (Fin n))}
    {A : Finset (Fin n)} (hsat : CladeSaturated π A) :
    ∑ s ∈ π.parts.powersetCard 2, sfsCladeTerm (mergeBlocks π s) A =
      ((cladeInside π A).card.choose 2 : ℝ) *
          sfsCladeCoeff (π.parts.card - 1) ((cladeInside π A).card - 1) +
        ((π.parts.card - (cladeInside π A).card).choose 2 : ℝ) *
          sfsCladeCoeff (π.parts.card - 1) (cladeInside π A).card := by
  have hInP : cladeInside π A ⊆ π.parts := Finset.filter_subset _ _
  have hpt : ∀ s ∈ π.parts.powersetCard 2, sfsCladeTerm (mergeBlocks π s) A =
      (if s ⊆ cladeInside π A then
          sfsCladeCoeff (π.parts.card - 1) ((cladeInside π A).card - 1) else 0) +
        (if s ⊆ π.parts \ cladeInside π A then
          sfsCladeCoeff (π.parts.card - 1) (cladeInside π A).card else 0) := by
    intro s hs
    rw [Finset.mem_powersetCard] at hs
    obtain ⟨hs, hc⟩ := hs
    have hne : s.Nonempty := Finset.card_pos.mp (by omega)
    have hk := card_parts_mergeBlocks hs hc
    by_cases h1 : s ⊆ cladeInside π A
    · obtain ⟨hsat', hcard⟩ := cladeSaturated_mergeBlocks_inside hsat hs hc h1
      have h2 : ¬ s ⊆ π.parts \ cladeInside π A := by
        obtain ⟨b, hb⟩ := hne
        exact fun h => (Finset.mem_sdiff.mp (h hb)).2 (h1 hb)
      rw [ite_eq_left h1, ite_eq_right h2, add_zero, sfsCladeTerm, ite_eq_left hsat',
        show (mergeBlocks π s).parts.card = π.parts.card - 1 by omega,
        show (cladeInside (mergeBlocks π s) A).card = (cladeInside π A).card - 1 by omega]
    · by_cases h2 : s ⊆ π.parts \ cladeInside π A
      · have hout : ∀ b ∈ s, ¬ b ⊆ A := fun b hb hbA =>
          (Finset.mem_sdiff.mp (h2 hb)).2 (Finset.mem_filter.mpr ⟨hs hb, hbA⟩)
        obtain ⟨hsat', hins⟩ := cladeSaturated_mergeBlocks_outside hsat hs hne hout
        rw [ite_eq_right h1, ite_eq_left h2, zero_add, sfsCladeTerm, ite_eq_left hsat', hins,
          show (mergeBlocks π s).parts.card = π.parts.card - 1 by omega]
      · obtain ⟨b, hb, hbI⟩ := Finset.not_subset.mp h1
        obtain ⟨a, ha, haO⟩ := Finset.not_subset.mp h2
        have hbA : ¬ b ⊆ A := fun h => hbI (Finset.mem_filter.mpr ⟨hs hb, h⟩)
        have haA : a ⊆ A := by
          by_contra h
          exact haO (Finset.mem_sdiff.mpr ⟨hs ha, fun hI => h (Finset.mem_filter.mp hI).2⟩)
        rw [ite_eq_right h1, ite_eq_right h2, add_zero, sfsCladeTerm,
          ite_eq_right (not_cladeSaturated_mergeBlocks_mixed hs ha haA hb hbA)]
  have hf1 : (π.parts.powersetCard 2).filter (· ⊆ cladeInside π A) =
      (cladeInside π A).powersetCard 2 := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨h.1.trans hInP, h.2⟩, h.1⟩⟩
  have hf2 : (π.parts.powersetCard 2).filter (· ⊆ π.parts \ cladeInside π A) =
      (π.parts \ cladeInside π A).powersetCard 2 := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨h.1.trans Finset.sdiff_subset, h.2⟩, h.1⟩⟩
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, ← Finset.sum_filter,
    ← Finset.sum_filter, hf1, hf2, Finset.sum_const, Finset.sum_const, nsmul_eq_mul,
    nsmul_eq_mul, Finset.card_powersetCard, Finset.card_powersetCard,
    Finset.card_sdiff_of_subset hInP]

/-- Source: fu1995, eq. 22. -/
theorem sum_sfsCladeTerm_increment {π : Finpartition (Finset.univ : Finset (Fin n))}
    (hk : 2 ≤ π.parts.card) (A : Finset (Fin n)) :
    ∑ s ∈ π.parts.powersetCard 2, (sfsCladeTerm (mergeBlocks π s) A - sfsCladeTerm π A) =
      -(if A ∈ π.parts then (1 : ℝ) else 0) := by
  by_cases hsat : CladeSaturated π A
  · have hInP : cladeInside π A ⊆ π.parts := Finset.filter_subset _ _
    have hm := Finset.card_le_card hInP
    rw [Finset.sum_sub_distrib, sum_sfsCladeTerm_mergeBlocks hsat, Finset.sum_const,
      nsmul_eq_mul, Finset.card_powersetCard, sfsCladeCoeff_step hk hm, sfsCladeTerm,
      ite_eq_left hsat]
    have hiff : A ∈ π.parts ↔ (cladeInside π A).card = 1 := by
      rw [mem_parts_iff_cladeSaturated_card]
      exact ⟨fun h => h.2, fun h => ⟨hsat, h⟩⟩
    by_cases h1 : (cladeInside π A).card = 1
    · rw [ite_eq_left h1, ite_eq_left (hiff.mpr h1)]
      ring
    · rw [ite_eq_right h1, ite_eq_right (fun h => h1 (hiff.mp h))]
      ring
  · have hA : A ∉ π.parts := fun h =>
      hsat ((mem_parts_iff_cladeSaturated_card π A).mp h).1
    rw [ite_eq_right hA, neg_zero]
    apply Finset.sum_eq_zero
    intro s _
    rw [sfsCladeTerm, ite_eq_right (not_cladeSaturated_mergeBlocks hsat s), sfsCladeTerm,
      ite_eq_right hsat, sub_zero]

/-- Source: fu1995, eq. 22. -/
theorem sfsWeightPotential_generator (w : Finset (Fin n) → ℝ)
    {π : Finpartition (Finset.univ : Finset (Fin n))} (hk : 2 ≤ π.parts.card) :
    ∑ σ, (partitionChain (Fin n)).Q π σ * sfsWeightPotential w σ =
      -blockWeightReward w π := by
  rw [sum_partitionQ_reward]
  unfold sfsWeightPotential blockWeightReward
  simp_rw [← Finset.sum_sub_distrib, ← mul_sub]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_sfsCladeTerm_increment hk]
  simp only [mul_neg, mul_ite, mul_one, mul_zero, Finset.sum_neg_distrib, neg_inj]
  rw [← Finset.sum_filter]
  congr 1
  ext B
  simp

theorem sfsWeightPotential_coalesced (w : Finset (Fin n) → ℝ)
    {π : Finpartition (Finset.univ : Finset (Fin n))}
    (hπ : π ∈ coalescedPartitions (Fin n)) : sfsWeightPotential w π = 0 := by
  unfold sfsWeightPotential
  apply Finset.sum_eq_zero
  intro A _
  rw [sfsCladeTerm, sfsCladeCoeff_of_le_one (mem_coalescedPartitions.mp hπ)]
  simp

/-- Source: fu1995, eq. 22. -/
theorem sfsWeightPotential_eq_expectedCost (w : Finset (Fin n) → ℝ) :
    sfsWeightPotential w = (partitionChain (Fin n)).expectedCost
      (coalescedPartitions (Fin n)) (blockWeightReward w) := by
  apply Rhone.MarkovChain.RateChain.eq_expectedCost_of_generator
    (partitionChain_coalesced_isAbsorbingSet n) (partitionChain_coalesced_reaches n)
    (fun π hπ => (partitionChain_transient_rate_pos n π hπ).ne')
  · intro π hπ
    exact sfsWeightPotential_coalesced w hπ
  · intro π hπ
    have hk : 2 ≤ π.parts.card := by
      have := mt mem_coalescedPartitions.mpr hπ
      omega
    exact sfsWeightPotential_generator w hk

/-- Source: fu1995, eq. 22. -/
theorem sfsWeightPotential_bot (w : Finset (Fin n) → ℝ) :
    sfsWeightPotential w (⊥ : Finpartition (Finset.univ : Finset (Fin n))) =
      ∑ A : Finset (Fin n), w A * sfsCladeCoeff n A.card := by
  unfold sfsWeightPotential
  apply Finset.sum_congr rfl
  intro A _
  have hsat : CladeSaturated (⊥ : Finpartition (Finset.univ : Finset (Fin n))) A := by
    intro B hB
    obtain ⟨x, -, rfl⟩ := Finpartition.mem_bot_iff.mp hB
    by_cases hx : x ∈ A
    · exact Or.inl (Finset.singleton_subset_iff.mpr hx)
    · exact Or.inr (Finset.disjoint_singleton_left.mpr hx)
  have hin : cladeInside (⊥ : Finpartition (Finset.univ : Finset (Fin n))) A =
      A.map ⟨singleton, Finset.singleton_injective⟩ := by
    ext B
    simp only [cladeInside, Finset.mem_filter, Finpartition.mem_bot_iff, Finset.mem_univ,
      true_and, Finset.mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨⟨x, rfl⟩, hx⟩
      exact ⟨x, Finset.singleton_subset_iff.mp hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, rfl⟩, Finset.singleton_subset_iff.mpr hx⟩
  have hcard : (⊥ : Finpartition (Finset.univ : Finset (Fin n))).parts.card = n := by simp
  rw [sfsCladeTerm, ite_eq_left hsat, hin, Finset.card_map, hcard]

/-- Source: fu1995, eq. 22. -/
theorem lintegral_kingmanFiniteReward_blockWeight {w : Finset (Fin n) → ℝ}
    (hw : ∀ B, 0 ≤ w B) :
    ∫⁻ h, ENNReal.ofReal (kingmanFiniteReward n (blockWeightReward w) h)
      ∂(partitionChain (Fin n)).jumpHoldLaw ⊥ =
    ENNReal.ofReal (∑ A : Finset (Fin n), w A * sfsCladeCoeff n A.card) := by
  rw [← sfsWeightPotential_bot w, sfsWeightPotential_eq_expectedCost w,
    ← (partitionChain (Fin n)).lintegral_costBefore
      (partitionChain_coalesced_isAbsorbingSet n) (partitionChain_coalesced_reaches n)
      (blockWeightReward_nonneg hw)]
  apply lintegral_congr_ae
  filter_upwards [partition_costBefore_eq_finite_clamped_sum n
    (blockWeightReward w) (blockWeightReward_nonneg hw)] with h hh
  exact hh.symm

theorem integrable_kingmanFiniteReward_blockWeight {w : Finset (Fin n) → ℝ}
    (hw : ∀ B, 0 ≤ w B) :
    Integrable (kingmanFiniteReward n (blockWeightReward w))
      ((partitionChain (Fin n)).jumpHoldLaw ⊥) := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    (measurable_kingmanFiniteReward n _).aestronglyMeasurable
    (Eventually.of_forall (kingmanFiniteReward_nonneg n _ (blockWeightReward_nonneg hw)))).mp
  rw [lintegral_kingmanFiniteReward_blockWeight hw]
  exact ENNReal.ofReal_ne_top

/-- Source: fu1995, eq. 22. -/
theorem integral_kingmanFiniteReward_blockWeight {w : Finset (Fin n) → ℝ}
    (hw : ∀ B, 0 ≤ w B) :
    ∫ h, kingmanFiniteReward n (blockWeightReward w) h
      ∂(partitionChain (Fin n)).jumpHoldLaw ⊥ =
    ∑ A : Finset (Fin n), w A * sfsCladeCoeff n A.card := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall (kingmanFiniteReward_nonneg n _ (blockWeightReward_nonneg hw)))
    (measurable_kingmanFiniteReward n _).aestronglyMeasurable,
    lintegral_kingmanFiniteReward_blockWeight hw,
    ENNReal.toReal_ofReal (Finset.sum_nonneg fun A _ =>
      mul_nonneg (hw A) (sfsCladeCoeff_nonneg n A.card))]

end Rhone.Coalescent
