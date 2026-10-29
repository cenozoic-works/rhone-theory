/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Statistics.SfsVarianceCoeff
public import Rhone.Statistics.SfsMarkedSpectrum
public import Rhone.Statistics.TajimaDCrossMoment

/-!
# Reward potential for the SFS second moment from clade square and pair terms

Source: fu1995, eq. (23)–(24), (28), (31), pp. 182–187; durrett2008, Thm 2.2. -/

@[expose] public section
namespace Rhone.Statistics

open MeasureTheory ProbabilityTheory Finset Coalescent Rhone.Combinatorics MarkovChain Filter

variable {n : ℕ}

noncomputable def sfsCladeSqTerm (π : Finpartition (Finset.univ : Finset (Fin n)))
    (A : Finset (Fin n)) : ℝ :=
  if CladeSaturated π A then sfsCladeSqCoeff π.parts.card (cladeInside π A).card else 0

noncomputable def sfsCladePairTerm (π : Finpartition (Finset.univ : Finset (Fin n)))
    (A B : Finset (Fin n)) : ℝ :=
  if CladeSaturated π A ∧ CladeSaturated π B then
    sfsCladePairCoeff π.parts.card (cladeInside π A).card (cladeInside π B).card
  else 0

noncomputable def sfsSecondPotential (i : ℕ)
    (π : Finpartition (Finset.univ : Finset (Fin n))) : ℝ :=
  ∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard i, sfsCladeSqTerm π A +
    ∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard i,
      ∑ B ∈ (Finset.univ : Finset (Fin n)).powersetCard i,
        if Disjoint A B then sfsCladePairTerm π A B else 0

private theorem filter_subset_powersetCard_two {α : Type*} [DecidableEq α]
    {P T : Finset α} (hT : T ⊆ P) :
    (P.powersetCard 2).filter (· ⊆ T) = T.powersetCard 2 := by
  ext s
  simp only [Finset.mem_filter, Finset.mem_powersetCard]
  exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨h.1.trans hT, h.2⟩, h.1⟩⟩

theorem sum_sfsCladeSqTerm_mergeBlocks {π : Finpartition (Finset.univ : Finset (Fin n))}
    {A : Finset (Fin n)} (hsat : CladeSaturated π A) :
    ∑ s ∈ π.parts.powersetCard 2, sfsCladeSqTerm (mergeBlocks π s) A =
      ((cladeInside π A).card.choose 2 : ℝ) *
          sfsCladeSqCoeff (π.parts.card - 1) ((cladeInside π A).card - 1) +
        ((π.parts.card - (cladeInside π A).card).choose 2 : ℝ) *
          sfsCladeSqCoeff (π.parts.card - 1) (cladeInside π A).card := by
  have hInP : cladeInside π A ⊆ π.parts := Finset.filter_subset _ _
  have hpt : ∀ s ∈ π.parts.powersetCard 2, sfsCladeSqTerm (mergeBlocks π s) A =
      (if s ⊆ cladeInside π A then
          sfsCladeSqCoeff (π.parts.card - 1) ((cladeInside π A).card - 1) else 0) +
        (if s ⊆ π.parts \ cladeInside π A then
          sfsCladeSqCoeff (π.parts.card - 1) (cladeInside π A).card else 0) := by
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
      rw [ite_eq_left h1, ite_eq_right h2, add_zero, sfsCladeSqTerm, ite_eq_left hsat',
        show (mergeBlocks π s).parts.card = π.parts.card - 1 by omega,
        show (cladeInside (mergeBlocks π s) A).card = (cladeInside π A).card - 1 by omega]
    · by_cases h2 : s ⊆ π.parts \ cladeInside π A
      · have hout : ∀ b ∈ s, ¬ b ⊆ A := fun b hb hbA =>
          (Finset.mem_sdiff.mp (h2 hb)).2 (Finset.mem_filter.mpr ⟨hs hb, hbA⟩)
        obtain ⟨hsat', hins⟩ := cladeSaturated_mergeBlocks_outside hsat hs hne hout
        rw [ite_eq_right h1, ite_eq_left h2, zero_add, sfsCladeSqTerm, ite_eq_left hsat', hins,
          show (mergeBlocks π s).parts.card = π.parts.card - 1 by omega]
      · obtain ⟨b, hb, hbI⟩ := Finset.not_subset.mp h1
        obtain ⟨a, ha, haO⟩ := Finset.not_subset.mp h2
        have hbA : ¬ b ⊆ A := fun h => hbI (Finset.mem_filter.mpr ⟨hs hb, h⟩)
        have haA : a ⊆ A := by
          by_contra h
          exact haO (Finset.mem_sdiff.mpr ⟨hs ha, fun hI => h (Finset.mem_filter.mp hI).2⟩)
        rw [ite_eq_right h1, ite_eq_right h2, add_zero, sfsCladeSqTerm,
          ite_eq_right (not_cladeSaturated_mergeBlocks_mixed hs ha haA hb hbA)]
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, ← Finset.sum_filter,
    ← Finset.sum_filter, filter_subset_powersetCard_two hInP,
    filter_subset_powersetCard_two Finset.sdiff_subset, Finset.sum_const, Finset.sum_const,
    nsmul_eq_mul, nsmul_eq_mul, Finset.card_powersetCard, Finset.card_powersetCard,
    Finset.card_sdiff_of_subset hInP]

theorem sum_sfsCladeSqTerm_increment {π : Finpartition (Finset.univ : Finset (Fin n))}
    (hk : 2 ≤ π.parts.card) (A : Finset (Fin n)) :
    ∑ s ∈ π.parts.powersetCard 2, (sfsCladeSqTerm (mergeBlocks π s) A - sfsCladeSqTerm π A) =
      -(if A ∈ π.parts then 2 * sfsCladeTerm π A else 0) := by
  by_cases hsat : CladeSaturated π A
  · have hInP : cladeInside π A ⊆ π.parts := Finset.filter_subset _ _
    have hm := Finset.card_le_card hInP
    rw [Finset.sum_sub_distrib, sum_sfsCladeSqTerm_mergeBlocks hsat, Finset.sum_const,
      nsmul_eq_mul, Finset.card_powersetCard, sfsCladeSqCoeff_step hk hm, sfsCladeSqTerm,
      ite_eq_left hsat]
    have hiff : A ∈ π.parts ↔ (cladeInside π A).card = 1 := by
      rw [mem_parts_iff_cladeSaturated_card]
      exact ⟨fun h => h.2, fun h => ⟨hsat, h⟩⟩
    by_cases h1 : (cladeInside π A).card = 1
    · rw [ite_eq_left h1, ite_eq_left (hiff.mpr h1), sfsCladeTerm, ite_eq_left hsat, h1]
      ring
    · rw [ite_eq_right h1, ite_eq_right (fun h => h1 (hiff.mp h))]
      ring
  · have hA : A ∉ π.parts := fun h =>
      hsat ((mem_parts_iff_cladeSaturated_card π A).mp h).1
    rw [ite_eq_right hA, neg_zero]
    apply Finset.sum_eq_zero
    intro s _
    rw [sfsCladeSqTerm, ite_eq_right (not_cladeSaturated_mergeBlocks hsat s), sfsCladeSqTerm,
      ite_eq_right hsat, sub_zero]

theorem card_cladeInside_pos {π : Finpartition (Finset.univ : Finset (Fin n))}
    {A : Finset (Fin n)} (hsat : CladeSaturated π A) (hne : A.Nonempty) :
    1 ≤ (cladeInside π A).card := by
  obtain ⟨x, hx⟩ := hne
  have hxp : π.part x ∈ π.parts := π.part_mem.2 (Finset.mem_univ x)
  have hxx : x ∈ π.part x := π.mem_part (Finset.mem_univ x)
  have hsub : π.part x ⊆ A := by
    rcases hsat _ hxp with h | h
    · exact h
    · exact absurd hx ((Finset.disjoint_left.mp h) hxx)
  exact Finset.card_pos.mpr ⟨π.part x, Finset.mem_filter.mpr ⟨hxp, hsub⟩⟩

theorem disjoint_cladeInside {π : Finpartition (Finset.univ : Finset (Fin n))}
    {A B : Finset (Fin n)} (hAB : Disjoint A B) :
    Disjoint (cladeInside π A) (cladeInside π B) := by
  rw [Finset.disjoint_left]
  intro x hxA hxB
  have h1 := Finset.mem_filter.mp hxA
  have h2 := Finset.mem_filter.mp hxB
  obtain ⟨y, hy⟩ := π.nonempty_of_mem_parts h1.1
  exact (Finset.disjoint_left.mp hAB) (h1.2 hy) (h2.2 hy)

theorem sum_sfsCladePairTerm_mergeBlocks {π : Finpartition (Finset.univ : Finset (Fin n))}
    {A B : Finset (Fin n)} (hA : CladeSaturated π A) (hB : CladeSaturated π B)
    (hAB : Disjoint A B) :
    ∑ s ∈ π.parts.powersetCard 2, sfsCladePairTerm (mergeBlocks π s) A B =
      ((cladeInside π A).card.choose 2 : ℝ) *
          sfsCladePairCoeff (π.parts.card - 1) ((cladeInside π A).card - 1)
            (cladeInside π B).card +
        ((cladeInside π B).card.choose 2 : ℝ) *
          sfsCladePairCoeff (π.parts.card - 1) (cladeInside π A).card
            ((cladeInside π B).card - 1) +
        ((π.parts.card - (cladeInside π A).card - (cladeInside π B).card).choose 2 : ℝ) *
          sfsCladePairCoeff (π.parts.card - 1) (cladeInside π A).card
            (cladeInside π B).card := by
  have hInA : cladeInside π A ⊆ π.parts := Finset.filter_subset _ _
  have hInB : cladeInside π B ⊆ π.parts := Finset.filter_subset _ _
  have hdisj := disjoint_cladeInside (π := π) hAB
  have hnotB : ∀ x ∈ π.parts, x ⊆ A → ¬ x ⊆ B := by
    intro x hx hxA hxB
    obtain ⟨y, hy⟩ := π.nonempty_of_mem_parts hx
    exact (Finset.disjoint_left.mp hAB) (hxA hy) (hxB hy)
  have hpt : ∀ s ∈ π.parts.powersetCard 2, sfsCladePairTerm (mergeBlocks π s) A B =
      (if s ⊆ cladeInside π A then
          sfsCladePairCoeff (π.parts.card - 1) ((cladeInside π A).card - 1)
            (cladeInside π B).card else 0) +
        (if s ⊆ cladeInside π B then
          sfsCladePairCoeff (π.parts.card - 1) (cladeInside π A).card
            ((cladeInside π B).card - 1) else 0) +
        (if s ⊆ π.parts \ (cladeInside π A ∪ cladeInside π B) then
          sfsCladePairCoeff (π.parts.card - 1) (cladeInside π A).card
            (cladeInside π B).card else 0) := by
    intro s hs
    rw [Finset.mem_powersetCard] at hs
    obtain ⟨hs, hc⟩ := hs
    have hne : s.Nonempty := Finset.card_pos.mp (by omega)
    have hk := card_parts_mergeBlocks hs hc
    by_cases h1 : s ⊆ cladeInside π A
    · obtain ⟨hsatA, hcardA⟩ := cladeSaturated_mergeBlocks_inside hA hs hc h1
      have houtB : ∀ x ∈ s, ¬ x ⊆ B := fun x hx =>
        hnotB x (hs hx) (Finset.mem_filter.mp (h1 hx)).2
      obtain ⟨hsatB, hinsB⟩ := cladeSaturated_mergeBlocks_outside hB hs hne houtB
      have h2 : ¬ s ⊆ cladeInside π B := by
        obtain ⟨x, hx⟩ := hne
        exact fun h => houtB x hx (Finset.mem_filter.mp (h hx)).2
      have h3 : ¬ s ⊆ π.parts \ (cladeInside π A ∪ cladeInside π B) := by
        obtain ⟨x, hx⟩ := hne
        exact fun h => (Finset.mem_sdiff.mp (h hx)).2 (Finset.mem_union_left _ (h1 hx))
      rw [ite_eq_left h1, ite_eq_right h2, ite_eq_right h3, add_zero, add_zero,
        sfsCladePairTerm, ite_eq_left ⟨hsatA, hsatB⟩, hinsB,
        show (mergeBlocks π s).parts.card = π.parts.card - 1 by omega,
        show (cladeInside (mergeBlocks π s) A).card = (cladeInside π A).card - 1 by omega]
    · by_cases h2 : s ⊆ cladeInside π B
      · obtain ⟨hsatB, hcardB⟩ := cladeSaturated_mergeBlocks_inside hB hs hc h2
        have houtA : ∀ x ∈ s, ¬ x ⊆ A := fun x hx hxA =>
          hnotB x (hs hx) hxA (Finset.mem_filter.mp (h2 hx)).2
        obtain ⟨hsatA, hinsA⟩ := cladeSaturated_mergeBlocks_outside hA hs hne houtA
        have h3 : ¬ s ⊆ π.parts \ (cladeInside π A ∪ cladeInside π B) := by
          obtain ⟨x, hx⟩ := hne
          exact fun h => (Finset.mem_sdiff.mp (h hx)).2 (Finset.mem_union_right _ (h2 hx))
        rw [ite_eq_right h1, ite_eq_left h2, ite_eq_right h3, zero_add, add_zero,
          sfsCladePairTerm, ite_eq_left ⟨hsatA, hsatB⟩, hinsA,
          show (mergeBlocks π s).parts.card = π.parts.card - 1 by omega,
          show (cladeInside (mergeBlocks π s) B).card = (cladeInside π B).card - 1 by omega]
      · by_cases h3 : s ⊆ π.parts \ (cladeInside π A ∪ cladeInside π B)
        · have houtA : ∀ x ∈ s, ¬ x ⊆ A := fun x hx hxA =>
            (Finset.mem_sdiff.mp (h3 hx)).2
              (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hs hx, hxA⟩))
          have houtB : ∀ x ∈ s, ¬ x ⊆ B := fun x hx hxB =>
            (Finset.mem_sdiff.mp (h3 hx)).2
              (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hs hx, hxB⟩))
          obtain ⟨hsatA, hinsA⟩ := cladeSaturated_mergeBlocks_outside hA hs hne houtA
          obtain ⟨hsatB, hinsB⟩ := cladeSaturated_mergeBlocks_outside hB hs hne houtB
          rw [ite_eq_right h1, ite_eq_right h2, ite_eq_left h3, zero_add, zero_add,
            sfsCladePairTerm, ite_eq_left ⟨hsatA, hsatB⟩, hinsA, hinsB,
            show (mergeBlocks π s).parts.card = π.parts.card - 1 by omega]
        · have hmixed : ¬ (CladeSaturated (mergeBlocks π s) A ∧
              CladeSaturated (mergeBlocks π s) B) := by
            rintro ⟨hsA, hsB⟩
            by_cases hxA : ∃ x ∈ s, x ⊆ A
            · obtain ⟨x, hx, hxA⟩ := hxA
              obtain ⟨y, hy, hyI⟩ := Finset.not_subset.mp h1
              have hyA : ¬ y ⊆ A := fun h => hyI (Finset.mem_filter.mpr ⟨hs hy, h⟩)
              exact not_cladeSaturated_mergeBlocks_mixed hs hx hxA hy hyA hsA
            · by_cases hxB : ∃ x ∈ s, x ⊆ B
              · obtain ⟨x, hx, hxB⟩ := hxB
                obtain ⟨y, hy, hyI⟩ := Finset.not_subset.mp h2
                have hyB : ¬ y ⊆ B := fun h => hyI (Finset.mem_filter.mpr ⟨hs hy, h⟩)
                exact not_cladeSaturated_mergeBlocks_mixed hs hx hxB hy hyB hsB
              · apply h3
                intro x hx
                rw [Finset.mem_sdiff]
                refine ⟨hs hx, fun hu => ?_⟩
                rcases Finset.mem_union.mp hu with h | h
                · exact hxA ⟨x, hx, (Finset.mem_filter.mp h).2⟩
                · exact hxB ⟨x, hx, (Finset.mem_filter.mp h).2⟩
          rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, add_zero, add_zero,
            sfsCladePairTerm, ite_eq_right hmixed]
  have hR : (π.parts \ (cladeInside π A ∪ cladeInside π B)).card =
      π.parts.card - (cladeInside π A).card - (cladeInside π B).card := by
    rw [Finset.card_sdiff_of_subset (Finset.union_subset hInA hInB),
      Finset.card_union_of_disjoint hdisj, Nat.sub_sub]
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.sum_filter, ← Finset.sum_filter, ← Finset.sum_filter,
    filter_subset_powersetCard_two hInA, filter_subset_powersetCard_two hInB,
    filter_subset_powersetCard_two Finset.sdiff_subset, Finset.sum_const, Finset.sum_const,
    Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul, Finset.card_powersetCard,
    Finset.card_powersetCard, Finset.card_powersetCard, hR]

theorem sum_sfsCladePairTerm_increment {π : Finpartition (Finset.univ : Finset (Fin n))}
    {A B : Finset (Fin n)} (hAB : Disjoint A B)
    (hAne : A.Nonempty) (hBne : B.Nonempty) :
    ∑ s ∈ π.parts.powersetCard 2,
        (sfsCladePairTerm (mergeBlocks π s) A B - sfsCladePairTerm π A B) =
      -((if A ∈ π.parts then sfsCladeTerm π B else 0) +
        (if B ∈ π.parts then sfsCladeTerm π A else 0)) := by
  by_cases h : CladeSaturated π A ∧ CladeSaturated π B
  · obtain ⟨hA, hB⟩ := h
    have ha := card_cladeInside_pos hA hAne
    have hb := card_cladeInside_pos hB hBne
    have hab : (cladeInside π A).card + (cladeInside π B).card ≤ π.parts.card := by
      rw [← Finset.card_union_of_disjoint (disjoint_cladeInside hAB)]
      exact Finset.card_le_card
        (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
    have hiffA : A ∈ π.parts ↔ (cladeInside π A).card = 1 := by
      rw [mem_parts_iff_cladeSaturated_card]
      exact ⟨fun h => h.2, fun h => ⟨hA, h⟩⟩
    have hiffB : B ∈ π.parts ↔ (cladeInside π B).card = 1 := by
      rw [mem_parts_iff_cladeSaturated_card]
      exact ⟨fun h => h.2, fun h => ⟨hB, h⟩⟩
    have hgA : sfsCladeTerm π A = sfsCladeCoeff π.parts.card (cladeInside π A).card := by
      rw [sfsCladeTerm, ite_eq_left hA]
    have hgB : sfsCladeTerm π B = sfsCladeCoeff π.parts.card (cladeInside π B).card := by
      rw [sfsCladeTerm, ite_eq_left hB]
    rw [Finset.sum_sub_distrib, sum_sfsCladePairTerm_mergeBlocks hA hB hAB, Finset.sum_const,
      nsmul_eq_mul, Finset.card_powersetCard, sfsCladePairCoeff_step ha hb hab,
      sfsCladePairTerm, ite_eq_left (And.intro hA hB), hgA, hgB, if_congr hiffA rfl rfl,
      if_congr hiffB rfl rfl]
    ring
  · have hz : ∀ s, sfsCladePairTerm (mergeBlocks π s) A B = 0 := by
      intro s
      rw [sfsCladePairTerm, ite_eq_right]
      rintro ⟨h1, h2⟩
      apply h
      constructor
      · by_contra hn
        exact not_cladeSaturated_mergeBlocks hn s h1
      · by_contra hn
        exact not_cladeSaturated_mergeBlocks hn s h2
    have h0 : sfsCladePairTerm π A B = 0 := by rw [sfsCladePairTerm, ite_eq_right h]
    have r1 : (if A ∈ π.parts then sfsCladeTerm π B else 0) = 0 := by
      split_ifs with hm
      · have hsA := ((mem_parts_iff_cladeSaturated_card π A).mp hm).1
        rw [sfsCladeTerm, ite_eq_right (fun hsB => h ⟨hsA, hsB⟩)]
      · rfl
    have r2 : (if B ∈ π.parts then sfsCladeTerm π A else 0) = 0 := by
      split_ifs with hm
      · have hsB := ((mem_parts_iff_cladeSaturated_card π B).mp hm).1
        rw [sfsCladeTerm, ite_eq_right (fun hsA => h ⟨hsA, hsB⟩)]
      · rfl
    rw [r1, r2, add_zero, neg_zero]
    apply Finset.sum_eq_zero
    intro s _
    rw [hz, h0, sub_zero]

theorem sfsBlockCount_eq_sum_powersetCard (i : ℕ)
    (π : Finpartition (Finset.univ : Finset (Fin n))) :
    sfsBlockCount n i π =
      ∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard i,
        if A ∈ π.parts then (1 : ℝ) else 0 := by
  unfold sfsBlockCount
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  congr 1
  ext B
  simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
  exact and_comm

/-- Source: fu1995, eq. 22. -/
theorem sfsWeightPotential_indicator (i : ℕ)
    (π : Finpartition (Finset.univ : Finset (Fin n))) :
    sfsWeightPotential (fun B : Finset (Fin n) => if B.card = i then (1 : ℝ) else 0) π =
      ∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard i, sfsCladeTerm π A := by
  unfold sfsWeightPotential
  simp only [ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  congr 1
  ext B
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powersetCard,
    Finset.subset_univ]

theorem sfsCladeTerm_split_of_mem_parts {π : Finpartition (Finset.univ : Finset (Fin n))}
    {A B : Finset (Fin n)} (hA : A ∈ π.parts) (hcard : B.card = A.card) :
    sfsCladeTerm π B =
      (if A = B then sfsCladeTerm π B else 0) +
        (if Disjoint A B then sfsCladeTerm π B else 0) := by
  by_cases hAB : A = B
  · subst hAB
    have hne := π.nonempty_of_mem_parts hA
    have hd : ¬ Disjoint A A := fun h => hne.ne_empty ((Finset.disjoint_self_iff_empty A).mp h)
    rw [ite_eq_left rfl, ite_eq_right hd, add_zero]
  · by_cases hd : Disjoint A B
    · rw [ite_eq_right hAB, ite_eq_left hd, zero_add]
    · have hns : ¬ CladeSaturated π B := by
        intro hs
        rcases hs A hA with h | h
        · exact hAB (Finset.eq_of_subset_of_card_le h hcard.le)
        · exact hd h
      rw [ite_eq_right hAB, ite_eq_right hd, add_zero, sfsCladeTerm, ite_eq_right hns]

theorem sfsSecondPotential_generator {i : ℕ} (hi : 1 ≤ i)
    {π : Finpartition (Finset.univ : Finset (Fin n))} (hk : 2 ≤ π.parts.card) :
    ∑ σ, (partitionChain (Fin n)).Q π σ * sfsSecondPotential i σ =
      -(2 * sfsBlockCount n i π *
        sfsWeightPotential (fun B : Finset (Fin n) => if B.card = i then (1 : ℝ) else 0) π) := by
  have hne : ∀ A ∈ (Finset.univ : Finset (Fin n)).powersetCard i, A.Nonempty := by
    intro A hA
    exact Finset.card_pos.mp (by rw [(Finset.mem_powersetCard.mp hA).2]; omega)
  have hsq : ∑ s ∈ π.parts.powersetCard 2,
      (∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard i,
          sfsCladeSqTerm (mergeBlocks π s) A -
        ∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard i, sfsCladeSqTerm π A) =
      -(2 * ∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard i,
        if A ∈ π.parts then sfsCladeTerm π A else 0) := by
    simp_rw [← Finset.sum_sub_distrib]
    rw [Finset.sum_comm, Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro A _
    rw [sum_sfsCladeSqTerm_increment hk, mul_ite, mul_zero]
  have hpair : ∑ s ∈ π.parts.powersetCard 2,
      (∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard i,
          ∑ B ∈ (Finset.univ : Finset (Fin n)).powersetCard i,
            (if Disjoint A B then sfsCladePairTerm (mergeBlocks π s) A B else 0) -
        ∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard i,
          ∑ B ∈ (Finset.univ : Finset (Fin n)).powersetCard i,
            (if Disjoint A B then sfsCladePairTerm π A B else 0)) =
      -(∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard i,
          ∑ B ∈ (Finset.univ : Finset (Fin n)).powersetCard i,
            (if Disjoint A B then (if A ∈ π.parts then sfsCladeTerm π B else 0) else 0) +
        ∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard i,
          ∑ B ∈ (Finset.univ : Finset (Fin n)).powersetCard i,
            (if Disjoint A B then (if B ∈ π.parts then sfsCladeTerm π A else 0) else 0)) := by
    simp_rw [← Finset.sum_sub_distrib]
    rw [Finset.sum_comm, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro A hA
    rw [Finset.sum_comm, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro B hB
    by_cases hd : Disjoint A B
    · simp only [hd, ↓reduceIte]
      rw [sum_sfsCladePairTerm_increment hd (hne A hA) (hne B hB)]
    · simp only [hd, ↓reduceIte, sub_self, Finset.sum_const_zero, add_zero, neg_zero]
  have hsymm : ∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard i,
        ∑ B ∈ (Finset.univ : Finset (Fin n)).powersetCard i,
          (if Disjoint A B then (if B ∈ π.parts then sfsCladeTerm π A else 0) else 0) =
      ∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard i,
        ∑ B ∈ (Finset.univ : Finset (Fin n)).powersetCard i,
          (if Disjoint A B then (if A ∈ π.parts then sfsCladeTerm π B else 0) else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro A _
    apply Finset.sum_congr rfl
    intro B _
    exact if_congr disjoint_comm rfl rfl
  have hprod : sfsBlockCount n i π *
      sfsWeightPotential (fun B : Finset (Fin n) => if B.card = i then (1 : ℝ) else 0) π =
      ∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard i,
          (if A ∈ π.parts then sfsCladeTerm π A else 0) +
        ∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard i,
          ∑ B ∈ (Finset.univ : Finset (Fin n)).powersetCard i,
            (if Disjoint A B then (if A ∈ π.parts then sfsCladeTerm π B else 0) else 0) := by
    rw [sfsBlockCount_eq_sum_powersetCard, sfsWeightPotential_indicator, Finset.sum_mul,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro A hA
    by_cases hm : A ∈ π.parts
    · simp only [hm, ↓reduceIte, one_mul]
      rw [Finset.sum_congr rfl (fun B hB => sfsCladeTerm_split_of_mem_parts hm
        (((Finset.mem_powersetCard.mp hB).2).trans (Finset.mem_powersetCard.mp hA).2.symm)),
        Finset.sum_add_distrib, Finset.sum_ite_eq, ite_eq_left hA]
    · simp only [hm, ↓reduceIte, zero_mul, ite_self, Finset.sum_const_zero, add_zero]
  rw [sum_partitionQ_reward]
  unfold sfsSecondPotential
  have hsplit : ∀ s ∈ π.parts.powersetCard 2,
      (∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard i,
          sfsCladeSqTerm (mergeBlocks π s) A +
        ∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard i,
          ∑ B ∈ (Finset.univ : Finset (Fin n)).powersetCard i,
            (if Disjoint A B then sfsCladePairTerm (mergeBlocks π s) A B else 0)) -
      (∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard i, sfsCladeSqTerm π A +
        ∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard i,
          ∑ B ∈ (Finset.univ : Finset (Fin n)).powersetCard i,
            (if Disjoint A B then sfsCladePairTerm π A B else 0)) =
      (∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard i,
          sfsCladeSqTerm (mergeBlocks π s) A -
        ∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard i, sfsCladeSqTerm π A) +
      (∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard i,
          ∑ B ∈ (Finset.univ : Finset (Fin n)).powersetCard i,
            (if Disjoint A B then sfsCladePairTerm (mergeBlocks π s) A B else 0) -
        ∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard i,
          ∑ B ∈ (Finset.univ : Finset (Fin n)).powersetCard i,
            (if Disjoint A B then sfsCladePairTerm π A B else 0)) := fun s _ => by ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, hsq, hpair, hsymm, mul_assoc, hprod]
  ring

theorem sfsSecondPotential_coalesced (i : ℕ)
    {π : Finpartition (Finset.univ : Finset (Fin n))}
    (hπ : π ∈ coalescedPartitions (Fin n)) : sfsSecondPotential i π = 0 := by
  have hk := mem_coalescedPartitions.mp hπ
  unfold sfsSecondPotential
  have h1 : ∀ A, sfsCladeSqTerm π A = 0 := by
    intro A
    rw [sfsCladeSqTerm, sfsCladeSqCoeff_of_le_one hk, ite_self]
  have h2 : ∀ A B, sfsCladePairTerm π A B = 0 := by
    intro A B
    rw [sfsCladePairTerm, sfsCladePairCoeff_of_le_one hk, ite_self]
  simp only [h1, h2, ite_self, Finset.sum_const_zero, add_zero]

theorem sfsSecondPotential_eq_expectedCost {i : ℕ} (hi : 1 ≤ i) :
    sfsSecondPotential (n := n) i = (partitionChain (Fin n)).expectedCost
      (coalescedPartitions (Fin n)) (fun π => 2 * sfsBlockCount n i π *
        sfsWeightPotential (fun B : Finset (Fin n) => if B.card = i then (1 : ℝ) else 0) π) := by
  apply Rhone.MarkovChain.RateChain.eq_expectedCost_of_generator
    (partitionChain_coalesced_isAbsorbingSet n) (partitionChain_coalesced_reaches n)
    (fun π hπ => (partitionChain_transient_rate_pos n π hπ).ne')
  · intro π hπ
    exact sfsSecondPotential_coalesced i hπ
  · intro π hπ
    have hk : 2 ≤ π.parts.card := by
      have := mt mem_coalescedPartitions.mpr hπ
      omega
    exact sfsSecondPotential_generator hi hk

private theorem jump_drift_of_eq_expectedCost' (n : ℕ)
    (c u : Finpartition (Finset.univ : Finset (Fin n)) → ℝ)
    (h : u = (partitionChain (Fin n)).expectedCost (coalescedPartitions (Fin n)) c)
    (π : Finpartition (Finset.univ : Finset (Fin n))) :
    u π - (partitionChain (Fin n)).jumpChain.expect u π = kingmanJumpReward n c π := by
  subst h
  have hs := FinChain.potential_step (partitionChain_coalesced_isAbsorbingSet n)
    (partitionChain_coalesced_reaches n)
    (fun σ => c σ / (partitionChain (Fin n)).rate σ) π
  change (partitionChain (Fin n)).expectedCost (coalescedPartitions (Fin n)) c π =
    _ + (partitionChain (Fin n)).jumpChain.expect
      ((partitionChain (Fin n)).expectedCost (coalescedPartitions (Fin n)) c) π at hs
  unfold kingmanJumpReward
  linarith

/-- Source: fu1995, eq. 22. -/
theorem sfsWeightPotential_indicator_jump_drift (n i : ℕ)
    (π : Finpartition (Finset.univ : Finset (Fin n))) :
    sfsWeightPotential (fun B : Finset (Fin n) => if B.card = i then (1 : ℝ) else 0) π -
        (partitionChain (Fin n)).jumpChain.expect
          (sfsWeightPotential (fun B : Finset (Fin n) => if B.card = i then (1 : ℝ) else 0)) π =
      kingmanJumpReward n (sfsBlockCount n i) π :=
  jump_drift_of_eq_expectedCost' n _ _ (sfsWeightPotential_eq_expectedCost _) π

theorem sfsSecondPotential_jump_drift {n i : ℕ} (hi : 1 ≤ i)
    (π : Finpartition (Finset.univ : Finset (Fin n))) :
    sfsSecondPotential i π -
        (partitionChain (Fin n)).jumpChain.expect (sfsSecondPotential i) π =
      kingmanJumpReward n (sfsBlockCount n i) π *
          sfsWeightPotential (fun B : Finset (Fin n) => if B.card = i then (1 : ℝ) else 0) π +
        kingmanJumpReward n (sfsBlockCount n i) π *
          sfsWeightPotential
              (fun B : Finset (Fin n) => if B.card = i then (1 : ℝ) else 0) π := by
  rw [jump_drift_of_eq_expectedCost' n _ _ (sfsSecondPotential_eq_expectedCost hi) π]
  unfold kingmanJumpReward
  split_ifs <;> ring

theorem cladeSaturated_bot (A : Finset (Fin n)) :
    CladeSaturated (⊥ : Finpartition (Finset.univ : Finset (Fin n))) A := by
  intro B hB
  obtain ⟨x, -, rfl⟩ := Finpartition.mem_bot_iff.mp hB
  by_cases hx : x ∈ A
  · exact Or.inl (Finset.singleton_subset_iff.mpr hx)
  · exact Or.inr (Finset.disjoint_singleton_left.mpr hx)

theorem card_cladeInside_bot (A : Finset (Fin n)) :
    (cladeInside (⊥ : Finpartition (Finset.univ : Finset (Fin n))) A).card = A.card := by
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
  rw [hin, Finset.card_map]

theorem sfsSecondPotential_bot (n i : ℕ) :
    sfsSecondPotential i (⊥ : Finpartition (Finset.univ : Finset (Fin n))) =
      (n.choose i : ℝ) * sfsCladeSqCoeff n i +
        (n.choose i : ℝ) * ((n - i).choose i : ℝ) * sfsCladePairCoeff n i i := by
  have hcard : (⊥ : Finpartition (Finset.univ : Finset (Fin n))).parts.card = n := by simp
  have h1 : ∀ A ∈ (Finset.univ : Finset (Fin n)).powersetCard i,
      sfsCladeSqTerm (⊥ : Finpartition (Finset.univ : Finset (Fin n))) A =
        sfsCladeSqCoeff n i := by
    intro A hA
    rw [sfsCladeSqTerm, ite_eq_left (cladeSaturated_bot A), card_cladeInside_bot, hcard,
      (Finset.mem_powersetCard.mp hA).2]
  have h2 : ∀ A ∈ (Finset.univ : Finset (Fin n)).powersetCard i,
      ∑ B ∈ (Finset.univ : Finset (Fin n)).powersetCard i,
        (if Disjoint A B then
          sfsCladePairTerm (⊥ : Finpartition (Finset.univ : Finset (Fin n))) A B else 0) =
        ((n - i).choose i : ℝ) * sfsCladePairCoeff n i i := by
    intro A hA
    have hA' := (Finset.mem_powersetCard.mp hA).2
    have hf : ((Finset.univ : Finset (Fin n)).powersetCard i).filter (fun B => Disjoint A B) =
        ((Finset.univ : Finset (Fin n)) \ A).powersetCard i := by
      ext B
      simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and,
        Finset.subset_sdiff]
      exact ⟨fun h => ⟨h.2.symm, h.1⟩, fun h => ⟨h.2, h.1.symm⟩⟩
    have hterm : ∀ B ∈ ((Finset.univ : Finset (Fin n)) \ A).powersetCard i,
        sfsCladePairTerm (⊥ : Finpartition (Finset.univ : Finset (Fin n))) A B =
          sfsCladePairCoeff n i i := by
      intro B hB
      rw [sfsCladePairTerm, ite_eq_left (And.intro (cladeSaturated_bot A) (cladeSaturated_bot B)),
        card_cladeInside_bot, card_cladeInside_bot, hcard, hA',
        (Finset.mem_powersetCard.mp hB).2]
    rw [← Finset.sum_filter, hf, Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul,
      Finset.card_powersetCard, Finset.card_sdiff_of_subset (Finset.subset_univ A),
      Finset.card_univ, Fintype.card_fin, hA']
  unfold sfsSecondPotential
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_const, Finset.sum_const,
    nsmul_eq_mul, nsmul_eq_mul, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  ring

theorem sfsSecondPotential_bot_eq {n i : ℕ} (hi : 1 ≤ i) (hin : i < n) :
    sfsSecondPotential i (⊥ : Finpartition (Finset.univ : Finset (Fin n))) =
      4 * fuSigmaDiag n i + 4 / (i : ℝ) ^ 2 := by
  rw [sfsSecondPotential_bot, choose_mul_sfsCladeSqCoeff hi hin, choose_mul_sfsCladePairCoeff,
    ← fuSigmaDiag_eq hi]
  ring

/-- Source: fu1995, eq. (31), p. 187; durrett2008, Thm 2.2. -/
theorem integral_kingmanFiniteReward_sfsBlockCount_sq {n i : ℕ} (hi : 1 ≤ i) (hin : i < n) :
    ∫ h, kingmanFiniteReward n (sfsBlockCount n i) h ^ 2
      ∂(partitionChain (Fin n)).jumpHoldLaw ⊥ = 4 * fuSigmaDiag n i + 4 / (i : ℝ) ^ 2 := by
  have hc : ∀ π : Finpartition (Finset.univ : Finset (Fin n)), 0 ≤ sfsBlockCount n i π := by
    intro π
    unfold sfsBlockCount
    exact Finset.sum_nonneg fun B _ => by split_ifs <;> norm_num
  rw [integral_kingmanFiniteReward_sq n _ hc,
    partitionChain_integral_cross_jumpReward n _ _ _ _ (sfsSecondPotential i)
      (sfsWeightPotential_indicator_jump_drift n i) (sfsWeightPotential_indicator_jump_drift n i)
      (sfsSecondPotential_jump_drift hi)
      (fun π hπ => sfsWeightPotential_coalesced _ hπ)
      (fun π hπ => sfsWeightPotential_coalesced _ hπ)
      (fun π hπ => sfsSecondPotential_coalesced i hπ),
    sfsSecondPotential_bot_eq hi hin]

end Rhone.Statistics
