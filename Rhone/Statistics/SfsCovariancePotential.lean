/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Statistics.SfsCovarianceCoeff
public import Rhone.Statistics.SfsVariancePotential

/-!
# Reward potential for SFS covariances from clade-nesting and cross terms

Source: fu1995, eq. (15)–(21), (23)–(31), pp. 178–187; durrett2008, Thm 2.2. -/

@[expose] public section
namespace Rhone.Statistics

open MeasureTheory ProbabilityTheory Finset Coalescent Rhone.Combinatorics MarkovChain Filter

variable {n : ℕ}

noncomputable def cladePairForm (f : ℕ → ℕ → ℕ → ℝ)
    (π : Finpartition (Finset.univ : Finset (Fin n))) (A B : Finset (Fin n)) : ℝ :=
  if CladeSaturated π A ∧ CladeSaturated π B then
    f π.parts.card (cladeInside π A).card (cladeInside π B).card
  else 0

noncomputable def sfsCladeNestTerm (π : Finpartition (Finset.univ : Finset (Fin n)))
    (A C : Finset (Fin n)) : ℝ :=
  cladePairForm sfsCladeNestCoeff π A C

noncomputable def sfsCrossPotential (i j : ℕ)
    (π : Finpartition (Finset.univ : Finset (Fin n))) : ℝ :=
  ∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard i,
    ∑ B ∈ (Finset.univ : Finset (Fin n)).powersetCard j,
      ((if Disjoint A B then sfsCladePairTerm π A B else 0) +
        (if A ⊆ B then sfsCladeNestTerm π A (B \ A) else 0))

private theorem filter_subset_powersetCard_two' {α : Type*} [DecidableEq α]
    {P T : Finset α} (hT : T ⊆ P) :
    (P.powersetCard 2).filter (· ⊆ T) = T.powersetCard 2 := by
  ext s
  simp only [Finset.mem_filter, Finset.mem_powersetCard]
  exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨h.1.trans hT, h.2⟩, h.1⟩⟩

theorem sum_cladePairForm_mergeBlocks (f : ℕ → ℕ → ℕ → ℝ)
    {π : Finpartition (Finset.univ : Finset (Fin n))}
    {A B : Finset (Fin n)} (hA : CladeSaturated π A) (hB : CladeSaturated π B)
    (hAB : Disjoint A B) :
    ∑ s ∈ π.parts.powersetCard 2, cladePairForm f (mergeBlocks π s) A B =
      ((cladeInside π A).card.choose 2 : ℝ) *
          f (π.parts.card - 1) ((cladeInside π A).card - 1) (cladeInside π B).card +
        ((cladeInside π B).card.choose 2 : ℝ) *
          f (π.parts.card - 1) (cladeInside π A).card ((cladeInside π B).card - 1) +
        ((π.parts.card - (cladeInside π A).card - (cladeInside π B).card).choose 2 : ℝ) *
          f (π.parts.card - 1) (cladeInside π A).card (cladeInside π B).card := by
  have hInA : cladeInside π A ⊆ π.parts := Finset.filter_subset _ _
  have hInB : cladeInside π B ⊆ π.parts := Finset.filter_subset _ _
  have hdisj := disjoint_cladeInside (π := π) hAB
  have hnotB : ∀ x ∈ π.parts, x ⊆ A → ¬ x ⊆ B := by
    intro x hx hxA hxB
    obtain ⟨y, hy⟩ := π.nonempty_of_mem_parts hx
    exact (Finset.disjoint_left.mp hAB) (hxA hy) (hxB hy)
  have hpt : ∀ s ∈ π.parts.powersetCard 2, cladePairForm f (mergeBlocks π s) A B =
      (if s ⊆ cladeInside π A then
          f (π.parts.card - 1) ((cladeInside π A).card - 1) (cladeInside π B).card else 0) +
        (if s ⊆ cladeInside π B then
          f (π.parts.card - 1) (cladeInside π A).card ((cladeInside π B).card - 1) else 0) +
        (if s ⊆ π.parts \ (cladeInside π A ∪ cladeInside π B) then
          f (π.parts.card - 1) (cladeInside π A).card (cladeInside π B).card else 0) := by
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
        cladePairForm, ite_eq_left ⟨hsatA, hsatB⟩, hinsB,
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
          cladePairForm, ite_eq_left ⟨hsatA, hsatB⟩, hinsA,
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
            cladePairForm, ite_eq_left ⟨hsatA, hsatB⟩, hinsA, hinsB,
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
            cladePairForm, ite_eq_right hmixed]
  have hR : (π.parts \ (cladeInside π A ∪ cladeInside π B)).card =
      π.parts.card - (cladeInside π A).card - (cladeInside π B).card := by
    rw [Finset.card_sdiff_of_subset (Finset.union_subset hInA hInB),
      Finset.card_union_of_disjoint hdisj, Nat.sub_sub]
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.sum_filter, ← Finset.sum_filter, ← Finset.sum_filter,
    filter_subset_powersetCard_two' hInA, filter_subset_powersetCard_two' hInB,
    filter_subset_powersetCard_two' Finset.sdiff_subset, Finset.sum_const, Finset.sum_const,
    Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul, Finset.card_powersetCard,
    Finset.card_powersetCard, Finset.card_powersetCard, hR]

theorem cladeSaturated_union {π : Finpartition (Finset.univ : Finset (Fin n))}
    {A C : Finset (Fin n)} (hA : CladeSaturated π A) (hC : CladeSaturated π C) :
    CladeSaturated π (A ∪ C) := by
  intro X hX
  rcases hA X hX with h | h
  · exact Or.inl (h.trans Finset.subset_union_left)
  · rcases hC X hX with h' | h'
    · exact Or.inl (h'.trans Finset.subset_union_right)
    · exact Or.inr (Finset.disjoint_union_right.mpr ⟨h, h'⟩)

theorem card_cladeInside_union {π : Finpartition (Finset.univ : Finset (Fin n))}
    {A C : Finset (Fin n)} (hA : CladeSaturated π A) (hAC : Disjoint A C) :
    (cladeInside π (A ∪ C)).card = (cladeInside π A).card + (cladeInside π C).card := by
  have he : cladeInside π (A ∪ C) = cladeInside π A ∪ cladeInside π C := by
    ext X
    simp only [cladeInside, Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hX, hsub⟩
      rcases hA X hX with h | h
      · exact Or.inl ⟨hX, h⟩
      · refine Or.inr ⟨hX, fun x hx => ?_⟩
        rcases Finset.mem_union.mp (hsub hx) with h1 | h1
        · exact absurd h1 ((Finset.disjoint_left.mp h) hx)
        · exact h1
    · rintro (⟨hX, h⟩ | ⟨hX, h⟩)
      · exact ⟨hX, h.trans Finset.subset_union_left⟩
      · exact ⟨hX, h.trans Finset.subset_union_right⟩
  rw [he, Finset.card_union_of_disjoint (disjoint_cladeInside hAC)]

theorem sum_sfsCladeNestTerm_increment {π : Finpartition (Finset.univ : Finset (Fin n))}
    {A C : Finset (Fin n)} (hAC : Disjoint A C)
    (hAne : A.Nonempty) (hCne : C.Nonempty) :
    ∑ s ∈ π.parts.powersetCard 2,
        (sfsCladeNestTerm (mergeBlocks π s) A C - sfsCladeNestTerm π A C) =
      -(if A ∈ π.parts then sfsCladeTerm π (A ∪ C) else 0) := by
  unfold sfsCladeNestTerm
  by_cases h : CladeSaturated π A ∧ CladeSaturated π C
  · obtain ⟨hA, hC⟩ := h
    have ha := card_cladeInside_pos hA hAne
    have hc := card_cladeInside_pos hC hCne
    have hac : (cladeInside π A).card + (cladeInside π C).card ≤ π.parts.card := by
      rw [← Finset.card_union_of_disjoint (disjoint_cladeInside hAC)]
      exact Finset.card_le_card
        (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
    have hiffA : A ∈ π.parts ↔ (cladeInside π A).card = 1 := by
      rw [mem_parts_iff_cladeSaturated_card]
      exact ⟨fun h => h.2, fun h => ⟨hA, h⟩⟩
    have hg : sfsCladeTerm π (A ∪ C) =
        sfsCladeCoeff π.parts.card ((cladeInside π A).card + (cladeInside π C).card) := by
      rw [sfsCladeTerm, ite_eq_left (cladeSaturated_union hA hC), card_cladeInside_union hA hAC]
    rw [Finset.sum_sub_distrib, sum_cladePairForm_mergeBlocks _ hA hC hAC, Finset.sum_const,
      nsmul_eq_mul, Finset.card_powersetCard, sfsCladeNestCoeff_step ha hc hac,
      cladePairForm, ite_eq_left (And.intro hA hC), hg, if_congr hiffA rfl rfl]
    ring
  · have hz : ∀ s, cladePairForm sfsCladeNestCoeff (mergeBlocks π s) A C = 0 := by
      intro s
      rw [cladePairForm, ite_eq_right]
      rintro ⟨h1, h2⟩
      apply h
      constructor
      · by_contra hn
        exact not_cladeSaturated_mergeBlocks hn s h1
      · by_contra hn
        exact not_cladeSaturated_mergeBlocks hn s h2
    have h0 : cladePairForm sfsCladeNestCoeff π A C = 0 := by
      rw [cladePairForm, ite_eq_right h]
    have r1 : (if A ∈ π.parts then sfsCladeTerm π (A ∪ C) else 0) = 0 := by
      split_ifs with hm
      · have hsA := ((mem_parts_iff_cladeSaturated_card π A).mp hm).1
        rw [sfsCladeTerm, ite_eq_right]
        intro hU
        apply h
        refine ⟨hsA, fun X hX => ?_⟩
        by_cases hXA : X = A
        · rw [hXA]
          exact Or.inr hAC
        · have hd : Disjoint X A := π.disjoint hX hm hXA
          rcases hU X hX with h1 | h1
          · refine Or.inl fun x hx => ?_
            rcases Finset.mem_union.mp (h1 hx) with h2 | h2
            · exact absurd h2 ((Finset.disjoint_left.mp hd) hx)
            · exact h2
          · exact Or.inr (h1.mono_right Finset.subset_union_right)
      · rfl
    rw [r1, neg_zero]
    apply Finset.sum_eq_zero
    intro s _
    rw [hz, h0, sub_zero]

theorem sfsCladeTerm_eq_zero_of_block_meets {π : Finpartition (Finset.univ : Finset (Fin n))}
    {A B : Finset (Fin n)} (hA : A ∈ π.parts) (hd : ¬ Disjoint A B) (hs : ¬ A ⊆ B) :
    sfsCladeTerm π B = 0 := by
  rw [sfsCladeTerm, ite_eq_right]
  intro hsat
  rcases hsat A hA with h | h
  · exact hs h
  · exact hd h

theorem sfsCladeTerm_eq_zero_of_larger_block {π : Finpartition (Finset.univ : Finset (Fin n))}
    {A B : Finset (Fin n)} (hB : B ∈ π.parts) (hcard : A.card < B.card)
    (hd : ¬ Disjoint A B) : sfsCladeTerm π A = 0 := by
  rw [sfsCladeTerm, ite_eq_right]
  intro hsat
  rcases hsat B hB with h | h
  · have := Finset.card_le_card h
    omega
  · exact hd h.symm

theorem sum_sfsCrossTerm_increment {i j : ℕ} (hi : 1 ≤ i) (hij : i < j)
    {π : Finpartition (Finset.univ : Finset (Fin n))} {A B : Finset (Fin n)}
    (hA : A.card = i) (hB : B.card = j) :
    ∑ s ∈ π.parts.powersetCard 2,
        (((if Disjoint A B then sfsCladePairTerm (mergeBlocks π s) A B else 0) +
            (if A ⊆ B then sfsCladeNestTerm (mergeBlocks π s) A (B \ A) else 0)) -
          ((if Disjoint A B then sfsCladePairTerm π A B else 0) +
            (if A ⊆ B then sfsCladeNestTerm π A (B \ A) else 0))) =
      -((if A ∈ π.parts then sfsCladeTerm π B else 0) +
        (if B ∈ π.parts then sfsCladeTerm π A else 0)) := by
  have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
  have hBne : B.Nonempty := Finset.card_pos.mp (by omega)
  by_cases hd : Disjoint A B
  · have hs : ¬ A ⊆ B := fun h =>
      hAne.ne_empty ((Finset.disjoint_self_iff_empty A).mp (hd.mono_right h))
    simp only [hd, hs, ↓reduceIte, add_zero]
    exact sum_sfsCladePairTerm_increment hd hAne hBne
  · have hBt : (if B ∈ π.parts then sfsCladeTerm π A else 0) = 0 := by
      split_ifs with hm
      · exact sfsCladeTerm_eq_zero_of_larger_block hm (by omega) hd
      · rfl
    by_cases hs : A ⊆ B
    · have hnBA : (B \ A).Nonempty := by
        rw [Finset.sdiff_nonempty]
        intro h
        have := Finset.card_le_card h
        omega
      simp only [hd, hs, ↓reduceIte, zero_add]
      rw [sum_sfsCladeNestTerm_increment Finset.disjoint_sdiff hAne hnBA,
        Finset.union_sdiff_of_subset hs, hBt, add_zero]
    · have hAt : (if A ∈ π.parts then sfsCladeTerm π B else 0) = 0 := by
        split_ifs with hm
        · exact sfsCladeTerm_eq_zero_of_block_meets hm hd hs
        · rfl
      simp only [hd, hs, ↓reduceIte, add_zero, sub_self, Finset.sum_const_zero]
      rw [hAt, hBt, add_zero, neg_zero]

theorem sfsCrossPotential_generator {i j : ℕ} (hi : 1 ≤ i) (hij : i < j)
    (π : Finpartition (Finset.univ : Finset (Fin n))) :
    ∑ σ, (partitionChain (Fin n)).Q π σ * sfsCrossPotential i j σ =
      -(sfsBlockCount n i π *
          sfsWeightPotential (fun B : Finset (Fin n) => if B.card = j then (1 : ℝ) else 0) π +
        sfsBlockCount n j π *
          sfsWeightPotential
            (fun B : Finset (Fin n) => if B.card = i then (1 : ℝ) else 0) π) := by
  have e1 : sfsBlockCount n i π *
      sfsWeightPotential (fun B : Finset (Fin n) => if B.card = j then (1 : ℝ) else 0) π =
      ∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard i,
        ∑ B ∈ (Finset.univ : Finset (Fin n)).powersetCard j,
          (if A ∈ π.parts then sfsCladeTerm π B else 0) := by
    rw [sfsBlockCount_eq_sum_powersetCard, sfsWeightPotential_indicator, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro A _
    apply Finset.sum_congr rfl
    intro B _
    rw [ite_mul, one_mul, zero_mul]
  have e2 : sfsBlockCount n j π *
      sfsWeightPotential (fun B : Finset (Fin n) => if B.card = i then (1 : ℝ) else 0) π =
      ∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard i,
        ∑ B ∈ (Finset.univ : Finset (Fin n)).powersetCard j,
          (if B ∈ π.parts then sfsCladeTerm π A else 0) := by
    rw [sfsBlockCount_eq_sum_powersetCard, sfsWeightPotential_indicator, Finset.sum_mul_sum,
      Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro A _
    apply Finset.sum_congr rfl
    intro B _
    rw [ite_mul, one_mul, zero_mul]
  rw [sum_partitionQ_reward, e1, e2, ← Finset.sum_add_distrib]
  unfold sfsCrossPotential
  simp_rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro A hA
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro B hB
  exact sum_sfsCrossTerm_increment hi hij (Finset.mem_powersetCard.mp hA).2
    (Finset.mem_powersetCard.mp hB).2

theorem sfsCrossPotential_coalesced (i j : ℕ)
    {π : Finpartition (Finset.univ : Finset (Fin n))}
    (hπ : π ∈ coalescedPartitions (Fin n)) : sfsCrossPotential i j π = 0 := by
  have hk := mem_coalescedPartitions.mp hπ
  unfold sfsCrossPotential
  have h1 : ∀ A B, sfsCladePairTerm π A B = 0 := by
    intro A B
    rw [sfsCladePairTerm, sfsCladePairCoeff_of_le_one hk, ite_self]
  have h2 : ∀ A C, sfsCladeNestTerm π A C = 0 := by
    intro A C
    rw [sfsCladeNestTerm, cladePairForm, sfsCladeNestCoeff_of_le_one hk, ite_self]
  simp only [h1, h2, ite_self, add_zero, Finset.sum_const_zero]

theorem sfsCrossPotential_eq_expectedCost {i j : ℕ} (hi : 1 ≤ i) (hij : i < j) :
    sfsCrossPotential (n := n) i j = (partitionChain (Fin n)).expectedCost
      (coalescedPartitions (Fin n)) (fun π => sfsBlockCount n i π *
          sfsWeightPotential (fun B : Finset (Fin n) => if B.card = j then (1 : ℝ) else 0) π +
        sfsBlockCount n j π *
          sfsWeightPotential
            (fun B : Finset (Fin n) => if B.card = i then (1 : ℝ) else 0) π) := by
  apply Rhone.MarkovChain.RateChain.eq_expectedCost_of_generator
    (partitionChain_coalesced_isAbsorbingSet n) (partitionChain_coalesced_reaches n)
    (fun π hπ => (partitionChain_transient_rate_pos n π hπ).ne')
  · intro π hπ
    exact sfsCrossPotential_coalesced i j hπ
  · intro π _
    exact sfsCrossPotential_generator hi hij π

private theorem jump_drift_of_eq_expectedCost'' (n : ℕ)
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

theorem sfsCrossPotential_jump_drift {n i j : ℕ} (hi : 1 ≤ i) (hij : i < j)
    (π : Finpartition (Finset.univ : Finset (Fin n))) :
    sfsCrossPotential i j π -
        (partitionChain (Fin n)).jumpChain.expect (sfsCrossPotential i j) π =
      kingmanJumpReward n (sfsBlockCount n i) π *
          sfsWeightPotential (fun B : Finset (Fin n) => if B.card = j then (1 : ℝ) else 0) π +
        kingmanJumpReward n (sfsBlockCount n j) π *
          sfsWeightPotential
              (fun B : Finset (Fin n) => if B.card = i then (1 : ℝ) else 0) π := by
  rw [jump_drift_of_eq_expectedCost'' n _ _ (sfsCrossPotential_eq_expectedCost hi hij) π]
  unfold kingmanJumpReward
  split_ifs <;> ring

theorem sfsCrossPotential_bot (n i j : ℕ) :
    sfsCrossPotential i j (⊥ : Finpartition (Finset.univ : Finset (Fin n))) =
      (n.choose i : ℝ) * ((n - i).choose j : ℝ) * sfsCladePairCoeff n i j +
        (n.choose j : ℝ) * (j.choose i : ℝ) * sfsCladeNestCoeff n i (j - i) := by
  have hcard : (⊥ : Finpartition (Finset.univ : Finset (Fin n))).parts.card = n := by simp
  have h1 : ∀ A ∈ (Finset.univ : Finset (Fin n)).powersetCard i,
      ∑ B ∈ (Finset.univ : Finset (Fin n)).powersetCard j,
        (if Disjoint A B then
          sfsCladePairTerm (⊥ : Finpartition (Finset.univ : Finset (Fin n))) A B else 0) =
        ((n - i).choose j : ℝ) * sfsCladePairCoeff n i j := by
    intro A hA
    have hA' := (Finset.mem_powersetCard.mp hA).2
    have hf : ((Finset.univ : Finset (Fin n)).powersetCard j).filter (fun B => Disjoint A B) =
        ((Finset.univ : Finset (Fin n)) \ A).powersetCard j := by
      ext B
      simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and,
        Finset.subset_sdiff]
      exact ⟨fun h => ⟨h.2.symm, h.1⟩, fun h => ⟨h.2, h.1.symm⟩⟩
    have hterm : ∀ B ∈ ((Finset.univ : Finset (Fin n)) \ A).powersetCard j,
        sfsCladePairTerm (⊥ : Finpartition (Finset.univ : Finset (Fin n))) A B =
          sfsCladePairCoeff n i j := by
      intro B hB
      rw [sfsCladePairTerm, ite_eq_left (And.intro (cladeSaturated_bot A) (cladeSaturated_bot B)),
        card_cladeInside_bot, card_cladeInside_bot, hcard, hA',
        (Finset.mem_powersetCard.mp hB).2]
    rw [← Finset.sum_filter, hf, Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul,
      Finset.card_powersetCard, Finset.card_sdiff_of_subset (Finset.subset_univ A),
      Finset.card_univ, Fintype.card_fin, hA']
  have h2 : ∀ B ∈ (Finset.univ : Finset (Fin n)).powersetCard j,
      ∑ A ∈ (Finset.univ : Finset (Fin n)).powersetCard i,
        (if A ⊆ B then
          sfsCladeNestTerm (⊥ : Finpartition (Finset.univ : Finset (Fin n))) A (B \ A)
            else 0) =
        (j.choose i : ℝ) * sfsCladeNestCoeff n i (j - i) := by
    intro B hB
    have hB' := (Finset.mem_powersetCard.mp hB).2
    have hf : ((Finset.univ : Finset (Fin n)).powersetCard i).filter (fun A => A ⊆ B) =
        B.powersetCard i := by
      ext A
      simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
      exact and_comm
    have hterm : ∀ A ∈ B.powersetCard i,
        sfsCladeNestTerm (⊥ : Finpartition (Finset.univ : Finset (Fin n))) A (B \ A) =
          sfsCladeNestCoeff n i (j - i) := by
      intro A hA
      obtain ⟨hAB, hAc⟩ := Finset.mem_powersetCard.mp hA
      rw [sfsCladeNestTerm, cladePairForm,
        ite_eq_left (And.intro (cladeSaturated_bot A) (cladeSaturated_bot (B \ A))),
        card_cladeInside_bot, card_cladeInside_bot, hcard, Finset.card_sdiff_of_subset hAB,
        hAc, hB']
    rw [← Finset.sum_filter, hf, Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul,
      Finset.card_powersetCard, hB']
  unfold sfsCrossPotential
  simp_rw [Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm, Finset.sum_congr rfl h2, Finset.sum_const,
    Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, Finset.card_powersetCard,
    Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  ring

theorem sfsCrossPotential_bot_eq {n i j : ℕ} (hi : 1 ≤ i) (hij : i < j) (hjn : j < n) :
    sfsCrossPotential i j (⊥ : Finpartition (Finset.univ : Finset (Fin n))) =
      4 * fuSigma n i j + 4 / ((i : ℝ) * (j : ℝ)) := by
  have hch : (n.choose j : ℝ) * (j.choose i : ℝ) =
      (n.choose i : ℝ) * ((n - i).choose (j - i) : ℝ) := by
    exact_mod_cast Nat.choose_mul (n := n) hij.le
  rw [sfsCrossPotential_bot n i j, choose_mul_sfsCladePairCoeff, hch,
    choose_mul_sfsCladeNestCoeff, fuSigma_eq hi hij hjn]

theorem sfsBlockCount_nonneg (n i : ℕ) (π : Finpartition (Finset.univ : Finset (Fin n))) :
    0 ≤ sfsBlockCount n i π := by
  unfold sfsBlockCount
  exact Finset.sum_nonneg fun B _ => by split_ifs <;> norm_num

/-- Source: fu1995, eq. (31), p. 187; durrett2008, Thm 2.2. -/
theorem integral_kingmanFiniteReward_sfsBlockCount_mul {n i j : ℕ} (hi : 1 ≤ i) (hij : i < j)
    (hjn : j < n) :
    ∫ h, kingmanFiniteReward n (sfsBlockCount n i) h * kingmanFiniteReward n (sfsBlockCount n j) h
      ∂(partitionChain (Fin n)).jumpHoldLaw ⊥ =
      4 * fuSigma n i j + 4 / ((i : ℝ) * (j : ℝ)) := by
  rw [integral_kingmanFiniteReward_mul n _ _ (sfsBlockCount_nonneg n i)
      (sfsBlockCount_nonneg n j),
    partitionChain_integral_cross_jumpReward n _ _ _ _ (sfsCrossPotential i j)
      (sfsWeightPotential_indicator_jump_drift n i) (sfsWeightPotential_indicator_jump_drift n j)
      (sfsCrossPotential_jump_drift hi hij)
      (fun π hπ => sfsWeightPotential_coalesced _ hπ)
      (fun π hπ => sfsWeightPotential_coalesced _ hπ)
      (fun π hπ => sfsCrossPotential_coalesced i j hπ),
    sfsCrossPotential_bot_eq hi hij hjn]

end Rhone.Statistics
