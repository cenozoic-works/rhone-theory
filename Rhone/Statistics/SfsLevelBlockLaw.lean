/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Statistics.SfsMarkedSpectrum
public import Rhone.Coalescent.Sfs
public import Rhone.Coalescent.KingmanPartitionJumpKernel
public import Rhone.Coalescent.KingmanFiniteRewards

/-!
# Level and block-count laws of the site frequency spectrum via reward potentials

Source: wakeley2009, sec. 3.2; fu1995, eq. 22. -/

@[expose] public section
namespace Rhone.Statistics
open MeasureTheory ProbabilityTheory Finset Coalescent Rhone.Combinatorics MarkovChain Filter

variable {n : ℕ}

/-- Source: wakeley2009, sec. 3.2. -/
noncomputable def sfsLevelCoeff (k m t : ℕ) : ℝ :=
  if 1 ≤ t ∧ t < m then
    (k : ℝ) * ((m - t - 1).choose (k - 2) : ℝ) /
      (((m - 1).choose (k - 1) : ℝ) * (m.choose t : ℝ))
  else 0

/-- Source: wakeley2009, sec. 3.2. -/
theorem sfsLevelCoeff_self {k : ℕ} (hk : 2 ≤ k) (t : ℕ) :
    sfsLevelCoeff k k t = if t = 1 then 1 else 0 := by
  unfold sfsLevelCoeff
  by_cases h : 1 ≤ t ∧ t < k
  · rw [ite_eq_left h]
    by_cases ht : t = 1
    · subst ht
      have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
      rw [ite_eq_left rfl, show k - 1 - 1 = k - 2 by omega, Nat.choose_self, Nat.choose_self,
        Nat.choose_one_right]
      field_simp
    · rw [ite_eq_right ht, Nat.choose_eq_zero_of_lt (by omega)]
      simp
  · rw [ite_eq_right h, ite_eq_right (by omega)]

/-- Source: wakeley2009, sec. 3.2. -/
theorem sfsLevelCoeff_step {k m : ℕ} (hk : 2 ≤ k) (hkm : k < m) (t : ℕ) :
    (t.choose 2 : ℝ) * sfsLevelCoeff k (m - 1) (t - 1) +
        ((m - t).choose 2 : ℝ) * sfsLevelCoeff k (m - 1) t =
      (m.choose 2 : ℝ) * sfsLevelCoeff k m t := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp [sfsLevelCoeff]
  rcases Nat.lt_or_ge t m with htm | htm
  swap
  · have h1 : ¬ (1 ≤ t - 1 ∧ t - 1 < m - 1) := by omega
    have h2 : ¬ (1 ≤ t ∧ t < m - 1) := by omega
    have h3 : ¬ (1 ≤ t ∧ t < m) := by omega
    simp [sfsLevelCoeff, h1, h2, h3]
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  obtain ⟨a, rfl⟩ : ∃ a, m = s + a + 2 := ⟨m - s - 2, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  obtain ⟨d, hd⟩ : ∃ d, s + a = j + 1 + d := ⟨s + a - j - 1, by omega⟩
  rw [show s + a + 2 - 1 = s + a + 1 by omega, show s + 1 - 1 = s by omega,
    show s + a + 2 - (s + 1) = a + 1 by omega]
  have hfirst : ((s + 1).choose 2 : ℝ) * sfsLevelCoeff (j + 2) (s + a + 1) s =
      ((s + 1).choose 2 : ℝ) * (((j + 2 : ℕ) : ℝ) * (a.choose j : ℝ) /
        (((s + a).choose (j + 1) : ℝ) * ((s + a + 1).choose s : ℝ))) := by
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · simp [Nat.choose]
    · rw [sfsLevelCoeff, ite_eq_left (by omega), show s + a + 1 - s - 1 = a by omega,
        show j + 2 - 2 = j by omega, show s + a + 1 - 1 = s + a by omega,
        show j + 2 - 1 = j + 1 by omega]
  have hsecond : ((a + 1).choose 2 : ℝ) * sfsLevelCoeff (j + 2) (s + a + 1) (s + 1) =
      ((a + 1).choose 2 : ℝ) * (((j + 2 : ℕ) : ℝ) * ((a - 1).choose j : ℝ) /
        (((s + a).choose (j + 1) : ℝ) * ((s + a + 1).choose (s + 1) : ℝ))) := by
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp [Nat.choose]
    · rw [sfsLevelCoeff, ite_eq_left (by omega), show s + a + 1 - (s + 1) - 1 = a - 1 by omega,
        show j + 2 - 2 = j by omega, show s + a + 1 - 1 = s + a by omega,
        show j + 2 - 1 = j + 1 by omega]
  have hthird : sfsLevelCoeff (j + 2) (s + a + 2) (s + 1) =
      ((j + 2 : ℕ) : ℝ) * (a.choose j : ℝ) /
        (((s + a + 1).choose (j + 1) : ℝ) * ((s + a + 2).choose (s + 1) : ℝ)) := by
    rw [sfsLevelCoeff, ite_eq_left (by omega), show s + a + 2 - (s + 1) - 1 = a by omega,
      show j + 2 - 2 = j by omega, show s + a + 2 - 1 = s + a + 1 by omega,
      show j + 2 - 1 = j + 1 by omega]
  have hA : (a : ℝ) * ((a - 1).choose j : ℝ) = (a.choose j : ℝ) * ((a : ℝ) - j) := by
    rcases le_or_gt j a with h | h
    · rcases Nat.eq_zero_or_pos a with rfl | ha
      · obtain rfl : j = 0 := by omega
        simp
      · have hN := Nat.choose_mul_succ_eq (a - 1) j
        rw [show a - 1 + 1 = a by omega] at hN
        have hR : ((a - 1).choose j : ℝ) * (a : ℝ) = (a.choose j : ℝ) * ((a - j : ℕ) : ℝ) := by
          exact_mod_cast hN
        rw [Nat.cast_sub h] at hR
        linarith
    · rw [Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt (by omega)]
      simp
  have hY0 : 0 < (s + a + 1).choose (j + 1) := Nat.choose_pos (by omega)
  have hT0 : 0 < (s + a + 2).choose (s + 1) := Nat.choose_pos (by omega)
  have hYN := Nat.choose_mul_succ_eq (s + a) (j + 1)
  rw [show s + a + 1 - (j + 1) = d + 1 by omega] at hYN
  have hT1N := Nat.add_one_mul_choose_eq (s + a + 1) s
  have hT2N := Nat.choose_mul_succ_eq (s + a + 1) (s + 1)
  rw [show s + a + 1 + 1 - (s + 1) = a + 1 by omega] at hT2N
  have hYR : ((s + a).choose (j + 1) : ℝ) * ((s : ℝ) + a + 1) =
      ((s + a + 1).choose (j + 1) : ℝ) * ((d : ℝ) + 1) := by exact_mod_cast hYN
  have hT1R : ((s : ℝ) + a + 1 + 1) * ((s + a + 1).choose s : ℝ) =
      ((s + a + 2).choose (s + 1) : ℝ) * ((s : ℝ) + 1) := by exact_mod_cast hT1N
  have hT2R : ((s + a + 1).choose (s + 1) : ℝ) * ((s : ℝ) + a + 1 + 1) =
      ((s + a + 2).choose (s + 1) : ℝ) * ((a : ℝ) + 1) := by exact_mod_cast hT2N
  have hdR : (j : ℝ) = (s : ℝ) + a - 1 - d := by
    have : ((s + a : ℕ) : ℝ) = ((j + 1 + d : ℕ) : ℝ) := by rw [hd]
    push_cast at this
    linarith
  have hK1 : (s : ℝ) + a + 1 ≠ 0 := by positivity
  have hK2 : (s : ℝ) + a + 1 + 1 ≠ 0 := by positivity
  have hs1 : (s : ℝ) + 1 ≠ 0 := by positivity
  have ha1 : (a : ℝ) + 1 ≠ 0 := by positivity
  have hd1 : (d : ℝ) + 1 ≠ 0 := by positivity
  have hYne : ((s + a + 1).choose (j + 1) : ℝ) ≠ 0 := by exact_mod_cast hY0.ne'
  have hTne : ((s + a + 2).choose (s + 1) : ℝ) ≠ 0 := by exact_mod_cast hT0.ne'
  have hxE : ((s + a).choose (j + 1) : ℝ) =
      ((s + a + 1).choose (j + 1) : ℝ) * ((d : ℝ) + 1) / ((s : ℝ) + a + 1) := by
    rw [eq_div_iff hK1, hYR]
  have ht1E : ((s + a + 1).choose s : ℝ) =
      ((s + a + 2).choose (s + 1) : ℝ) * ((s : ℝ) + 1) / ((s : ℝ) + a + 1 + 1) := by
    rw [eq_div_iff hK2, ← hT1R]
    ring
  have ht2E : ((s + a + 1).choose (s + 1) : ℝ) =
      ((s + a + 2).choose (s + 1) : ℝ) * ((a : ℝ) + 1) / ((s : ℝ) + a + 1 + 1) := by
    rw [eq_div_iff hK2, hT2R]
  have hsecond' : ((a + 1).choose 2 : ℝ) * (((j + 2 : ℕ) : ℝ) * ((a - 1).choose j : ℝ) /
        (((s + a).choose (j + 1) : ℝ) * ((s + a + 1).choose (s + 1) : ℝ))) =
      ((a : ℝ) + 1) / 2 * (((j + 2 : ℕ) : ℝ) * ((a.choose j : ℝ) * ((a : ℝ) - j)) /
        (((s + a).choose (j + 1) : ℝ) * ((s + a + 1).choose (s + 1) : ℝ))) := by
    rw [Nat.cast_choose_two, ← hA]
    push_cast
    ring
  rw [hfirst, hsecond, hsecond', hthird, hxE, ht1E, ht2E, Nat.cast_choose_two,
    Nat.cast_choose_two]
  push_cast
  rw [hdR]
  field_simp
  ring

/-- Source: wakeley2009, sec. 3.2. -/
noncomputable def sfsLevelTerm (k : ℕ) (π : Finpartition (Finset.univ : Finset (Fin n)))
    (A : Finset (Fin n)) : ℝ :=
  if CladeSaturated π A then sfsLevelCoeff k π.parts.card (cladeInside π A).card else 0

/-- Source: wakeley2009, sec. 3.2. -/
noncomputable def sfsLevelPotential (k : ℕ) (w : Finset (Fin n) → ℝ)
    (π : Finpartition (Finset.univ : Finset (Fin n))) : ℝ :=
  ∑ A : Finset (Fin n), w A * sfsLevelTerm k π A

/-- Source: wakeley2009, sec. 3.2. -/
theorem sum_sfsLevelTerm_mergeBlocks (k : ℕ)
    {π : Finpartition (Finset.univ : Finset (Fin n))}
    {A : Finset (Fin n)} (hsat : CladeSaturated π A) :
    ∑ s ∈ π.parts.powersetCard 2, sfsLevelTerm k (mergeBlocks π s) A =
      ((cladeInside π A).card.choose 2 : ℝ) *
          sfsLevelCoeff k (π.parts.card - 1) ((cladeInside π A).card - 1) +
        ((π.parts.card - (cladeInside π A).card).choose 2 : ℝ) *
          sfsLevelCoeff k (π.parts.card - 1) (cladeInside π A).card := by
  have hInP : cladeInside π A ⊆ π.parts := Finset.filter_subset _ _
  have hpt : ∀ s ∈ π.parts.powersetCard 2, sfsLevelTerm k (mergeBlocks π s) A =
      (if s ⊆ cladeInside π A then
          sfsLevelCoeff k (π.parts.card - 1) ((cladeInside π A).card - 1) else 0) +
        (if s ⊆ π.parts \ cladeInside π A then
          sfsLevelCoeff k (π.parts.card - 1) (cladeInside π A).card else 0) := by
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
      rw [ite_eq_left h1, ite_eq_right h2, add_zero, sfsLevelTerm, ite_eq_left hsat',
        show (mergeBlocks π s).parts.card = π.parts.card - 1 by omega,
        show (cladeInside (mergeBlocks π s) A).card = (cladeInside π A).card - 1 by omega]
    · by_cases h2 : s ⊆ π.parts \ cladeInside π A
      · have hout : ∀ b ∈ s, ¬ b ⊆ A := fun b hb hbA =>
          (Finset.mem_sdiff.mp (h2 hb)).2 (Finset.mem_filter.mpr ⟨hs hb, hbA⟩)
        obtain ⟨hsat', hins⟩ := cladeSaturated_mergeBlocks_outside hsat hs hne hout
        rw [ite_eq_right h1, ite_eq_left h2, zero_add, sfsLevelTerm, ite_eq_left hsat', hins,
          show (mergeBlocks π s).parts.card = π.parts.card - 1 by omega]
      · obtain ⟨b, hb, hbI⟩ := Finset.not_subset.mp h1
        obtain ⟨a, ha, haO⟩ := Finset.not_subset.mp h2
        have hbA : ¬ b ⊆ A := fun h => hbI (Finset.mem_filter.mpr ⟨hs hb, h⟩)
        have haA : a ⊆ A := by
          by_contra h
          exact haO (Finset.mem_sdiff.mpr ⟨hs ha, fun hI => h (Finset.mem_filter.mp hI).2⟩)
        rw [ite_eq_right h1, ite_eq_right h2, add_zero, sfsLevelTerm,
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

/-- Source: wakeley2009, sec. 3.2. -/
theorem sum_sfsLevelTerm_mergeBlocks_eq {k : ℕ}
    {π : Finpartition (Finset.univ : Finset (Fin n))} (hk : 2 ≤ k)
    (hkm : k < π.parts.card) (A : Finset (Fin n)) :
    ∑ s ∈ π.parts.powersetCard 2, sfsLevelTerm k (mergeBlocks π s) A =
      (π.parts.card.choose 2 : ℝ) * sfsLevelTerm k π A := by
  by_cases hsat : CladeSaturated π A
  · rw [sum_sfsLevelTerm_mergeBlocks k hsat, sfsLevelCoeff_step hk hkm, sfsLevelTerm,
      ite_eq_left hsat]
  · rw [sfsLevelTerm, ite_eq_right hsat, mul_zero]
    apply Finset.sum_eq_zero
    intro s _
    rw [sfsLevelTerm, ite_eq_right (not_cladeSaturated_mergeBlocks hsat s)]

/-- Source: wakeley2009, sec. 3.2. -/
theorem expect_sfsLevelPotential {k : ℕ} (hk : 2 ≤ k) (w : Finset (Fin n) → ℝ)
    {π : Finpartition (Finset.univ : Finset (Fin n))} (hkm : k < π.parts.card) :
    (partitionChain (Fin n)).jumpChain.expect (sfsLevelPotential k w) π =
      sfsLevelPotential k w π := by
  have hr : (partitionChain (Fin n)).rate π ≠ 0 := by
    rw [partitionChain_rate]
    exact_mod_cast (coalRate_pos (by omega : 2 ≤ π.parts.card)).ne'
  have hz : ∑ s ∈ π.parts.powersetCard 2,
      (sfsLevelPotential k w (mergeBlocks π s) - sfsLevelPotential k w π) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]
    unfold sfsLevelPotential
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, sum_sfsLevelTerm_mergeBlocks_eq hk hkm]
    rw [Finset.mul_sum, sub_eq_zero]
    exact Finset.sum_congr rfl fun A _ => by ring
  rw [FinChain.expect_apply, RateChain.jumpChain_P, RateChain.sum_jumpMatrix_mul _ hr,
    sum_partitionQ_reward, hz, zero_div, add_zero]

/-- Source: wakeley2009, sec. 3.2. -/
theorem sfsLevelPotential_of_card {k : ℕ} (hk : 2 ≤ k) (w : Finset (Fin n) → ℝ)
    {π : Finpartition (Finset.univ : Finset (Fin n))} (hπ : π.parts.card = k) :
    sfsLevelPotential k w π = blockWeightReward w π := by
  unfold sfsLevelPotential blockWeightReward
  have hterm : ∀ A : Finset (Fin n),
      w A * sfsLevelTerm k π A = if A ∈ π.parts then w A else 0 := by
    intro A
    rw [sfsLevelTerm, hπ, sfsLevelCoeff_self hk]
    by_cases hA : A ∈ π.parts
    · obtain ⟨hsat, hc⟩ := (mem_parts_iff_cladeSaturated_card π A).mp hA
      rw [ite_eq_left hsat, ite_eq_left hc, ite_eq_left hA, mul_one]
    · rw [ite_eq_right hA]
      by_cases hsat : CladeSaturated π A
      · have hc : ¬ (cladeInside π A).card = 1 := fun h =>
          hA ((mem_parts_iff_cladeSaturated_card π A).mpr ⟨hsat, h⟩)
        rw [ite_eq_left hsat, ite_eq_right hc, mul_zero]
      · rw [ite_eq_right hsat, mul_zero]
  simp_rw [hterm]
  rw [← Finset.sum_filter]
  congr 1
  ext B
  simp

/-- Source: wakeley2009, sec. 3.2. -/
theorem expectN_blockWeightReward_eq_sfsLevelPotential {k : ℕ} (hk : 2 ≤ k)
    (w : Finset (Fin n) → ℝ) (d : ℕ) :
    ∀ π : Finpartition (Finset.univ : Finset (Fin n)), π.parts.card = k + d →
      (partitionChain (Fin n)).jumpChain.expectN d (blockWeightReward w) π =
        sfsLevelPotential k w π := by
  induction d with
  | zero =>
    intro π hπ
    rw [FinChain.expectN_zero, sfsLevelPotential_of_card hk w (by omega)]
  | succ d ih =>
    intro π hπ
    refine Eq.trans ?_ (expect_sfsLevelPotential hk w (by omega : k < π.parts.card))
    rw [FinChain.expectN_succ, FinChain.expect_apply, FinChain.expect_apply]
    apply Finset.sum_congr rfl
    intro σ _
    by_cases hσ : σ ∈ merges π
    · rw [ih σ (by have := card_parts_of_mem_merges hσ; omega)]
    · rw [partition_jump_prob (by omega : 2 ≤ π.parts.card) σ, ite_eq_right hσ, zero_mul,
        zero_mul]

/-- Source: wakeley2009, sec. 3.2. -/
theorem sfsLevelPotential_bot (k : ℕ) (w : Finset (Fin n) → ℝ) :
    sfsLevelPotential k w (⊥ : Finpartition (Finset.univ : Finset (Fin n))) =
      ∑ A : Finset (Fin n), w A * sfsLevelCoeff k n A.card := by
  unfold sfsLevelPotential
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
  rw [sfsLevelTerm, ite_eq_left hsat, hin, Finset.card_map, hcard]

/-- Source: kingman1982, eq. (1.14). -/
theorem ae_card_parts_level {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) :
    ∀ᵐ ω ∂(partitionChain (Fin n)).jumpChain.pathLaw ⊥, (ω (n - k)).parts.card = k := by
  filter_upwards [partition_path_countdown_general n] with ω hω
  rw [hω]
  omega

/-- Source: wakeley2009, sec. 3.2. -/
theorem integral_blockWeightReward_level {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n)
    (w : Finset (Fin n) → ℝ) :
    ∫ ω, blockWeightReward w (ω (n - k)) ∂(partitionChain (Fin n)).jumpChain.pathLaw ⊥ =
      ∑ A : Finset (Fin n), w A * sfsLevelCoeff k n A.card := by
  have hcard : (⊥ : Finpartition (Finset.univ : Finset (Fin n))).parts.card = n := by simp
  rw [FinChain.integral_eval _ (n - k) (blockWeightReward w) ⊥,
    expectN_blockWeightReward_eq_sfsLevelPotential hk w (n - k) ⊥ (by omega),
    sfsLevelPotential_bot]

/-- Source: wakeley2009, sec. 3.2. -/
theorem integral_sfsBlockCount_level {n k i : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n)
    (hi : 1 ≤ i) (hin : i < n) :
    ∫ ω, sfsBlockCount n i (ω (n - k)) ∂(partitionChain (Fin n)).jumpChain.pathLaw ⊥ =
      (k : ℝ) * ((subtendProb n k i : ℚ) : ℝ) := by
  rw [sfsBlockCount_eq_blockWeightReward, integral_blockWeightReward_level hk hkn]
  have hterm : ∀ A : Finset (Fin n),
      (if A.card = i then (1 : ℝ) else 0) * sfsLevelCoeff k n A.card =
        if A.card = i then sfsLevelCoeff k n i else 0 := by
    intro A
    split_ifs with hA
    · rw [hA, one_mul]
    · rw [zero_mul]
  simp_rw [hterm]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Finset.univ_filter_card_eq,
    Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  have hc : (n.choose i : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hin.le).ne'
  have hC : ((n - 1).choose (k - 1) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : k - 1 ≤ n - 1)).ne'
  unfold sfsLevelCoeff subtendProb
  rw [ite_eq_left ⟨hi, hin⟩]
  push_cast
  field_simp

/-- Source: wakeley2009, sec. 3.2. -/
theorem integral_sfsBlockCount_level_jumpHoldLaw {n k i : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n)
    (hi : 1 ≤ i) (hin : i < n) :
    ∫ h, sfsBlockCount n i (h.1 (n - k)) ∂(partitionChain (Fin n)).jumpHoldLaw ⊥ =
      (k : ℝ) * ((subtendProb n k i : ℚ) : ℝ) := by
  rw [← integral_sfsBlockCount_level hk hkn hi hin, RateChain.jumpHoldLaw]
  refine (integral_fun_fst (μ := (partitionChain (Fin n)).jumpChain.pathLaw ⊥)
    (ν := clockLaw)
    (fun ω : ℕ → Finpartition (Finset.univ : Finset (Fin n)) =>
      sfsBlockCount n i (ω (n - k)))).trans ?_
  simp

end Rhone.Statistics
