/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.SfsMarkedSpectrumPotential
public import Rhone.Coalescent.KingmanFiniteRewards

/-!
# Clade probability and expected number of cherries of the Kingman coalescent

Source: kingman1982, sec. 1, eq. (1.1)–(1.4), (1.7). -/

@[expose] public section
namespace Rhone.Coalescent
open MeasureTheory ProbabilityTheory Finset MarkovChain Probability

variable {n : ℕ}

noncomputable def cladeCreationCoeff (k j : ℕ) : ℝ :=
  if 2 ≤ j then
    2 * ((j - 1).factorial : ℝ) * ((k - j).factorial : ℝ) /
      (((j : ℝ) + 1) * ((k - 1).factorial : ℝ))
  else 0

theorem cladeCreation_factorial_step (a d : ℕ) :
    ((a + 2).choose 2 : ℝ) *
          (2 * (a.factorial : ℝ) * ((d + 1).factorial : ℝ) /
            (((a : ℝ) + 2) * ((a + d + 1).factorial : ℝ))) +
        ((d + 1).choose 2 : ℝ) *
          (2 * ((a + 1).factorial : ℝ) * (d.factorial : ℝ) /
            (((a : ℝ) + 3) * ((a + d + 1).factorial : ℝ))) =
      ((a + d + 3).choose 2 : ℝ) *
        (2 * ((a + 1).factorial : ℝ) * ((d + 1).factorial : ℝ) /
          (((a : ℝ) + 3) * ((a + d + 2).factorial : ℝ))) := by
  have ha : (a.factorial : ℝ) ≠ 0 := by exact_mod_cast a.factorial_ne_zero
  have hd : (d.factorial : ℝ) ≠ 0 := by exact_mod_cast d.factorial_ne_zero
  have hs : ((a + d + 1).factorial : ℝ) ≠ 0 := by exact_mod_cast (a + d + 1).factorial_ne_zero
  have h2 : (a : ℝ) + 2 ≠ 0 := by positivity
  have h3 : (a : ℝ) + 3 ≠ 0 := by positivity
  have h4 : (a : ℝ) + d + 2 ≠ 0 := by positivity
  rw [Nat.cast_choose_two, Nat.cast_choose_two, Nat.cast_choose_two,
    Nat.factorial_succ a, Nat.factorial_succ d, Nat.factorial_succ (a + d + 1)]
  push_cast
  field_simp
  ring

theorem cladeCreationCoeff_step {k j : ℕ} (hj : j < k) :
    (k.choose 2 : ℝ) * cladeCreationCoeff k j -
        ((j.choose 2 : ℝ) * cladeCreationCoeff (k - 1) (j - 1) +
          ((k - j).choose 2 : ℝ) * cladeCreationCoeff (k - 1) j) =
      if j = 2 then 1 else 0 := by
  rcases Nat.lt_or_ge j 2 with hj2 | hj2
  · have h1 : ¬ 2 ≤ j := by omega
    have h2 : ¬ 2 ≤ j - 1 := by omega
    have h3 : j ≠ 2 := by omega
    simp only [cladeCreationCoeff, h1, h2, h3, ↓reduceIte, mul_zero, add_zero, sub_zero]
  · obtain ⟨a, rfl⟩ : ∃ a, j = a + 2 := ⟨j - 2, by omega⟩
    obtain ⟨d, rfl⟩ : ∃ d, k = a + d + 3 := ⟨k - a - 3, by omega⟩
    have hstep := cladeCreation_factorial_step a d
    have e1 : a + d + 3 - 1 = a + d + 2 := by omega
    have e2 : a + 2 - 1 = a + 1 := by omega
    have e3 : a + d + 3 - (a + 2) = d + 1 := by omega
    have e4 : a + d + 2 - (a + 2) = d := by omega
    have e5 : a + d + 2 - (a + 1) = d + 1 := by omega
    have e6 : a + d + 2 - 1 = a + d + 1 := by omega
    have e7 : a + 1 - 1 = a := by omega
    have c2 : (2 : ℕ) ≤ a + 2 := by omega
    rw [e1, e2, e3]
    simp only [cladeCreationCoeff, c2, ↓reduceIte, e1, e2, e3, e4, e5, e6, e7]
    have hc : (((a + 2 : ℕ) : ℝ) + 1) = (a : ℝ) + 3 := by push_cast; ring
    have hc' : (((a + 1 : ℕ) : ℝ) + 1) = (a : ℝ) + 2 := by push_cast; ring
    rw [hc, hc']
    rcases Nat.eq_zero_or_pos a with rfl | hapos
    · have hone : (2 * ((0 : ℕ).factorial : ℝ) * ((d + 1).factorial : ℝ) /
          ((((0 : ℕ) : ℝ) + 2) * ((0 + d + 1).factorial : ℝ))) = 1 := by
        have hd : (((0 + d + 1).factorial : ℕ) : ℝ) ≠ 0 := by
          exact_mod_cast (0 + d + 1).factorial_ne_zero
        rw [show (0 + d + 1) = d + 1 by omega] at hd ⊢
        simp only [Nat.factorial_zero, Nat.cast_one, Nat.cast_zero, zero_add, mul_one]
        field_simp
      rw [hone] at hstep
      have hn : ¬ (2 : ℕ) ≤ 0 + 1 := by omega
      simp only [hn, ↓reduceIte, mul_zero, zero_add]
      have hch : (((0 + 2).choose 2 : ℕ) : ℝ) = 1 := by norm_num [Nat.choose]
      rw [hch] at hstep
      simp only [zero_add, Nat.cast_zero, Nat.factorial_one, Nat.cast_one, mul_one] at hstep ⊢
      linarith
    · have hn : (2 : ℕ) ≤ a + 1 := by omega
      have hne : a + 2 ≠ 2 := by omega
      simp only [hn, hne, ↓reduceIte]
      linarith

theorem cladeCreationCoeff_eq_choose {m a : ℕ} (ha : 2 ≤ a) (ham : a ≤ m) :
    cladeCreationCoeff m a =
      2 * (m : ℝ) / ((a : ℝ) * ((a : ℝ) + 1) * (m.choose a : ℝ)) := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  obtain ⟨p, rfl⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
  have h := Nat.choose_mul_factorial_mul_factorial ham
  rw [Nat.factorial_succ b, Nat.factorial_succ p, Nat.add_sub_add_right] at h
  have hR : ((p + 1).choose (b + 1) : ℝ) * (((b : ℝ) + 1) * (b.factorial : ℝ)) *
      ((p - b).factorial : ℝ) = ((p : ℝ) + 1) * (p.factorial : ℝ) := by
    exact_mod_cast h
  have hc : ((p + 1).choose (b + 1) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos ham).ne'
  have hp : (p.factorial : ℝ) ≠ 0 := by exact_mod_cast p.factorial_ne_zero
  have hb1 : (b : ℝ) + 1 ≠ 0 := by positivity
  have hb2 : (b : ℝ) + 1 + 1 ≠ 0 := by positivity
  rw [cladeCreationCoeff, ite_eq_left ha, show b + 1 - 1 = b by omega,
    show p + 1 - 1 = p by omega, Nat.add_sub_add_right]
  push_cast
  rw [div_eq_div_iff (mul_ne_zero hb2 hp) (mul_ne_zero (mul_ne_zero hb1 hb2) hc)]
  linear_combination (2 * ((b : ℝ) + 1 + 1)) * hR

noncomputable def cladeTerm (c : ℕ → ℕ → ℝ) (A : Finset (Fin n))
    (π : Finpartition (Finset.univ : Finset (Fin n))) : ℝ :=
  if CladeSaturated π A then c π.parts.card (cladeInside π A).card else 0

theorem sum_cladeTerm_mergeBlocks (c : ℕ → ℕ → ℝ)
    {π : Finpartition (Finset.univ : Finset (Fin n))}
    {A : Finset (Fin n)} (hsat : CladeSaturated π A) :
    ∑ s ∈ π.parts.powersetCard 2, cladeTerm c A (mergeBlocks π s) =
      ((cladeInside π A).card.choose 2 : ℝ) *
          c (π.parts.card - 1) ((cladeInside π A).card - 1) +
        ((π.parts.card - (cladeInside π A).card).choose 2 : ℝ) *
          c (π.parts.card - 1) (cladeInside π A).card := by
  have hInP : cladeInside π A ⊆ π.parts := Finset.filter_subset _ _
  have hpt : ∀ s ∈ π.parts.powersetCard 2, cladeTerm c A (mergeBlocks π s) =
      (if s ⊆ cladeInside π A then
          c (π.parts.card - 1) ((cladeInside π A).card - 1) else 0) +
        (if s ⊆ π.parts \ cladeInside π A then
          c (π.parts.card - 1) (cladeInside π A).card else 0) := by
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
      rw [ite_eq_left h1, ite_eq_right h2, add_zero, cladeTerm, ite_eq_left hsat',
        show (mergeBlocks π s).parts.card = π.parts.card - 1 by omega,
        show (cladeInside (mergeBlocks π s) A).card = (cladeInside π A).card - 1 by omega]
    · by_cases h2 : s ⊆ π.parts \ cladeInside π A
      · have hout : ∀ b ∈ s, ¬ b ⊆ A := fun b hb hbA =>
          (Finset.mem_sdiff.mp (h2 hb)).2 (Finset.mem_filter.mpr ⟨hs hb, hbA⟩)
        obtain ⟨hsat', hins⟩ := cladeSaturated_mergeBlocks_outside hsat hs hne hout
        rw [ite_eq_right h1, ite_eq_left h2, zero_add, cladeTerm, ite_eq_left hsat', hins,
          show (mergeBlocks π s).parts.card = π.parts.card - 1 by omega]
      · obtain ⟨b, hb, hbI⟩ := Finset.not_subset.mp h1
        obtain ⟨a, ha, haO⟩ := Finset.not_subset.mp h2
        have hbA : ¬ b ⊆ A := fun h => hbI (Finset.mem_filter.mpr ⟨hs hb, h⟩)
        have haA : a ⊆ A := by
          by_contra h
          exact haO (Finset.mem_sdiff.mpr ⟨hs ha, fun hI => h (Finset.mem_filter.mp hI).2⟩)
        rw [ite_eq_right h1, ite_eq_right h2, add_zero, cladeTerm,
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

theorem cladeTerm_mergeBlocks_of_not_saturated (c : ℕ → ℕ → ℝ)
    {π : Finpartition (Finset.univ : Finset (Fin n))} {A : Finset (Fin n)}
    (hsat : ¬ CladeSaturated π A) (s : Finset (Finset (Fin n))) :
    cladeTerm c A (mergeBlocks π s) = 0 := by
  rw [cladeTerm, ite_eq_right (not_cladeSaturated_mergeBlocks hsat s)]

theorem cladeTerm_bot (c : ℕ → ℕ → ℝ) (A : Finset (Fin n)) :
    cladeTerm c A (⊥ : Finpartition (Finset.univ : Finset (Fin n))) = c n A.card := by
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
  rw [cladeTerm, ite_eq_left hsat, hin, Finset.card_map, hcard]

noncomputable def cladeBlockIndicator (A : Finset (Fin n))
    (π : Finpartition (Finset.univ : Finset (Fin n))) : ℝ :=
  if A ∈ π.parts then 1 else 0

theorem cladeBlockIndicator_eq_cladeTerm (A : Finset (Fin n)) :
    cladeBlockIndicator A = cladeTerm (fun _ j => if j = 1 then 1 else 0) A := by
  funext π
  simp only [cladeBlockIndicator, cladeTerm]
  by_cases hA : A ∈ π.parts
  · obtain ⟨hsat, hc⟩ := (mem_parts_iff_cladeSaturated_card π A).mp hA
    rw [ite_eq_left hA, ite_eq_left hsat, ite_eq_left hc]
  · rw [ite_eq_right hA]
    by_cases hsat : CladeSaturated π A
    · rw [ite_eq_left hsat, ite_eq_right fun hc => hA ((mem_parts_iff_cladeSaturated_card π A).mpr
        ⟨hsat, hc⟩)]
    · rw [ite_eq_right hsat]

noncomputable def cladeCreationPotential (A : Finset (Fin n))
    (π : Finpartition (Finset.univ : Finset (Fin n))) : ℝ :=
  cladeTerm cladeCreationCoeff A π

theorem cladeCreationPotential_of_card_le_one (A : Finset (Fin n))
    {π : Finpartition (Finset.univ : Finset (Fin n))} (hπ : π.parts.card ≤ 1) :
    cladeCreationPotential A π = 0 := by
  unfold cladeCreationPotential cladeTerm
  split_ifs with hsat
  · have hle : (cladeInside π A).card ≤ π.parts.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    rw [cladeCreationCoeff, ite_eq_right (by omega)]
  · rfl

theorem card_cladeInside_lt (π : Finpartition (Finset.univ : Finset (Fin n)))
    {A : Finset (Fin n)} (hA : A.card < n) : (cladeInside π A).card < π.parts.card := by
  apply Finset.card_lt_card
  rw [cladeInside, Finset.filter_ssubset]
  have hne : A ≠ Finset.univ := fun h => by
    rw [h, Finset.card_univ, Fintype.card_fin] at hA
    omega
  obtain ⟨x, hx⟩ : ∃ x, x ∉ A := by
    by_contra hall
    exact hne (Finset.eq_univ_iff_forall.mpr fun x => by
      by_contra hx
      exact hall ⟨x, hx⟩)
  exact ⟨π.part x, π.part_mem.2 (Finset.mem_univ x),
    fun hsub => hx (hsub (π.mem_part (Finset.mem_univ x)))⟩

/-- Source: kingman1982, eq. (2.2). -/
theorem partition_expect_eq_sum_mergeBlocks
    {π : Finpartition (Finset.univ : Finset (Fin n))} (hk : 2 ≤ π.parts.card)
    (f : Finpartition (Finset.univ : Finset (Fin n)) → ℝ) :
    (partitionChain (Fin n)).jumpChain.expect f π =
      (∑ s ∈ π.parts.powersetCard 2, f (mergeBlocks π s)) / (π.parts.card.choose 2 : ℝ) := by
  have hr : (partitionChain (Fin n)).rate π = (π.parts.card.choose 2 : ℝ) := by
    rw [partitionChain_rate, coalRate_cast_eq_choose]
  have hc : (π.parts.card.choose 2 : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hk).ne'
  rw [FinChain.expect_apply, RateChain.jumpChain_P,
    RateChain.sum_jumpMatrix_mul _ (by rw [hr]; exact hc), sum_partitionQ_reward, hr,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]
  field_simp
  ring

theorem partition_expect_of_card_le_one
    {π : Finpartition (Finset.univ : Finset (Fin n))} (hk : π.parts.card ≤ 1)
    (f : Finpartition (Finset.univ : Finset (Fin n)) → ℝ) :
    (partitionChain (Fin n)).jumpChain.expect f π = f π := by
  have ha := partitionChain_coalesced_isAbsorbingSet n π (mem_coalescedPartitions.mpr hk)
  rw [FinChain.expect_apply]
  simp only [ha.P_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    ↓reduceIte]

theorem cladeCreationPotential_drift {A : Finset (Fin n)} (hA : A.card < n)
    (π : Finpartition (Finset.univ : Finset (Fin n))) :
    (if A ∈ π.parts then 0
      else (partitionChain (Fin n)).jumpChain.expect (cladeBlockIndicator A) π) =
      cladeCreationPotential A π -
        (partitionChain (Fin n)).jumpChain.expect (cladeCreationPotential A) π := by
  rcases Nat.lt_or_ge π.parts.card 2 with hk | hk
  · rw [partition_expect_of_card_le_one (by omega), partition_expect_of_card_le_one (by omega),
      sub_self]
    split_ifs with h
    · rfl
    · rw [cladeBlockIndicator, ite_eq_right h]
  · have hc : (π.parts.card.choose 2 : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos hk).ne'
    rw [partition_expect_eq_sum_mergeBlocks hk, partition_expect_eq_sum_mergeBlocks hk,
      cladeBlockIndicator_eq_cladeTerm]
    unfold cladeCreationPotential
    by_cases hsat : CladeSaturated π A
    · have hlt := card_cladeInside_lt π hA
      have hstep := cladeCreationCoeff_step hlt
      have hiff : A ∈ π.parts ↔ (cladeInside π A).card = 1 := by
        rw [mem_parts_iff_cladeSaturated_card]
        exact ⟨fun h => h.2, fun h => ⟨hsat, h⟩⟩
      rw [sum_cladeTerm_mergeBlocks _ hsat, sum_cladeTerm_mergeBlocks _ hsat]
      rw [show cladeTerm cladeCreationCoeff A π =
        cladeCreationCoeff π.parts.card (cladeInside π A).card by rw [cladeTerm, ite_eq_left hsat]]
      generalize (cladeInside π A).card = j at hlt hstep hiff ⊢
      generalize π.parts.card = k at hk hc hlt hstep ⊢
      by_cases h1 : j = 1
      · subst h1
        rw [ite_eq_left (hiff.mpr rfl)]
        have hz : ¬ (2 : ℕ) ≤ 1 := by omega
        have hz' : ¬ (2 : ℕ) ≤ 1 - 1 := by omega
        simp only [cladeCreationCoeff, hz, hz', ↓reduceIte, mul_zero, add_zero, zero_div,
          sub_zero]
      · rw [ite_eq_right fun h => h1 (hiff.mp h)]
        have hind : ((j.choose 2 : ℕ) : ℝ) * (if j - 1 = 1 then (1 : ℝ) else 0) +
            (((k - j).choose 2 : ℕ) : ℝ) * (if j = 1 then (1 : ℝ) else 0) =
            if j = 2 then 1 else 0 := by
          rw [ite_eq_right h1, mul_zero, add_zero]
          by_cases h2 : j = 2
          · subst h2
            norm_num [Nat.choose]
          · rw [ite_eq_right h2, ite_eq_right (by omega), mul_zero]
        rw [hind, ← hstep]
        field_simp
    · have hAn : A ∉ π.parts := fun h =>
        hsat ((mem_parts_iff_cladeSaturated_card π A).mp h).1
      rw [ite_eq_right hAn, Finset.sum_eq_zero fun s _ =>
          cladeTerm_mergeBlocks_of_not_saturated _ hsat s,
        Finset.sum_eq_zero fun s _ => cladeTerm_mergeBlocks_of_not_saturated _ hsat s,
        cladeTerm, ite_eq_right hsat, zero_div, sub_zero]

theorem mem_parts_of_le_of_le {π σ τ : Finpartition (Finset.univ : Finset (Fin n))}
    {A : Finset (Fin n)} (h1 : π ≤ σ) (h2 : σ ≤ τ) (hπ : A ∈ π.parts) (hτ : A ∈ τ.parts) :
    A ∈ σ.parts := by
  obtain ⟨B, hB, hAB⟩ := h1 hπ
  obtain ⟨D, hD, hBD⟩ := h2 hB
  have hDA : D = A := by
    by_contra hne
    have hd : Disjoint D A := τ.disjoint hD hτ hne
    obtain ⟨x, hx⟩ := π.nonempty_of_mem_parts hπ
    exact (Finset.disjoint_left.mp hd) (hBD (hAB hx)) hx
  have hBA : B = A := le_antisymm (hDA ▸ hBD) hAB
  exact hBA ▸ hB

def cladeSeenBy (A : Finset (Fin n)) (N : ℕ) :
    Set (ℕ → Finpartition (Finset.univ : Finset (Fin n))) :=
  {ω | ∃ k ≤ N, A ∈ (ω k).parts}

theorem measurableSet_cladeSeenBy (A : Finset (Fin n)) (N : ℕ) :
    MeasurableSet (cladeSeenBy A N) := by
  have h : cladeSeenBy A N = ⋃ k ∈ Finset.range (N + 1),
      (fun ω : ℕ → Finpartition (Finset.univ : Finset (Fin n)) => ω k) ⁻¹'
        {π | A ∈ π.parts} := by
    ext ω
    simp only [cladeSeenBy, Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_range,
      Set.mem_preimage, exists_prop, Nat.lt_succ_iff]
  rw [h]
  exact Finset.measurableSet_biUnion _ fun k _ =>
    measurable_pi_apply k (MeasurableSet.of_discrete
      (s := {π : Finpartition (Finset.univ : Finset (Fin n)) | A ∈ π.parts}))

theorem measureReal_cladeSeenBy_succ {A : Finset (Fin n)} (hA : A.card < n) (N : ℕ) :
    ((partitionChain (Fin n)).jumpChain.pathLaw ⊥).real (cladeSeenBy A (N + 1)) =
      ((partitionChain (Fin n)).jumpChain.pathLaw ⊥).real (cladeSeenBy A N) +
        (∫ ω, cladeCreationPotential A (ω N) ∂(partitionChain (Fin n)).jumpChain.pathLaw ⊥ -
          ∫ ω, cladeCreationPotential A (ω (N + 1))
            ∂(partitionChain (Fin n)).jumpChain.pathLaw ⊥) := by
  set C := (partitionChain (Fin n)).jumpChain with hC
  set B : Set (ℕ → Finpartition (Finset.univ : Finset (Fin n))) :=
    {ω | A ∉ (ω N).parts} with hBdef
  set E : Set (ℕ → Finpartition (Finset.univ : Finset (Fin n))) :=
    {ω | A ∈ (ω (N + 1)).parts} with hEdef
  have hBn : MeasurableSet[Filtration.piLE
      (X := fun _ : ℕ => Finpartition (Finset.univ : Finset (Fin n))) N] B :=
    (DiscreteProcess.measurable_eval_piLE
      (S := Finpartition (Finset.univ : Finset (Fin n))) N)
      (MeasurableSet.of_discrete
        (s := {π : Finpartition (Finset.univ : Finset (Fin n)) | A ∉ π.parts}))
  have hBm : MeasurableSet B := (Filtration.piLE.le N) B hBn
  have hEm : MeasurableSet E := by
    have h : Measurable (fun ω : ℕ → Finpartition (Finset.univ : Finset (Fin n)) =>
        ω (N + 1)) := measurable_pi_apply (N + 1)
    exact h (MeasurableSet.of_discrete
      (s := {π : Finpartition (Finset.univ : Finset (Fin n)) | A ∈ π.parts}))
  have hHm := measurableSet_cladeSeenBy A N
  have hunion : cladeSeenBy A (N + 1) = cladeSeenBy A N ∪ ((B ∩ E) \ cladeSeenBy A N) := by
    ext ω
    simp only [cladeSeenBy, Set.mem_ofPred_eq, Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff,
      hBdef, hEdef]
    constructor
    · rintro ⟨k, hk, hk'⟩
      by_cases hH : ∃ k ≤ N, A ∈ (ω k).parts
      · exact Or.inl hH
      · have hkN : k = N + 1 := by
          by_contra hne
          exact hH ⟨k, by omega, hk'⟩
        subst hkN
        exact Or.inr ⟨⟨fun h => hH ⟨N, le_rfl, h⟩, hk'⟩, hH⟩
    · rintro (⟨k, hk, hk'⟩ | ⟨⟨-, h⟩, -⟩)
      · exact ⟨k, by omega, hk'⟩
      · exact ⟨N + 1, le_rfl, h⟩
  have hmono : ∀ᵐ ω ∂C.pathLaw ⊥, Monotone ω := (kingmanAncestral (Fin n)).ae_monotone ⊥
  have hae : ((B ∩ E) \ cladeSeenBy A N : Set _) =ᵐ[C.pathLaw ⊥] (B ∩ E : Set _) := by
    filter_upwards [hmono] with ω hω
    apply propext
    constructor
    · exact fun h => h.1
    · rintro ⟨hB, hE⟩
      refine ⟨⟨hB, hE⟩, ?_⟩
      rintro ⟨k, hk, hk'⟩
      exact hB (mem_parts_of_le_of_le (hω hk) (hω (Nat.le_succ N)) hk' hE)
  have hprob : (C.pathLaw ⊥).real (B ∩ E) =
      ∫ ω in B, cladeBlockIndicator A (ω (N + 1)) ∂C.pathLaw ⊥ := by
    have hind : (fun ω : ℕ → Finpartition (Finset.univ : Finset (Fin n)) =>
        cladeBlockIndicator A (ω (N + 1))) = Set.indicator E fun _ => (1 : ℝ) := by
      funext ω
      simp only [cladeBlockIndicator, Set.indicator, hEdef, Set.mem_ofPred_eq]
    rw [hind, setIntegral_indicator hEm, setIntegral_const, smul_eq_mul, mul_one]
  have hdrift : ∫ ω in B, C.expect (cladeBlockIndicator A) (ω N) ∂C.pathLaw ⊥ =
      ∫ ω, (cladeCreationPotential A (ω N) -
        C.expect (cladeCreationPotential A) (ω N)) ∂C.pathLaw ⊥ := by
    rw [← integral_indicator hBm]
    apply integral_congr_ae
    filter_upwards with ω
    rw [← cladeCreationPotential_drift hA (ω N)]
    by_cases h : A ∈ (ω N).parts
    · rw [ite_eq_left h, Set.indicator_of_notMem (show ω ∉ B from fun hB => hB h)]
    · rw [ite_eq_right h, Set.indicator_of_mem (show ω ∈ B from h)]
  have hnext : ∫ ω, C.expect (cladeCreationPotential A) (ω N) ∂C.pathLaw ⊥ =
      ∫ ω, cladeCreationPotential A (ω (N + 1)) ∂C.pathLaw ⊥ := by
    have h := C.setIntegral_eval_succ ⊥ N (cladeCreationPotential A)
      (B := Set.univ) MeasurableSet.univ
    rw [setIntegral_univ, setIntegral_univ] at h
    exact h.symm
  rw [hunion, measureReal_union Set.disjoint_sdiff_right ((hBm.inter hEm).diff hHm),
    measureReal_congr hae, hprob, C.setIntegral_eval_succ ⊥ N _ hBn, hdrift,
    integral_sub (C.integrable_eval _ N ⊥) (C.integrable_eval _ N ⊥), hnext]

theorem partition_path_zero (π : Finpartition (Finset.univ : Finset (Fin n))) :
    ∀ᵐ ω ∂(partitionChain (Fin n)).jumpChain.pathLaw π, ω 0 = π := by
  have h := (partitionChain (Fin n)).jumpChain.pathLaw_real_eval_notMem 0 π {π}
  have hs : (partitionChain (Fin n)).jumpChain.survival {π} 0 π = 0 := by
    simp [FinChain.survival, FinChain.stepN_zero, Matrix.one_apply]
  rw [hs, measureReal_eq_zero_iff (measure_ne_top _ _)] at h
  rw [ae_iff]
  convert h using 2
  ext ω
  simp

theorem measureReal_cladeSeenBy {A : Finset (Fin n)} (hA : A.card < n) (N : ℕ) :
    ((partitionChain (Fin n)).jumpChain.pathLaw ⊥).real (cladeSeenBy A N) =
      cladeBlockIndicator A ⊥ + cladeCreationPotential A ⊥ -
        ∫ ω, cladeCreationPotential A (ω N) ∂(partitionChain (Fin n)).jumpChain.pathLaw ⊥ := by
  induction N with
  | zero =>
    have h0 := partition_path_zero (⊥ : Finpartition (Finset.univ : Finset (Fin n)))
    have hint : ∫ ω, cladeCreationPotential A (ω 0)
        ∂(partitionChain (Fin n)).jumpChain.pathLaw ⊥ = cladeCreationPotential A ⊥ := by
      rw [integral_congr_ae (g := fun _ => cladeCreationPotential A ⊥)
        (by filter_upwards [h0] with ω hω; rw [hω])]
      simp
    rw [hint, add_sub_cancel_right]
    by_cases hb : A ∈ (⊥ : Finpartition (Finset.univ : Finset (Fin n))).parts
    · have hae : (cladeSeenBy A 0 : Set _) =ᵐ[(partitionChain (Fin n)).jumpChain.pathLaw ⊥]
          (Set.univ : Set _) := by
        filter_upwards [h0] with ω hω
        exact propext ⟨fun _ => trivial, fun _ => ⟨0, le_rfl, hω ▸ hb⟩⟩
      rw [measureReal_congr hae, cladeBlockIndicator, ite_eq_left hb]
      simp
    · have hae : (cladeSeenBy A 0 : Set _) =ᵐ[(partitionChain (Fin n)).jumpChain.pathLaw ⊥]
          (∅ : Set _) := by
        filter_upwards [h0] with ω hω
        apply propext
        constructor
        · rintro ⟨k, hk, hk'⟩
          have hk0 : k = 0 := by omega
          subst hk0
          exact hb (hω ▸ hk')
        · exact fun h => h.elim
      rw [measureReal_congr hae, cladeBlockIndicator, ite_eq_right hb]
      simp
  | succ N ih =>
    rw [measureReal_cladeSeenBy_succ hA N, ih]
    ring

theorem kingman_clade_probability {n : ℕ} (A : Finset (Fin n))
    (ha : 1 ≤ A.card) (han : A.card < n) :
    ((partitionChain (Fin n)).jumpChain.pathLaw ⊥).real {ω | ∃ k, A ∈ (ω k).parts} =
      2 * (n : ℝ) / ((A.card : ℝ) * ((A.card : ℝ) + 1) * (n.choose A.card : ℝ)) := by
  have hcount := partition_path_countdown_general n
  have hae : ({ω | ∃ k, A ∈ (ω k).parts} : Set _)
      =ᵐ[(partitionChain (Fin n)).jumpChain.pathLaw ⊥] (cladeSeenBy A (n - 1) : Set _) := by
    filter_upwards [hcount] with ω hω
    apply propext
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_, hk⟩
      by_contra hlt
      have hcard : (ω k).parts.card = 1 := by
        rw [hω k]
        omega
      obtain ⟨D, hD⟩ := Finset.card_eq_one.mp hcard
      have hAD : A = D := by
        rw [hD] at hk
        exact Finset.mem_singleton.mp hk
      have hsup := (ω k).sup_parts
      rw [hD, Finset.sup_singleton, id] at hsup
      rw [hAD, hsup, Finset.card_univ, Fintype.card_fin] at han
      omega
    · rintro ⟨k, -, hk⟩
      exact ⟨k, hk⟩
  have hzero : ∫ ω, cladeCreationPotential A (ω (n - 1))
      ∂(partitionChain (Fin n)).jumpChain.pathLaw ⊥ = 0 := by
    rw [integral_congr_ae (g := fun _ => (0 : ℝ))
      (by
        filter_upwards [hcount] with ω hω
        exact cladeCreationPotential_of_card_le_one A (by rw [hω]; omega))]
    simp
  rw [measureReal_congr hae, measureReal_cladeSeenBy han, hzero, sub_zero,
    cladeBlockIndicator_eq_cladeTerm, cladeCreationPotential, cladeTerm_bot, cladeTerm_bot]
  rcases Nat.eq_or_lt_of_le ha with h1 | h2
  · have hn0 : (n : ℝ) ≠ 0 := by
      have : 0 < n := by omega
      positivity
    rw [← h1, cladeCreationCoeff, ite_eq_left rfl, ite_eq_right (by omega), Nat.choose_one_right]
    push_cast
    field_simp
    ring
  · rw [ite_eq_right (by omega), zero_add, cladeCreationCoeff_eq_choose h2 han.le]

theorem kingman_expected_cherries {n : ℕ} (hn : 3 ≤ n) :
    ∑ A ∈ (univ : Finset (Fin n)).powersetCard 2,
        ((partitionChain (Fin n)).jumpChain.pathLaw ⊥).real {ω | ∃ k, A ∈ (ω k).parts} =
      (n : ℝ) / 3 := by
  have hterm : ∀ A ∈ (univ : Finset (Fin n)).powersetCard 2,
      ((partitionChain (Fin n)).jumpChain.pathLaw ⊥).real {ω | ∃ k, A ∈ (ω k).parts} =
        2 * (n : ℝ) / ((2 : ℝ) * ((2 : ℝ) + 1) * (n.choose 2 : ℝ)) := by
    intro A hA
    have hc := (Finset.mem_powersetCard.mp hA).2
    have h := kingman_clade_probability A (by omega) (by omega)
    rw [hc] at h
    exact_mod_cast h
  have hc : (n.choose 2 : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : 2 ≤ n)).ne'
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

end Rhone.Coalescent
