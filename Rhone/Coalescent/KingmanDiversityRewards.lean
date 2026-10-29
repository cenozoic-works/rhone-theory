/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.KingmanDiversityGenerator
public import Rhone.MarkovChain.JumpHold

/-!
# Labelled Kingman diversity reward potentials and first moments

Source: kingman1982, sec. 1, eq. (1.1)–(1.4), (1.7); tajima1989, p. 585, eq. (6)–(7). -/

@[expose] public section
namespace Rhone.Coalescent
open Finset Rhone.Combinatorics MarkovChain

theorem kingmanBlockMassMoment_coalesced {n : ℕ} (hn : 0 < n) (k : ℕ)
    (π : Finpartition (Finset.univ : Finset (Fin n)))
    (hπ : π ∈ coalescedPartitions (Fin n)) :
    kingmanBlockMassMoment n k π = 1 := by
  classical
  have hsum := π.sum_card_parts
  simp only [Finset.card_univ, Fintype.card_fin] at hsum
  have hne : π.parts.Nonempty := by
    by_contra h
    have he := Finset.not_nonempty_iff_eq_empty.mp h
    simp [he] at hsum
    omega
  obtain ⟨B, hB⟩ := hne
  have hc := mem_coalescedPartitions.mp hπ
  have hparts : π.parts = {B} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨hB, ?_⟩
    intro C hC
    exact (Finset.card_le_one.mp hc) C hC B hB
  rw [hparts, Finset.sum_singleton] at hsum
  simp [kingmanBlockMassMoment, hparts, hsum, div_self (by positivity : (n : ℝ) ≠ 0)]

theorem kingmanBlockMassMoment_bot (n k : ℕ) :
    kingmanBlockMassMoment n k (⊥ : Finpartition (Finset.univ : Finset (Fin n))) =
      n * (1 / (n : ℝ)) ^ k := by
  classical
  unfold kingmanBlockMassMoment
  rw [Finpartition.parts_bot, Finset.sum_map]
  simp

noncomputable def kingmanDiversityReward (n : ℕ)
    (π : Finpartition (Finset.univ : Finset (Fin n))) : ℝ :=
  (2 * n / (n - 1 : ℝ)) * (1 - kingmanBlockMassMoment n 2 π)

noncomputable def kingmanDiversityMutationReward (n : ℕ)
    (π : Finpartition (Finset.univ : Finset (Fin n))) : ℝ :=
  (2 * n / (n - 1 : ℝ)) ^ 2 *
    (kingmanBlockMassMoment n 2 π - 2 * kingmanBlockMassMoment n 3 π +
      kingmanBlockMassMoment n 4 π)

noncomputable def kingmanDiversityMutationPotential (n : ℕ)
    (π : Finpartition (Finset.univ : Finset (Fin n))) : ℝ :=
  (2 * n / (n - 1 : ℝ)) ^ 2 *
    ((2 / 3 : ℝ) * (1 - kingmanBlockMassMoment n 3 π) -
      (1 / 2 : ℝ) * (1 - kingmanBlockMassMoment n 2 π ^ 2))

noncomputable def kingmanDiversitySquarePotential (n : ℕ)
    (π : Finpartition (Finset.univ : Finset (Fin n))) : ℝ :=
  (2 * n / (n - 1 : ℝ)) ^ 2 *
    (2 * (1 - kingmanBlockMassMoment n 2 π) +
      (8 / 9 : ℝ) * (1 - kingmanBlockMassMoment n 3 π) +
      (2 / 3 : ℝ) * (1 - kingmanBlockMassMoment n 4 π) -
      (7 / 3 : ℝ) * (1 - kingmanBlockMassMoment n 2 π ^ 2))

theorem kingmanDiversityReward_generator {n : ℕ} (hn : 0 < n)
    (π : Finpartition (Finset.univ : Finset (Fin n))) :
    ∑ σ, (partitionChain (Fin n)).Q π σ * kingmanDiversityReward n σ =
      -kingmanDiversityReward n π := by
  let Q := (partitionChain (Fin n)).Q
  have hs (a : ℝ) (f : Finpartition (Finset.univ : Finset (Fin n)) → ℝ) :
      (∑ σ, Q π σ * (a * f σ)) = a * ∑ σ, Q π σ * f σ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    ring
  have h1 : (∑ σ, Q π σ * 1) = 0 := by
    simpa using (partitionChain (Fin n)).row_sum π
  change (∑ σ, Q π σ * kingmanDiversityReward n σ) = _
  unfold kingmanDiversityReward
  simp only [hs, mul_sub, Finset.sum_sub_distrib, h1]
  dsimp only [Q]
  rw [kingman_generator_mass_two hn π]
  ring

theorem kingmanDiversityMutationPotential_generator {n : ℕ} (hn : 0 < n)
    (π : Finpartition (Finset.univ : Finset (Fin n))) :
    ∑ σ, (partitionChain (Fin n)).Q π σ * kingmanDiversityMutationPotential n σ =
      -kingmanDiversityMutationReward n π := by
  let Q := (partitionChain (Fin n)).Q
  have hs (a : ℝ) (f : Finpartition (Finset.univ : Finset (Fin n)) → ℝ) :
      (∑ σ, Q π σ * (a * f σ)) = a * ∑ σ, Q π σ * f σ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    ring
  have h1 : (∑ σ, Q π σ * 1) = 0 := by
    simpa using (partitionChain (Fin n)).row_sum π
  change (∑ σ, Q π σ * kingmanDiversityMutationPotential n σ) = _
  unfold kingmanDiversityMutationPotential kingmanDiversityMutationReward
  simp only [hs, mul_sub, mul_add, Finset.sum_sub_distrib, h1]
  dsimp only [Q]
  rw [kingman_generator_mass_three hn π, kingman_generator_mass_two_sq hn π]
  ring

theorem kingmanDiversitySquarePotential_generator {n : ℕ} (hn : 0 < n)
    (π : Finpartition (Finset.univ : Finset (Fin n))) :
    ∑ σ, (partitionChain (Fin n)).Q π σ * kingmanDiversitySquarePotential n σ =
      -2 * kingmanDiversityReward n π ^ 2 := by
  let Q := (partitionChain (Fin n)).Q
  have hs (a : ℝ) (f : Finpartition (Finset.univ : Finset (Fin n)) → ℝ) :
      (∑ σ, Q π σ * (a * f σ)) = a * ∑ σ, Q π σ * f σ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    ring
  have h1 : (∑ σ, Q π σ * 1) = 0 := by
    simpa using (partitionChain (Fin n)).row_sum π
  change (∑ σ, Q π σ * kingmanDiversitySquarePotential n σ) = _
  unfold kingmanDiversitySquarePotential kingmanDiversityReward
  simp only [hs, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, h1]
  dsimp only [Q]
  rw [kingman_generator_mass_two hn π]
  rw [kingman_generator_mass_three hn π, kingman_generator_mass_four hn π,
    kingman_generator_mass_two_sq hn π]
  ring

/-- Source: kingman1982, eq. (1.10)–(1.12). -/
theorem partitionChain_coalesced_isAbsorbingSet (n : ℕ) :
    (partitionChain (Fin n)).jumpChain.IsAbsorbingSet (coalescedPartitions (Fin n)) := by
  apply Rhone.MarkovChain.RateChain.jumpChain_isAbsorbingSet
  intro π hπ
  rw [partitionChain_rate]
  exact_mod_cast coalRate_eq_zero (mem_coalescedPartitions.mp hπ)

/-- Source: kingman1982, eq. (1.10)–(1.12). -/
theorem partitionChain_coalesced_reaches (n : ℕ) :
    (partitionChain (Fin n)).jumpChain.Reaches (coalescedPartitions (Fin n)) := by
  have h := (partitionChain_lumps (α := Fin n)).jumpChain_lumps
    (fun _ _ => partitionChain_Q_eq_zero_of_blockCount_eq)
  exact h.reaches_preimage (blockChain_reaches (Fintype.card (Fin n)))

/-- Source: kingman1982, eq. (1.6)–(1.7). -/
theorem partitionChain_transient_rate_pos (n : ℕ)
    (π : Finpartition (Finset.univ : Finset (Fin n)))
    (hπ : π ∉ coalescedPartitions (Fin n)) :
    0 < (partitionChain (Fin n)).rate π := by
  rw [partitionChain_rate]
  have hk : 2 ≤ π.parts.card := by
    have := mt mem_coalescedPartitions.mpr hπ
    omega
  exact_mod_cast coalRate_pos hk

theorem kingmanDiversityReward_nonneg {n : ℕ} (hn : 2 ≤ n)
    (π : Finpartition (Finset.univ : Finset (Fin n))) :
    0 ≤ kingmanDiversityReward n π := by
  have hmass (B : Finset (Fin n)) : 0 ≤ (B.card : ℝ) / n ∧ (B.card : ℝ) / n ≤ 1 := by
    refine ⟨by positivity, ?_⟩
    apply (div_le_one (by positivity : (0 : ℝ) < n)).mpr
    have h := Finset.card_le_univ B
    simp only [Fintype.card_fin] at h
    exact_mod_cast h
  have hm : kingmanBlockMassMoment n 2 π ≤ 1 := by
    rw [← sum_kingmanBlockMass (by omega) π]
    apply Finset.sum_le_sum
    intro B _
    have h := hmass B
    nlinarith
  unfold kingmanDiversityReward
  apply mul_nonneg
  · apply div_nonneg (by positivity)
    have h : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  · linarith

theorem kingmanDiversityMutationReward_nonneg (n : ℕ)
    (π : Finpartition (Finset.univ : Finset (Fin n))) :
    0 ≤ kingmanDiversityMutationReward n π := by
  have he : kingmanBlockMassMoment n 2 π - 2 * kingmanBlockMassMoment n 3 π +
      kingmanBlockMassMoment n 4 π =
      ∑ B ∈ π.parts, (((B.card : ℝ) / n) * (1 - (B.card : ℝ) / n)) ^ 2 := by
    unfold kingmanBlockMassMoment
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro B _
    ring
  unfold kingmanDiversityMutationReward
  rw [he]
  exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun B _ => sq_nonneg _)

theorem kingmanDiversityReward_eq_expectedCost {n : ℕ} (hn : 0 < n) :
    kingmanDiversityReward n = (partitionChain (Fin n)).expectedCost
      (coalescedPartitions (Fin n)) (kingmanDiversityReward n) := by
  apply Rhone.MarkovChain.RateChain.eq_expectedCost_of_generator
    (partitionChain_coalesced_isAbsorbingSet n) (partitionChain_coalesced_reaches n)
    (fun π hπ => (partitionChain_transient_rate_pos n π hπ).ne')
  · intro π hπ
    simp [kingmanDiversityReward, kingmanBlockMassMoment_coalesced hn _ π hπ]
  · intro π _
    exact kingmanDiversityReward_generator hn π

theorem kingmanDiversityMutationPotential_eq_expectedCost {n : ℕ} (hn : 0 < n) :
    kingmanDiversityMutationPotential n = (partitionChain (Fin n)).expectedCost
      (coalescedPartitions (Fin n)) (kingmanDiversityMutationReward n) := by
  apply Rhone.MarkovChain.RateChain.eq_expectedCost_of_generator
    (partitionChain_coalesced_isAbsorbingSet n) (partitionChain_coalesced_reaches n)
    (fun π hπ => (partitionChain_transient_rate_pos n π hπ).ne')
  · intro π hπ
    simp [kingmanDiversityMutationPotential, kingmanBlockMassMoment_coalesced hn _ π hπ]
  · intro π _
    exact kingmanDiversityMutationPotential_generator hn π

theorem kingmanDiversitySquarePotential_eq_expectedCost {n : ℕ} (hn : 0 < n) :
    kingmanDiversitySquarePotential n = (partitionChain (Fin n)).expectedCost
      (coalescedPartitions (Fin n)) (fun π => 2 * kingmanDiversityReward n π ^ 2) := by
  apply Rhone.MarkovChain.RateChain.eq_expectedCost_of_generator
    (partitionChain_coalesced_isAbsorbingSet n) (partitionChain_coalesced_reaches n)
    (fun π hπ => (partitionChain_transient_rate_pos n π hπ).ne')
  · intro π hπ
    simp [kingmanDiversitySquarePotential, kingmanBlockMassMoment_coalesced hn _ π hπ]
  · intro π _
    simpa only [neg_mul] using kingmanDiversitySquarePotential_generator hn π

theorem lintegral_kingmanDiversityReward {n : ℕ} (hn : 2 ≤ n)
    (π : Finpartition (Finset.univ : Finset (Fin n))) :
    ∫⁻ h, (partitionChain (Fin n)).costBefore (coalescedPartitions (Fin n))
      (kingmanDiversityReward n) h ∂(partitionChain (Fin n)).jumpHoldLaw π =
        ENNReal.ofReal (kingmanDiversityReward n π) := by
  rw [(partitionChain (Fin n)).lintegral_costBefore
    (partitionChain_coalesced_isAbsorbingSet n) (partitionChain_coalesced_reaches n)
    (kingmanDiversityReward_nonneg hn)]
  rw [← kingmanDiversityReward_eq_expectedCost (by omega : 0 < n)]

theorem lintegral_kingmanDiversityMutationReward {n : ℕ} (hn : 0 < n)
    (π : Finpartition (Finset.univ : Finset (Fin n))) :
    ∫⁻ h, (partitionChain (Fin n)).costBefore (coalescedPartitions (Fin n))
      (kingmanDiversityMutationReward n) h ∂(partitionChain (Fin n)).jumpHoldLaw π =
        ENNReal.ofReal (kingmanDiversityMutationPotential n π) := by
  rw [(partitionChain (Fin n)).lintegral_costBefore
    (partitionChain_coalesced_isAbsorbingSet n) (partitionChain_coalesced_reaches n)
    (kingmanDiversityMutationReward_nonneg n)]
  rw [← kingmanDiversityMutationPotential_eq_expectedCost hn]

end Rhone.Coalescent
