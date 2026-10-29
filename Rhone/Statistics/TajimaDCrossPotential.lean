/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.TajimaFiniteMoments
public import Rhone.Statistics.TajimaInitialPotentials
public import Rhone.Coalescent.KingmanDiversityMoments

/-!
# Potentials for the joint moment of pair-separation exposure and tree length

Source: tajima1989, p. 587, eq. (24); watterson1975, p. 258, eq. (1.4a); durrett2008, eq. (1.21). -/

@[expose] public section
namespace Rhone.Statistics
open MeasureTheory ProbabilityTheory Finset Coalescent Rhone.Combinatorics MarkovChain Probability

noncomputable def kingmanJumpReward (n : ℕ)
    (c : Finpartition (Finset.univ : Finset (Fin n)) → ℝ)
    (π : Finpartition (Finset.univ : Finset (Fin n))) : ℝ :=
  if π ∈ coalescedPartitions (Fin n) then 0 else c π / (partitionChain (Fin n)).rate π

/-- Source: watterson1975, p. 258, eq. (1.4a), p. 267; durrett2008, eq. (1.21). -/
noncomputable def kingmanLengthWeight (k : ℕ) : ℝ := 2 * (harmonic (k - 1) : ℝ)

noncomputable def kingmanDiversityLengthWeight (k : ℕ) : ℝ :=
  ((k : ℝ) + 2) / k + 2 * (harmonic (k - 1) : ℝ)

/-- Source: watterson1975, p. 258, eq. (1.4a), p. 267; durrett2008, eq. (1.21). -/
noncomputable def kingmanLengthPotential (n : ℕ)
    (π : Finpartition (Finset.univ : Finset (Fin n))) : ℝ :=
  kingmanLengthWeight π.parts.card

noncomputable def kingmanDiversityLengthReward (n : ℕ)
    (π : Finpartition (Finset.univ : Finset (Fin n))) : ℝ :=
  kingmanDiversityReward n π * ((π.parts.card : ℝ) + kingmanLengthWeight π.parts.card)

noncomputable def kingmanDiversityLengthPotential (n : ℕ)
    (π : Finpartition (Finset.univ : Finset (Fin n))) : ℝ :=
  kingmanDiversityReward n π * kingmanDiversityLengthWeight π.parts.card

private theorem harmonic_succ_real (m : ℕ) :
    (harmonic (m + 1) : ℝ) = (harmonic m : ℝ) + 1 / ((m : ℝ) + 1) := by
  rw [harmonic_succ]
  push_cast
  ring

private theorem length_weight_step (m : ℕ) :
    (coalRate (m + 2) : ℝ) * (kingmanLengthWeight (m + 1) - kingmanLengthWeight (m + 2)) =
      -((m : ℝ) + 2) := by
  have e1 : m + 1 - 1 = m := rfl
  have e2 : m + 2 - 1 = m + 1 := rfl
  have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
  unfold kingmanLengthWeight coalRate
  rw [e1, e2, harmonic_succ_real]
  push_cast
  field_simp
  ring

private theorem diversity_length_weight_step (m : ℕ) :
    ((coalRate (m + 2) : ℝ) - 1) * kingmanDiversityLengthWeight (m + 1) -
      (coalRate (m + 2) : ℝ) * kingmanDiversityLengthWeight (m + 2) =
    -(((m : ℝ) + 2) + kingmanLengthWeight (m + 2)) := by
  have e1 : m + 1 - 1 = m := rfl
  have e2 : m + 2 - 1 = m + 1 := rfl
  have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
  have hm2 : (m : ℝ) + 2 ≠ 0 := by positivity
  unfold kingmanDiversityLengthWeight kingmanLengthWeight coalRate
  rw [e1, e2, harmonic_succ_real]
  push_cast
  field_simp
  ring

private theorem generator_card (n : ℕ) (F : ℕ → ℝ)
    (π : Finpartition (Finset.univ : Finset (Fin n))) :
    ∑ σ, (partitionChain (Fin n)).Q π σ * F σ.parts.card =
      (coalRate π.parts.card : ℝ) * (F (π.parts.card - 1) - F π.parts.card) := by
  classical
  rw [sum_partitionQ_reward π (fun σ => F σ.parts.card)]
  have he : ∀ s ∈ π.parts.powersetCard 2,
      F (mergeBlocks π s).parts.card - F π.parts.card =
        F (π.parts.card - 1) - F π.parts.card := by
    intro s hs
    rw [Finset.mem_powersetCard] at hs
    have hc := card_parts_mergeBlocks hs.1 hs.2
    rw [show (mergeBlocks π s).parts.card = π.parts.card - 1 by omega]
  rw [Finset.sum_congr rfl he, Finset.sum_const, nsmul_eq_mul, Finset.card_powersetCard,
    coalRate_cast_eq_choose]

private theorem generator_diversity_mul_card {n : ℕ} (hn : 0 < n) (F : ℕ → ℝ)
    (π : Finpartition (Finset.univ : Finset (Fin n))) :
    ∑ σ, (partitionChain (Fin n)).Q π σ * (kingmanDiversityReward n σ * F σ.parts.card) =
      kingmanDiversityReward n π *
        (((coalRate π.parts.card : ℝ) - 1) * F (π.parts.card - 1) -
          (coalRate π.parts.card : ℝ) * F π.parts.card) := by
  classical
  have hd := kingmanDiversityReward_generator hn π
  rw [sum_partitionQ_reward π (kingmanDiversityReward n)] at hd
  rw [sum_partitionQ_reward π (fun σ => kingmanDiversityReward n σ * F σ.parts.card)]
  have he : ∀ s ∈ π.parts.powersetCard 2,
      kingmanDiversityReward n (mergeBlocks π s) * F (mergeBlocks π s).parts.card -
          kingmanDiversityReward n π * F π.parts.card =
        F (π.parts.card - 1) *
            (kingmanDiversityReward n (mergeBlocks π s) - kingmanDiversityReward n π) +
          kingmanDiversityReward n π * (F (π.parts.card - 1) - F π.parts.card) := by
    intro s hs
    rw [Finset.mem_powersetCard] at hs
    have hc := card_parts_mergeBlocks hs.1 hs.2
    rw [show (mergeBlocks π s).parts.card = π.parts.card - 1 by omega]
    ring
  rw [Finset.sum_congr rfl he, Finset.sum_add_distrib, ← Finset.mul_sum, hd, Finset.sum_const,
    nsmul_eq_mul, Finset.card_powersetCard, coalRate_cast_eq_choose]
  ring

/-- Source: watterson1975, p. 264, eq. (2.5); durrett2008, eq. (1.21). -/
theorem kingmanLengthPotential_coalesced (n : ℕ)
    (π : Finpartition (Finset.univ : Finset (Fin n)))
    (hπ : π ∈ coalescedPartitions (Fin n)) : kingmanLengthPotential n π = 0 := by
  have hk := mem_coalescedPartitions.mp hπ
  have h0 : π.parts.card - 1 = 0 := by omega
  simp [kingmanLengthPotential, kingmanLengthWeight, h0]

theorem kingmanDiversityLengthPotential_coalesced {n : ℕ} (hn : 0 < n)
    (π : Finpartition (Finset.univ : Finset (Fin n)))
    (hπ : π ∈ coalescedPartitions (Fin n)) : kingmanDiversityLengthPotential n π = 0 := by
  simp [kingmanDiversityLengthPotential, kingmanDiversityReward,
    kingmanBlockMassMoment_coalesced hn _ π hπ]

theorem kingmanDiversityReward_coalesced {n : ℕ} (hn : 0 < n)
    (π : Finpartition (Finset.univ : Finset (Fin n)))
    (hπ : π ∈ coalescedPartitions (Fin n)) : kingmanDiversityReward n π = 0 := by
  simp [kingmanDiversityReward, kingmanBlockMassMoment_coalesced hn _ π hπ]

/-- Source: watterson1975, p. 258, eq. (1.4a), p. 267; durrett2008, eq. (1.21). -/
theorem kingmanLengthPotential_eq_expectedCost (n : ℕ) :
    kingmanLengthPotential n = (partitionChain (Fin n)).expectedCost
      (coalescedPartitions (Fin n)) (fun π => (π.parts.card : ℝ)) := by
  apply Rhone.MarkovChain.RateChain.eq_expectedCost_of_generator
    (partitionChain_coalesced_isAbsorbingSet n) (partitionChain_coalesced_reaches n)
    (fun π hπ => (partitionChain_transient_rate_pos n π hπ).ne')
  · intro π hπ
    exact kingmanLengthPotential_coalesced n π hπ
  · intro π hπ
    have hk : 2 ≤ π.parts.card := by
      have := mt mem_coalescedPartitions.mpr hπ
      omega
    obtain ⟨m, hm⟩ : ∃ m, π.parts.card = m + 2 := ⟨π.parts.card - 2, by omega⟩
    have e2 : m + 2 - 1 = m + 1 := rfl
    change ∑ σ, (partitionChain (Fin n)).Q π σ * kingmanLengthWeight σ.parts.card = _
    rw [generator_card n kingmanLengthWeight π, hm, e2, length_weight_step m]
    push_cast
    ring

theorem kingmanDiversityLengthPotential_eq_expectedCost {n : ℕ} (hn : 0 < n) :
    kingmanDiversityLengthPotential n = (partitionChain (Fin n)).expectedCost
      (coalescedPartitions (Fin n)) (kingmanDiversityLengthReward n) := by
  apply Rhone.MarkovChain.RateChain.eq_expectedCost_of_generator
    (partitionChain_coalesced_isAbsorbingSet n) (partitionChain_coalesced_reaches n)
    (fun π hπ => (partitionChain_transient_rate_pos n π hπ).ne')
  · intro π hπ
    exact kingmanDiversityLengthPotential_coalesced hn π hπ
  · intro π hπ
    have hk : 2 ≤ π.parts.card := by
      have := mt mem_coalescedPartitions.mpr hπ
      omega
    obtain ⟨m, hm⟩ : ∃ m, π.parts.card = m + 2 := ⟨π.parts.card - 2, by omega⟩
    have e2 : m + 2 - 1 = m + 1 := rfl
    change ∑ σ, (partitionChain (Fin n)).Q π σ *
        (kingmanDiversityReward n σ * kingmanDiversityLengthWeight σ.parts.card) =
      -(kingmanDiversityReward n π *
        ((π.parts.card : ℝ) + kingmanLengthWeight π.parts.card))
    rw [generator_diversity_mul_card hn kingmanDiversityLengthWeight π, hm, e2,
      diversity_length_weight_step m]
    push_cast
    ring

private theorem jump_drift_of_eq_expectedCost (n : ℕ)
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

theorem kingmanLengthPotential_jump_drift (n : ℕ)
    (π : Finpartition (Finset.univ : Finset (Fin n))) :
    kingmanLengthPotential n π -
        (partitionChain (Fin n)).jumpChain.expect (kingmanLengthPotential n) π =
      kingmanJumpReward n (fun π => (π.parts.card : ℝ)) π :=
  jump_drift_of_eq_expectedCost n _ _ (kingmanLengthPotential_eq_expectedCost n) π

theorem kingmanDiversityReward_jumpReward_drift {n : ℕ} (hn : 0 < n)
    (π : Finpartition (Finset.univ : Finset (Fin n))) :
    kingmanDiversityReward n π -
        (partitionChain (Fin n)).jumpChain.expect (kingmanDiversityReward n) π =
      kingmanJumpReward n (kingmanDiversityReward n) π :=
  jump_drift_of_eq_expectedCost n _ _ (kingmanDiversityReward_eq_expectedCost hn) π

theorem kingmanDiversityLengthPotential_jump_drift {n : ℕ} (hn : 0 < n)
    (π : Finpartition (Finset.univ : Finset (Fin n))) :
    kingmanDiversityLengthPotential n π -
        (partitionChain (Fin n)).jumpChain.expect (kingmanDiversityLengthPotential n) π =
      kingmanJumpReward n (kingmanDiversityReward n) π * kingmanLengthPotential n π +
        kingmanJumpReward n (fun π => (π.parts.card : ℝ)) π * kingmanDiversityReward n π := by
  rw [jump_drift_of_eq_expectedCost n _ _ (kingmanDiversityLengthPotential_eq_expectedCost hn) π]
  unfold kingmanJumpReward kingmanDiversityLengthReward kingmanLengthPotential
  split_ifs <;> ring

theorem kingmanDiversityLengthPotential_bot {n : ℕ} (hn : 2 ≤ n) :
    kingmanDiversityLengthPotential n ⊥ =
      2 * (((n : ℝ) + 2) / n + 2 * (tajimaA1 n : ℝ)) := by
  have hc : (⊥ : Finpartition (Finset.univ : Finset (Fin n))).parts.card = n := by
    rw [Finpartition.parts_bot, Finset.card_map]
    simp
  unfold kingmanDiversityLengthPotential kingmanDiversityLengthWeight
  rw [hc, kingmanDiversityReward_bot hn]
  rfl

end Rhone.Statistics
