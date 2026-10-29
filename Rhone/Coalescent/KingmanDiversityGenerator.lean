/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.KingmanPartition
public import Rhone.Combinatorics.FinitePairSums

/-!
# Labelled Kingman generator rewards for pairwise diversity moments

Source: kingman1982, sec. 1, eq. (1.1)–(1.4), (1.7); tajima1989, p. 585, eq. (6)–(7). -/

@[expose] public section
namespace Rhone.Coalescent
open Finset Rhone.Combinatorics MarkovChain

noncomputable def kingmanBlockMassMoment (n k : ℕ)
    (π : Finpartition (Finset.univ : Finset (Fin n))) : ℝ :=
  ∑ B ∈ π.parts, ((B.card : ℝ) / n) ^ k

/-- Source: kingman1982, eq. (1.3)–(1.4). -/
theorem sum_partitionQ_reward {n : ℕ}
    (π : Finpartition (Finset.univ : Finset (Fin n)))
    (f : Finpartition (Finset.univ : Finset (Fin n)) → ℝ) :
    ∑ σ, (partitionChain (Fin n)).Q π σ * f σ =
      ∑ s ∈ π.parts.powersetCard 2, (f (mergeBlocks π s) - f π) := by
  classical
  have hinj : Set.InjOn (mergeBlocks π) (↑(π.parts.powersetCard 2) : Set _) := by
    intro s hs t ht he
    rw [Finset.mem_coe, Finset.mem_powersetCard] at hs ht
    rw [← parts_sdiff_parts_mergeBlocks hs.1 hs.2,
      ← parts_sdiff_parts_mergeBlocks ht.1 ht.2]
    exact congrArg (fun σ => π.parts \ σ.parts) he
  have hm : (∑ σ with σ ∈ merges π, f σ) =
      ∑ s ∈ π.parts.powersetCard 2, f (mergeBlocks π s) := by
    rw [show (Finset.univ.filter (fun σ => σ ∈ merges π)) = merges π by ext; simp]
    unfold merges
    exact Finset.sum_image hinj
  rw [partitionChain_Q]
  simp only [partitionQ, sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib]
  rw [← Finset.sum_filter, hm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Finset.sum_const, nsmul_eq_mul,
    Finset.card_powersetCard, coalRate_cast_eq_choose]

theorem kingmanBlockMassMoment_merge (n k : ℕ)
    (π : Finpartition (Finset.univ : Finset (Fin n)))
    (s : Finset (Finset (Fin n))) (hs : s ⊆ π.parts) (hcard : s.card = 2) :
    kingmanBlockMassMoment n k (mergeBlocks π s) = kingmanBlockMassMoment n k π +
      (∑ B ∈ s, (B.card : ℝ) / n) ^ k - ∑ B ∈ s, ((B.card : ℝ) / n) ^ k := by
  classical
  have hne : s.Nonempty := Finset.card_pos.mp (by omega)
  have hm : s.sup id ∉ π.parts \ s := fun h =>
    sup_notMem_parts hs hcard (Finset.mem_sdiff.mp h).1
  have hmass : ((s.sup id).card : ℝ) / n = ∑ B ∈ s, (B.card : ℝ) / n := by
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
    have ha : a ∈ π.parts := hs (by simp)
    have hb : b ∈ π.parts := hs (by simp)
    have hd : Disjoint a b := π.disjoint ha hb hab
    simp only [Finset.sup_insert, Finset.sup_singleton, id_eq]
    change ((a ∪ b).card : ℝ) / n = _
    rw [Finset.card_union_of_disjoint hd]
    simp [hab, Nat.cast_add, add_div]
  unfold kingmanBlockMassMoment
  rw [parts_mergeBlocks hs hne, Finset.sum_insert hm, hmass]
  have hsum := Finset.sum_sdiff hs (f := fun B => ((B.card : ℝ) / n) ^ k)
  linarith

theorem sum_kingmanBlockMass {n : ℕ} (hn : 0 < n)
    (π : Finpartition (Finset.univ : Finset (Fin n))) :
    ∑ B ∈ π.parts, (B.card : ℝ) / n = 1 := by
  rw [← Finset.sum_div]
  have hm : ∑ B ∈ π.parts, (B.card : ℝ) = n := by
    have h := π.sum_card_parts
    simp only [Finset.card_univ, Fintype.card_fin] at h
    exact_mod_cast h
  rw [hm]
  exact div_self (by positivity)

theorem kingman_generator_mass_two {n : ℕ} (hn : 0 < n)
    (π : Finpartition (Finset.univ : Finset (Fin n))) :
    ∑ σ, (partitionChain (Fin n)).Q π σ * kingmanBlockMassMoment n 2 σ =
      1 - kingmanBlockMassMoment n 2 π := by
  rw [sum_partitionQ_reward]
  have he (s : Finset (Finset (Fin n))) (hs : s ∈ π.parts.powersetCard 2) :
      kingmanBlockMassMoment n 2 (mergeBlocks π s) - kingmanBlockMassMoment n 2 π =
      (∑ B ∈ s, (B.card : ℝ) / n) * (∑ B ∈ s, (B.card : ℝ) / n) -
        ∑ B ∈ s, ((B.card : ℝ) / n) * ((B.card : ℝ) / n) := by
    have hp := Finset.mem_powersetCard.mp hs
    rw [kingmanBlockMassMoment_merge n 2 π s hp.1 hp.2]
    simp only [pow_two]
    ring
  rw [Finset.sum_congr rfl he, sum_powersetCard_two_cross_general,
    sum_kingmanBlockMass hn π]
  simp [kingmanBlockMassMoment, pow_two]

theorem kingman_generator_mass_three {n : ℕ} (hn : 0 < n)
    (π : Finpartition (Finset.univ : Finset (Fin n))) :
    ∑ σ, (partitionChain (Fin n)).Q π σ * kingmanBlockMassMoment n 3 σ =
      3 * (kingmanBlockMassMoment n 2 π - kingmanBlockMassMoment n 3 π) := by
  classical
  rw [sum_partitionQ_reward]
  have he (s : Finset (Finset (Fin n))) (hs : s ∈ π.parts.powersetCard 2) :
      kingmanBlockMassMoment n 3 (mergeBlocks π s) - kingmanBlockMassMoment n 3 π =
      3 * ((∑ B ∈ s, ((B.card : ℝ) / n) ^ 2) * (∑ B ∈ s, (B.card : ℝ) / n) -
        ∑ B ∈ s, ((B.card : ℝ) / n) ^ 2 * ((B.card : ℝ) / n)) := by
    have hp := Finset.mem_powersetCard.mp hs
    rw [kingmanBlockMassMoment_merge n 3 π s hp.1 hp.2]
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hp.2
    simp only [Finset.sum_pair hab]
    ring
  rw [Finset.sum_congr rfl he, ← Finset.mul_sum, sum_powersetCard_two_cross_general,
    sum_kingmanBlockMass hn π]
  simp only [mul_one]
  unfold kingmanBlockMassMoment
  simp_rw [← pow_succ]

theorem kingman_generator_mass_four {n : ℕ} (hn : 0 < n)
    (π : Finpartition (Finset.univ : Finset (Fin n))) :
    ∑ σ, (partitionChain (Fin n)).Q π σ * kingmanBlockMassMoment n 4 σ =
      4 * kingmanBlockMassMoment n 3 π +
        3 * kingmanBlockMassMoment n 2 π ^ 2 - 7 * kingmanBlockMassMoment n 4 π := by
  classical
  rw [sum_partitionQ_reward]
  have he (s : Finset (Finset (Fin n))) (hs : s ∈ π.parts.powersetCard 2) :
      kingmanBlockMassMoment n 4 (mergeBlocks π s) - kingmanBlockMassMoment n 4 π =
      4 * ((∑ B ∈ s, ((B.card : ℝ) / n) ^ 3) * (∑ B ∈ s, (B.card : ℝ) / n) -
        ∑ B ∈ s, ((B.card : ℝ) / n) ^ 3 * ((B.card : ℝ) / n)) +
      3 * ((∑ B ∈ s, ((B.card : ℝ) / n) ^ 2) *
        (∑ B ∈ s, ((B.card : ℝ) / n) ^ 2) -
        ∑ B ∈ s, ((B.card : ℝ) / n) ^ 2 * ((B.card : ℝ) / n) ^ 2) := by
    have hp := Finset.mem_powersetCard.mp hs
    rw [kingmanBlockMassMoment_merge n 4 π s hp.1 hp.2]
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hp.2
    simp only [Finset.sum_pair hab]
    ring
  rw [Finset.sum_congr rfl he, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, sum_powersetCard_two_cross_general,
    sum_powersetCard_two_cross_general, sum_kingmanBlockMass hn π]
  simp only [mul_one, ← pow_succ, ← pow_add]
  unfold kingmanBlockMassMoment
  ring

theorem kingman_generator_mass_two_sq {n : ℕ} (hn : 0 < n)
    (π : Finpartition (Finset.univ : Finset (Fin n))) :
    ∑ σ, (partitionChain (Fin n)).Q π σ * kingmanBlockMassMoment n 2 σ ^ 2 =
      2 * kingmanBlockMassMoment n 2 π - 2 * kingmanBlockMassMoment n 4 π := by
  classical
  rw [sum_partitionQ_reward]
  have he (s : Finset (Finset (Fin n))) (hs : s ∈ π.parts.powersetCard 2) :
      kingmanBlockMassMoment n 2 (mergeBlocks π s) ^ 2 -
        kingmanBlockMassMoment n 2 π ^ 2 =
      2 * kingmanBlockMassMoment n 2 π *
        ((∑ B ∈ s, (B.card : ℝ) / n) * (∑ B ∈ s, (B.card : ℝ) / n) -
          ∑ B ∈ s, ((B.card : ℝ) / n) * ((B.card : ℝ) / n)) +
      2 * ((∑ B ∈ s, ((B.card : ℝ) / n) ^ 2) *
        (∑ B ∈ s, ((B.card : ℝ) / n) ^ 2) -
        ∑ B ∈ s, ((B.card : ℝ) / n) ^ 2 * ((B.card : ℝ) / n) ^ 2) := by
    have hp := Finset.mem_powersetCard.mp hs
    rw [kingmanBlockMassMoment_merge n 2 π s hp.1 hp.2]
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hp.2
    simp only [Finset.sum_pair hab]
    ring
  rw [Finset.sum_congr rfl he, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, sum_powersetCard_two_cross_general,
    sum_powersetCard_two_cross_general, sum_kingmanBlockMass hn π]
  have h2 : (∑ B ∈ π.parts, ((B.card : ℝ) / n) * ((B.card : ℝ) / n)) =
      kingmanBlockMassMoment n 2 π := by
    unfold kingmanBlockMassMoment
    apply Finset.sum_congr rfl
    intro B _
    ring
  have h4 : (∑ B ∈ π.parts, ((B.card : ℝ) / n) ^ 2 * ((B.card : ℝ) / n) ^ 2) =
      kingmanBlockMassMoment n 4 π := by
    unfold kingmanBlockMassMoment
    apply Finset.sum_congr rfl
    intro B _
    ring
  rw [h2, h4]
  change 2 * kingmanBlockMassMoment n 2 π * (1 * 1 - kingmanBlockMassMoment n 2 π) +
    2 * (kingmanBlockMassMoment n 2 π * kingmanBlockMassMoment n 2 π -
      kingmanBlockMassMoment n 4 π) = _
  ring

end Rhone.Coalescent
