/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Statistics.AllelicPartition
public import Rhone.Statistics.SegregatingGeneratingFunction

/-!
# With no mutation marks the allelic partition of a marked Kingman sample is one class

Source: watterson1975, sec. 1.4, p. 262. -/

@[expose] public section
namespace Rhone.Statistics
open MeasureTheory ProbabilityTheory Finset Rhone.Combinatorics MarkovChain Probability
open scoped NNReal

theorem kingmanBranchMutationRate_eq_zero_of_not_separating {n : ℕ} (θ : ℝ≥0)
    (h : Coalescent.KingmanMutationHistory n) {br : Coalescent.KingmanMutationBranch n}
    (hB : ∀ a b : Fin n, a ∈ br.2 → b ∈ br.2) :
    Coalescent.kingmanBranchMutationRate n θ h br = 0 := by
  have hcond : ¬ (br.2 ∈ (h.1 br.1.val).parts ∧ 1 < (h.1 br.1.val).parts.card) := by
    rintro ⟨hmem, hcard⟩
    obtain ⟨a, ha⟩ := (h.1 br.1.val).nonempty_of_mem_parts hmem
    have huniv : br.2 = univ := Finset.eq_univ_of_forall fun b => hB a b ha
    have hall : ∀ C ∈ (h.1 br.1.val).parts, C = br.2 := by
      intro C hC
      by_contra hne
      have hd := (h.1 br.1.val).disjoint hC hmem hne
      rw [huniv] at hd
      exact (h.1 br.1.val).ne_bot hC (hd.eq_bot_of_le (Finset.subset_univ C))
    have hle : (h.1 br.1.val).parts.card ≤ 1 :=
      Finset.card_le_one.2 fun C hC D hD => (hall C hC).trans (hall D hD).symm
    omega
  apply NNReal.eq
  change (if br.2 ∈ (h.1 br.1.val).parts ∧ 1 < (h.1 br.1.val).parts.card then
    max 0 ((θ : ℝ) / 2 * (Rhone.Coalescent.partitionChain (Fin n)).holdTime h br.1.val)
    else 0) = 0
  exact ite_eq_right hcond

theorem markedKingmanLaw_ae_mark_eq_zero (n : ℕ) (θ : ℝ≥0) :
    ∀ᵐ x ∂Coalescent.markedKingmanLaw n θ, ∀ br : Coalescent.KingmanMutationBranch n,
      Coalescent.kingmanBranchMutationRate n θ x.1 br = 0 → x.2 br = 0 := by
  rw [ae_all_iff]
  intro br
  have hrate := Coalescent.measurable_kingmanBranchMutationRate n θ br
  have hmeas : MeasurableSet
      {x : Coalescent.KingmanMutationHistory n × (Coalescent.KingmanMutationBranch n → ℕ) |
      Coalescent.kingmanBranchMutationRate n θ x.1 br = 0 → x.2 br = 0} := by
    have h1 : MeasurableSet
        {x : Coalescent.KingmanMutationHistory n × (Coalescent.KingmanMutationBranch n → ℕ) |
        Coalescent.kingmanBranchMutationRate n θ x.1 br = 0} :=
      (hrate.comp measurable_fst) (measurableSet_singleton 0)
    have h2 : MeasurableSet
        {x : Coalescent.KingmanMutationHistory n × (Coalescent.KingmanMutationBranch n → ℕ) |
        x.2 br = 0} :=
      ((measurable_pi_apply br).comp measurable_snd) (measurableSet_singleton 0)
    have he : {x : Coalescent.KingmanMutationHistory n × (Coalescent.KingmanMutationBranch n → ℕ) |
        Coalescent.kingmanBranchMutationRate n θ x.1 br = 0 → x.2 br = 0} =
        {x | Coalescent.kingmanBranchMutationRate n θ x.1 br = 0}ᶜ ∪ {x | x.2 br = 0} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff]
      tauto
    rw [he]
    exact h1.compl.union h2
  rw [show Coalescent.markedKingmanLaw n θ =
      ((Rhone.Coalescent.partitionChain (Fin n)).jumpHoldLaw ⊥).compProd
        (Coalescent.kingmanBranchMutationKernel n θ) from rfl, Measure.ae_compProd_iff hmeas]
  refine ae_of_all _ fun h => ?_
  change ∀ᵐ m ∂Measure.pi (fun b : Coalescent.KingmanMutationBranch n =>
    poissonMeasure (Coalescent.kingmanBranchMutationRate n θ h b)),
    Coalescent.kingmanBranchMutationRate n θ h br = 0 → m br = 0
  by_cases hr : Coalescent.kingmanBranchMutationRate n θ h br = 0
  · have hpre := (measurePreserving_eval (fun b : Coalescent.KingmanMutationBranch n =>
      poissonMeasure (Coalescent.kingmanBranchMutationRate n θ h b)) br).quasiMeasurePreserving
    have hd : ∀ᵐ k ∂poissonMeasure (Coalescent.kingmanBranchMutationRate n θ h br), k = 0 := by
      rw [hr, poissonMeasure_zero_eq_dirac]
      exact ae_dirac_iff (measurableSet_singleton 0) |>.2 rfl
    filter_upwards [hpre.ae hd] with m hm _
    exact hm
  · exact ae_of_all _ fun m hm => absurd hm hr

theorem allelicPartition_eq_indiscrete_of_marks_eq_zero {n : ℕ}
    {x : Coalescent.KingmanMutationHistory n × (Coalescent.KingmanMutationBranch n → ℕ)}
    (hx : ∀ br, x.2 br = 0) : allelicPartition n x = Nat.Partition.indiscrete n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Subsingleton.elim _ _
  have hpart : ∀ a : Fin n, (allelicFinpartition n x).part a = univ := fun a =>
    Finset.eq_univ_of_forall fun b => mem_part_allelicFinpartition.2 fun br _ => hx br
  have hparts : (allelicFinpartition n x).parts = {univ} := by
    refine Finset.eq_singleton_iff_unique_mem.2 ⟨?_, ?_⟩
    · have h0 := (allelicFinpartition n x).part_mem.2 (mem_univ (⟨0, hn⟩ : Fin n))
      rwa [hpart ⟨0, hn⟩] at h0
    · intro B hB
      obtain ⟨a, ha⟩ := (allelicFinpartition n x).nonempty_of_mem_parts hB
      rw [← (allelicFinpartition n x).part_eq_of_mem hB ha, hpart a]
  apply Nat.Partition.ext
  rw [allelicPartition_parts, hparts, Nat.Partition.indiscrete_parts hn.ne']
  simp

theorem sameAllele_of_allelicPartition_eq_indiscrete {n : ℕ}
    {x : Coalescent.KingmanMutationHistory n × (Coalescent.KingmanMutationBranch n → ℕ)}
    (hx : allelicPartition n x = Nat.Partition.indiscrete n) (a b : Fin n) :
    sameAllele n x a b := by
  have hn : n ≠ 0 := fun h => by
    subst h
    exact a.elim0
  have hparts := congrArg Nat.Partition.parts hx
  rw [allelicPartition_parts, Nat.Partition.indiscrete_parts hn] at hparts
  have hmem : ((allelicFinpartition n x).part a).card ∈
      (allelicFinpartition n x).parts.val.map Finset.card :=
    Multiset.mem_map_of_mem _ ((allelicFinpartition n x).part_mem.2 (mem_univ a))
  rw [hparts, Multiset.mem_singleton] at hmem
  have huniv : (allelicFinpartition n x).part a = univ := by
    apply Finset.eq_univ_of_card
    rw [hmem, Fintype.card_fin]
  have hb : b ∈ (allelicFinpartition n x).part a := by
    rw [huniv]
    exact mem_univ b
  exact mem_part_allelicFinpartition.1 hb

theorem markedKingman_allelicPartition_indiscrete (n : ℕ) (θ : ℝ≥0) :
    (Coalescent.markedKingmanLaw n θ).real {x | allelicPartition n x = Nat.Partition.indiscrete n} =
      ∏ j ∈ Icc 1 (n - 1), (j : ℝ) / ((j : ℝ) + (θ : ℝ)) := by
  rw [← markedKingman_no_segregating n θ]
  apply measureReal_congr
  filter_upwards [markedKingmanLaw_ae_mark_eq_zero n θ] with x hx
  apply propext
  constructor
  · intro h br
    by_cases hsep : ∀ a b : Fin n, a ∈ br.2 → b ∈ br.2
    · exact hx br (kingmanBranchMutationRate_eq_zero_of_not_separating θ x.1 hsep)
    · push Not at hsep
      obtain ⟨a, b, ha, hb⟩ := hsep
      exact sameAllele_of_allelicPartition_eq_indiscrete h a b br (by tauto)
  · exact allelicPartition_eq_indiscrete_of_marks_eq_zero

end Rhone.Statistics
