/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.SfsMarkedSpectrumPotential
public import Rhone.Statistics.SegregatingMoments

/-!
# Expected site frequency spectrum under the marked Kingman law

Source: fu1995, eq. 22. -/

@[expose] public section
namespace Rhone.Statistics
open MeasureTheory ProbabilityTheory Finset Coalescent Rhone.Combinatorics MarkovChain Probability
open Filter
open scoped NNReal

/-- Source: fu1995, eq. 22. -/
noncomputable def markedKingmanSfs (n i : ℕ)
    (x : KingmanMutationHistory n × (KingmanMutationBranch n → ℕ)) : ℝ :=
  ∑ b : KingmanMutationBranch n, if b.2.card = i then (x.2 b : ℝ) else 0

/-- Source: fu1995, eq. 22. -/
noncomputable def sfsBlockCount (n i : ℕ)
    (π : Finpartition (Finset.univ : Finset (Fin n))) : ℝ :=
  ∑ B ∈ π.parts, if B.card = i then (1 : ℝ) else 0

/-- Source: fu1995, eq. 22. -/
theorem sfsBlockCount_eq_blockWeightReward (n i : ℕ) :
    sfsBlockCount n i =
      blockWeightReward (fun B : Finset (Fin n) => if B.card = i then (1 : ℝ) else 0) := rfl

/-- Source: fu1995, eq. 22. -/
theorem markedKingmanSfs_eq_weighted (n i : ℕ)
    (x : KingmanMutationHistory n × (KingmanMutationBranch n → ℕ)) :
    markedKingmanSfs n i x = ∑ b : KingmanMutationBranch n,
      (if b.2.card = i then (1 : ℝ) else 0) * (x.2 b : ℝ) := by
  unfold markedKingmanSfs
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> simp

/-- Source: fu1995, eq. 22. -/
theorem measurable_markedKingmanSfs (n i : ℕ) : Measurable (markedKingmanSfs n i) := by
  unfold markedKingmanSfs
  apply Finset.measurable_sum
  intro b _
  split_ifs
  · fun_prop
  · exact measurable_const

/-- Source: fu1995, eq. 22. -/
theorem markedKingmanSfs_nonneg (n i : ℕ)
    (x : KingmanMutationHistory n × (KingmanMutationBranch n → ℕ)) :
    0 ≤ markedKingmanSfs n i x := by
  apply Finset.sum_nonneg
  intro b _
  split_ifs
  · exact Nat.cast_nonneg _
  · exact le_rfl

/-- Source: fu1995, eq. 22. -/
theorem sum_kingmanBranchMutationRate_blockWeight (n : ℕ) (θ : ℝ≥0)
    (h : KingmanMutationHistory n) (w : Finset (Fin n) → ℝ) :
    ∑ b : KingmanMutationBranch n, w b.2 * kingmanBranchMutationRate n θ h b =
      (θ : ℝ) / 2 * kingmanFiniteReward n (blockWeightReward w) h := by
  classical
  rw [Fintype.sum_prod_type]
  unfold kingmanFiniteReward blockWeightReward
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  change (∑ B, w B * (if B ∈ (h.1 k.val).parts ∧ 1 < (h.1 k.val).parts.card then
    max 0 ((θ : ℝ) / 2 * (partitionChain (Fin n)).holdTime h k.val) else 0)) = _
  by_cases hk : h.1 k.val ∈ coalescedPartitions (Fin n)
  · have ht : ¬ 1 < (h.1 k.val).parts.card := by
      have := mem_coalescedPartitions.mp hk
      omega
    simp [ht, hk]
  · have ht : 1 < (h.1 k.val).parts.card := by
      have := mt mem_coalescedPartitions.mpr hk
      omega
    simp only [ht, and_true, hk, ↓reduceIte]
    have he (B : Finset (Fin n)) :
        w B * (if B ∈ (h.1 k.val).parts then
          max 0 ((θ : ℝ) / 2 * (partitionChain (Fin n)).holdTime h k.val) else 0) =
        if B ∈ (h.1 k.val).parts then
          ((θ : ℝ) / 2 * max 0 ((partitionChain (Fin n)).holdTime h k.val)) * w B else 0 := by
      split_ifs
      · rw [mul_max_of_nonneg 0 ((partitionChain (Fin n)).holdTime h k.val)
          (by positivity), mul_zero]
        ring
      · ring
    simp_rw [he]
    rw [Finset.sum_ite_mem_eq, ← Finset.mul_sum]
    ring

/-- Source: fu1995, eq. 22. -/
theorem integral_kingmanBranchMutationKernel_sfs (n i : ℕ) (θ : ℝ≥0)
    (h : KingmanMutationHistory n) :
    ∫ x, markedKingmanSfs n i (h, x) ∂kingmanBranchMutationKernel n θ h =
      (θ : ℝ) / 2 * kingmanFiniteReward n (sfsBlockCount n i) h := by
  simp_rw [markedKingmanSfs_eq_weighted]
  change (∫ x : KingmanMutationBranch n → ℕ, ∑ b : KingmanMutationBranch n,
    (if b.2.card = i then (1 : ℝ) else 0) * (x b : ℝ)
    ∂Measure.pi (fun b => poissonMeasure (kingmanBranchMutationRate n θ h b))) = _
  rw [pi_poisson_integral_weighted_count,
    sum_kingmanBranchMutationRate_blockWeight n θ h
      (fun B => if B.card = i then (1 : ℝ) else 0), sfsBlockCount_eq_blockWeightReward]

private theorem indicator_weight_nonneg (n i : ℕ) (B : Finset (Fin n)) :
    0 ≤ (if B.card = i then (1 : ℝ) else 0) := by
  split_ifs <;> norm_num

theorem integrable_kingmanFiniteReward_sfsBlockCount (n i : ℕ) :
    Integrable (kingmanFiniteReward n (sfsBlockCount n i))
      ((partitionChain (Fin n)).jumpHoldLaw ⊥) := by
  rw [sfsBlockCount_eq_blockWeightReward]
  exact integrable_kingmanFiniteReward_blockWeight (indicator_weight_nonneg n i)

/-- Source: fu1995, eq. 22. -/
theorem integral_kingmanFiniteReward_sfsBlockCount {n i : ℕ} (hi : 1 ≤ i) (hin : i < n) :
    ∫ h, kingmanFiniteReward n (sfsBlockCount n i) h
      ∂(partitionChain (Fin n)).jumpHoldLaw ⊥ = 2 / (i : ℝ) := by
  rw [sfsBlockCount_eq_blockWeightReward,
    integral_kingmanFiniteReward_blockWeight (indicator_weight_nonneg n i)]
  have hterm : ∀ A : Finset (Fin n),
      (if A.card = i then (1 : ℝ) else 0) * sfsCladeCoeff n A.card =
        if A.card = i then sfsCladeCoeff n i else 0 := by
    intro A
    split_ifs with hA
    · rw [hA, one_mul]
    · rw [zero_mul]
  simp_rw [hterm]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, Finset.univ_filter_card_eq,
    Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
    choose_mul_sfsCladeCoeff hi hin]

/-- Source: fu1995, eq. 22. -/
theorem integrable_markedKingmanSfs (n i : ℕ) (θ : ℝ≥0) :
    Integrable (markedKingmanSfs n i) (markedKingmanLaw n θ) := by
  unfold markedKingmanLaw
  apply (Measure.integrable_compProd_iff
    (measurable_markedKingmanSfs n i).aestronglyMeasurable).mpr
  constructor
  · exact Eventually.of_forall fun h => by
      simp_rw [markedKingmanSfs_eq_weighted]
      exact pi_poisson_integrable_weighted_count (kingmanBranchMutationRate n θ h)
        (fun b => if b.2.card = i then (1 : ℝ) else 0)
  · simp_rw [Real.norm_eq_abs, abs_of_nonneg (markedKingmanSfs_nonneg n i _),
      integral_kingmanBranchMutationKernel_sfs]
    exact (integrable_kingmanFiniteReward_sfsBlockCount n i).const_mul _

/-- Source: fu1995, eq. 22. -/
theorem markedKingmanSfs_mean {n i : ℕ} (hi : 1 ≤ i) (hin : i < n) (θ : ℝ≥0) :
    ∫ x, markedKingmanSfs n i x ∂markedKingmanLaw n θ = (θ : ℝ) / i := by
  rw [show markedKingmanLaw n θ =
    ((partitionChain (Fin n)).jumpHoldLaw ⊥).compProd
      (kingmanBranchMutationKernel n θ) from rfl,
    Measure.integral_compProd (integrable_markedKingmanSfs n i θ)]
  simp_rw [integral_kingmanBranchMutationKernel_sfs]
  rw [integral_const_mul, integral_kingmanFiniteReward_sfsBlockCount hi hin]
  ring

/-- Source: fu1995, eq. 22; watterson1975, p. 258, eq. (1.4a); durrett2008, Thm 1.20. -/
theorem sum_markedKingmanSfs_mean {n : ℕ} (hn : 2 ≤ n) (θ : ℝ≥0) :
    ∑ i ∈ Finset.Icc 1 (n - 1), ∫ x, markedKingmanSfs n i x ∂markedKingmanLaw n θ =
      ∫ x, markedKingmanSegregating n x ∂markedKingmanLaw n θ := by
  have hq : ∑ i ∈ Finset.Icc 1 (n - 1), (1 : ℚ) / (i : ℚ) = tajimaA1 n := by
    have h := sum_expSfs 1 n
    rw [expSegSites_eq, one_mul] at h
    rw [tajimaA1, ← h]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_Icc] at hi
    rw [expSfs_eq 1 hi.1 (by omega)]
  have hr : (tajimaA1 n : ℝ) = ∑ i ∈ Finset.Icc 1 (n - 1), (1 : ℝ) / (i : ℝ) := by
    rw [← hq]
    push_cast
    rfl
  rw [markedKingmanSegregating_mean hn, hr, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_Icc] at hi
  rw [markedKingmanSfs_mean hi.1 (by omega)]
  ring

/-- Source: fu1995, eq. 22. -/
theorem expSfs_eq_integral_markedKingmanSfs (θ : ℚ) (hθ : 0 ≤ θ) {n i : ℕ}
    (hi : 1 ≤ i) (hin : i < n) :
    ((expSfs θ n i : ℚ) : ℝ) =
      ∫ x, markedKingmanSfs n i x
        ∂markedKingmanLaw n (NNReal.mk (θ : ℝ) (by exact_mod_cast hθ)) := by
  rw [expSfs_eq θ hi hin, markedKingmanSfs_mean hi hin, NNReal.coe_mk]
  push_cast
  rfl

end Rhone.Statistics
