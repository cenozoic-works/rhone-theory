/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Statistics.SfsCovariance
public import Rhone.Statistics.SegregatingMoments

/-!
# The segregating-site count as the sum of the site frequency spectrum

Source: fu1995, eq. 22. -/

@[expose] public section
namespace Rhone.Statistics
open MeasureTheory ProbabilityTheory Finset Coalescent Rhone.Combinatorics MarkovChain Probability
open Filter
open scoped NNReal

private theorem kingmanBranchMutationRate_eq_zero_of_card (n : ℕ) (θ : ℝ≥0)
    (h : KingmanMutationHistory n) (b : KingmanMutationBranch n)
    (hb : b.2.card = 0 ∨ b.2.card = n) : kingmanBranchMutationRate n θ h b = 0 := by
  have hc : ¬ (b.2 ∈ (h.1 b.1.val).parts ∧ 1 < (h.1 b.1.val).parts.card) := by
    rintro ⟨hmem, hcard⟩
    rcases hb with h0 | hn
    · rw [Finset.card_eq_zero] at h0
      rw [h0] at hmem
      exact Finpartition.empty_notMem_parts _ hmem
    · obtain ⟨B, hB, hne⟩ := Finset.exists_mem_ne hcard b.2
      have hsum := (h.1 b.1.val).sum_card_parts
      have hsub : ({b.2, B} : Finset (Finset (Fin n))) ⊆ (h.1 b.1.val).parts := by
        intro C hC
        rcases Finset.mem_insert.mp hC with rfl | hC'
        · exact hmem
        · rw [Finset.mem_singleton.mp hC']
          exact hB
      have hle := Finset.sum_le_sum_of_subset (f := fun C : Finset (Fin n) => C.card) hsub
      rw [Finset.sum_pair (Ne.symm hne)] at hle
      have hpos : 0 < B.card := Finset.card_pos.mpr ((h.1 b.1.val).nonempty_of_mem_parts hB)
      simp only [Finset.card_univ, Fintype.card_fin] at hsum
      omega
  unfold kingmanBranchMutationRate
  apply Subtype.ext
  change (if _ then _ else _ : ℝ) = 0
  rw [ite_eq_right hc]

private theorem integral_kingmanBranchMutationKernel_sfs_edge (n i : ℕ) (θ : ℝ≥0)
    (hi : i = 0 ∨ i = n) (h : KingmanMutationHistory n) :
    ∫ x, markedKingmanSfs n i (h, x) ∂kingmanBranchMutationKernel n θ h = 0 := by
  simp_rw [markedKingmanSfs_eq_weighted]
  change (∫ x : KingmanMutationBranch n → ℕ, ∑ b : KingmanMutationBranch n,
    (if b.2.card = i then (1 : ℝ) else 0) * (x b : ℝ)
    ∂Measure.pi (fun b => poissonMeasure (kingmanBranchMutationRate n θ h b))) = 0
  rw [pi_poisson_integral_weighted_count]
  apply Finset.sum_eq_zero
  intro b _
  by_cases hc : b.2.card = i
  · rw [kingmanBranchMutationRate_eq_zero_of_card n θ h b
      (by rcases hi with rfl | rfl <;> simp_all)]
    simp
  · simp [hc]

private theorem markedKingmanSfs_ae_zero_of_edge (n i : ℕ) (θ : ℝ≥0) (hi : i = 0 ∨ i = n) :
    ∀ᵐ x ∂markedKingmanLaw n θ, markedKingmanSfs n i x = 0 := by
  have hint : ∫ x, markedKingmanSfs n i x ∂markedKingmanLaw n θ = 0 := by
    rw [show markedKingmanLaw n θ =
      ((partitionChain (Fin n)).jumpHoldLaw ⊥).compProd
        (kingmanBranchMutationKernel n θ) from rfl,
      Measure.integral_compProd (integrable_markedKingmanSfs n i θ)]
    simp_rw [integral_kingmanBranchMutationKernel_sfs_edge n i θ hi]
    simp
  have h := (integral_eq_zero_iff_of_nonneg (fun x => markedKingmanSfs_nonneg n i x)
    (integrable_markedKingmanSfs n i θ)).1 hint
  filter_upwards [h] with x hx using hx

theorem markedKingmanSfs_zero_ae (n : ℕ) (θ : ℝ≥0) :
    ∀ᵐ x ∂markedKingmanLaw n θ, markedKingmanSfs n 0 x = 0 :=
  markedKingmanSfs_ae_zero_of_edge n 0 θ (Or.inl rfl)

theorem markedKingmanSfs_top_ae (n : ℕ) (θ : ℝ≥0) :
    ∀ᵐ x ∂markedKingmanLaw n θ, markedKingmanSfs n n x = 0 :=
  markedKingmanSfs_ae_zero_of_edge n n θ (Or.inr rfl)

/-- Source: fu1995, eq. 22. -/
theorem markedKingmanSegregating_ae_eq_sum_sfs (n : ℕ) (θ : ℝ≥0) :
    markedKingmanSegregating n =ᵐ[markedKingmanLaw n θ]
      fun x => ∑ i ∈ Icc 1 (n - 1), markedKingmanSfs n i x := by
  have hall : ∀ᵐ x ∂markedKingmanLaw n θ, ∀ i ∈ range (n + 1), (i = 0 ∨ i = n) →
      markedKingmanSfs n i x = 0 := by
    rw [Filter.eventually_all_finset]
    intro i _
    by_cases hi : i = 0 ∨ i = n
    · filter_upwards [markedKingmanSfs_ae_zero_of_edge n i θ hi] with x hx _ using hx
    · exact Eventually.of_forall fun x h => absurd h hi
  filter_upwards [hall] with x hx
  rw [markedKingmanSegregating_eq_sum_sfs]
  symm
  apply Finset.sum_subset
  · intro i hi
    rw [Finset.mem_Icc] at hi
    rw [Finset.mem_range]
    omega
  · intro i hi hni
    apply hx i hi
    rw [Finset.mem_range] at hi
    rw [Finset.mem_Icc] at hni
    omega

theorem sum_sum_fuSigma {n : ℕ} (hn : 2 ≤ n) :
    ∑ i ∈ Icc 1 (n - 1), ∑ j ∈ Icc 1 (n - 1), fuSigma n i j = (tajimaA2 n : ℝ) := by
  have h1 := markedKingman_linear_sfs_variance n (fun _ => (1 : ℝ)) 1
  have h2 := markedKingmanSegregating_variance hn 1
  rw [variance_congr (markedKingmanSegregating_ae_eq_sum_sfs n 1)] at h2
  simp only [one_mul, one_pow, mul_one] at h1
  have hA : (tajimaA1 n : ℝ) = ∑ i ∈ Icc 1 (n - 1), 1 / (i : ℝ) := by
    unfold tajimaA1
    rw [harmonic_eq_sum_Icc_inv]
    push_cast
    simp
  simp only [NNReal.coe_one, one_mul, one_pow] at h1 h2
  rw [h1, hA] at h2
  linarith

end Rhone.Statistics
