/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.KingmanPartition
public import Rhone.Probability.PoissonMoments
public import Mathlib.Probability.Kernel.Composition.CompProd

/-!
# The Kingman partition genealogy with independent branch mutation marks

Source: tajima1989, pp. 588–589, eq. (39)–(42); kingman1982, sec. 1, eq. (1.1)–(1.4), (1.7). -/

@[expose] public section
namespace Rhone.Coalescent
open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

abbrev KingmanMutationHistory (n : ℕ) :=
  (ℕ → Finpartition (Finset.univ : Finset (Fin n))) × (ℕ → ℝ)

abbrev KingmanMutationBranch (n : ℕ) := Fin (n - 1) × Finset (Fin n)

/-- Source: tajima1989, p. 586, eq. (12). -/
noncomputable def kingmanBranchPairWeight (n : ℕ) (B : Finset (Fin n)) : ℝ :=
  2 * (B.card : ℝ) * (n - B.card) / ((n : ℝ) * (n - 1))

/-- Source: tajima1989, pp. 588–589, eq. (39)–(42). -/
noncomputable def kingmanBranchMutationRate (n : ℕ) (θ : ℝ≥0)
    (h : KingmanMutationHistory n) (b : KingmanMutationBranch n) : ℝ≥0 :=
  ⟨if b.2 ∈ (h.1 b.1.val).parts ∧ 1 < (h.1 b.1.val).parts.card then
      max 0 ((θ : ℝ) / 2 *
        (Rhone.Coalescent.partitionChain (Fin n)).holdTime h b.1.val)
    else 0, by split_ifs <;> positivity⟩

theorem measurable_kingmanBranchMutationRate (n : ℕ) (θ : ℝ≥0)
    (b : KingmanMutationBranch n) :
    Measurable (fun h : KingmanMutationHistory n => kingmanBranchMutationRate n θ h b) := by
  apply Measurable.subtype_mk
  unfold Rhone.MarkovChain.RateChain.holdTime
  apply Measurable.ite
  · have hm : Measurable (fun h : KingmanMutationHistory n => h.1 b.1.val) :=
      (measurable_pi_apply b.1.val).comp measurable_fst
    exact hm (MeasurableSet.of_discrete (s :=
      {π : Finpartition (Finset.univ : Finset (Fin n)) |
        b.2 ∈ π.parts ∧ 1 < π.parts.card}))
  · have hr : Measurable (Rhone.Coalescent.partitionChain (Fin n)).rate :=
      Measurable.of_discrete
    fun_prop
  · fun_prop

/-- Source: tajima1989, pp. 588–589, eq. (39)–(42). -/
noncomputable def kingmanBranchMutationKernel (n : ℕ) (θ : ℝ≥0) :
    Kernel (KingmanMutationHistory n) (KingmanMutationBranch n → ℕ) where
  toFun h := Measure.pi (fun b : KingmanMutationBranch n =>
    poissonMeasure (kingmanBranchMutationRate n θ h b))
  measurable' := by
    classical
    apply Measure.measurable_of_measurable_coe
    intro s hs
    have he : (fun h : KingmanMutationHistory n =>
        Measure.pi (fun b : KingmanMutationBranch n =>
          poissonMeasure (kingmanBranchMutationRate n θ h b)) s) =
        fun h => ∑' x : KingmanMutationBranch n → ℕ,
          s.indicator (fun x =>
            Measure.pi (fun b : KingmanMutationBranch n =>
              poissonMeasure (kingmanBranchMutationRate n θ h b)) {x}) x := by
      funext h
      exact (Measure.tsum_indicator_apply_singleton _ s hs).symm
    rw [he]
    apply Measurable.tsum
    intro x
    by_cases hx : x ∈ s
    · simp only [Set.indicator_of_mem hx, Measure.pi_singleton, poissonMeasure_singleton]
      apply Finset.measurable_prod
      intro b _
      have hb := measurable_kingmanBranchMutationRate n θ b
      fun_prop
    · simp only [Set.indicator_of_notMem hx]
      exact measurable_const

instance kingmanBranchMutationKernel_markov (n : ℕ) (θ : ℝ≥0) :
    IsMarkovKernel (kingmanBranchMutationKernel n θ) where
  isProbabilityMeasure h := by
    change IsProbabilityMeasure (Measure.pi (fun b : KingmanMutationBranch n =>
      poissonMeasure (kingmanBranchMutationRate n θ h b)))
    infer_instance

/-- Source: tajima1989, pp. 588–589, eq. (39)–(42). -/
noncomputable def markedKingmanLaw (n : ℕ) (θ : ℝ≥0) :
    Measure (KingmanMutationHistory n × (KingmanMutationBranch n → ℕ)) :=
  ((Rhone.Coalescent.partitionChain (Fin n)).jumpHoldLaw ⊥).compProd
    (kingmanBranchMutationKernel n θ)

/-- Source: tajima1989, p. 586, eq. (11)–(12). -/
noncomputable def markedKingmanPi (n : ℕ)
    (x : KingmanMutationHistory n × (KingmanMutationBranch n → ℕ)) : ℝ :=
  ∑ b : KingmanMutationBranch n, kingmanBranchPairWeight n b.2 * (x.2 b : ℝ)

instance markedKingmanLaw_probability (n : ℕ) (θ : ℝ≥0) :
    IsProbabilityMeasure (markedKingmanLaw n θ) := by
  unfold markedKingmanLaw
  infer_instance

theorem measurable_markedKingmanPi (n : ℕ) : Measurable (markedKingmanPi n) := by
  unfold markedKingmanPi
  apply Finset.measurable_sum
  intro b _
  fun_prop

end Rhone.Coalescent
