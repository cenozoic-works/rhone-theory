/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.EqualRatesMutationSemigroup
public import Rhone.Statistics.Identifiability.FourEpochPanLaplaceExactness

/-! # Exact finite-site observation matching at fixed recombination -/

@[expose] public section

open Set MeasureTheory
namespace Rhone.Statistics.Identifiability.FiniteSiteObservation

theorem limit_pos {K : ℕ} (hK : 2 ≤ K) : 0 < limit K := by
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK
  exact div_pos (by linarith) (by linarith)

theorem exists_fourEpoch_observation_match {K : ℕ} {k r : ℝ}
    {μ : Measure (ℝ × ℝ)} [IsProbabilityMeasure μ]
    (hK : 2 ≤ K) (hk : 0 < k) (hr : 0 ≤ r)
    (hμ : NonnegativeTimes μ) (hsym : μ.map Prod.fst = μ.map Prod.snd)
    (hmom : momentPair K k μ ∈ MutationMomentSurjectivity.momentDomain (limit K)) :
    ∃ (ε δ M A τ : ℝ) (P : ProperIntegrablePanModel),
      0 < ε ∧ 0 < δ ∧ 0 < M ∧ 0 < A ∧ ε < τ ∧
      P.rate = MutationPulseKernel.fourEpochRate ε δ M A τ ∧
      P.pre.recomb = (fun _ => r) ∧
      (∀ t : ℝ, δ ≤ P.rate t ∧ P.rate t ≤ δ + (A + M) / ε) ∧
      law K k μ = law K k P.pre.jointLaw := by
  obtain ⟨ε, δ, M, A, τ, P, hε, hδ, hM, hA, hτ, hrate, hrecomb,
    _hprob, _hi1, _hi2, heq, hbound⟩ :=
    FourEpochBackward.exists_fourEpoch_jointLaw_exact (limit_pos hK) hr hk hmom
  exact ⟨ε, δ, M, A, τ, P, hε, hδ, hM, hA, hτ, hrate, hrecomb, hbound,
    law_eq_pan_of_momentPair_eq P hK hk.le hμ hsym heq.symm⟩

theorem exists_fourEpoch_equalRatesMutation_match {K : ℕ} {k r : ℝ}
    {μ : Measure (ℝ × ℝ)} [IsProbabilityMeasure μ]
    (hK : 2 ≤ K) (hk : 0 < k) (hr : 0 ≤ r)
    (hμ : NonnegativeTimes μ) (hsym : μ.map Prod.fst = μ.map Prod.snd)
    (hmom : momentPair K k μ ∈ MutationMomentSurjectivity.momentDomain (limit K)) :
    ∃ (ε δ M A τ : ℝ) (P : ProperIntegrablePanModel),
      0 < ε ∧ 0 < δ ∧ 0 < M ∧ 0 < A ∧ ε < τ ∧
      P.rate = MutationPulseKernel.fourEpochRate ε δ M A τ ∧
      P.pre.recomb = (fun _ => r) ∧
      (∀ t : ℝ, δ ≤ P.rate t ∧ P.rate t ≤ δ + (A + M) / ε) ∧
      EqualRatesMutation.observationLaw K k μ =
        EqualRatesMutation.observationLaw K k P.pre.jointLaw := by
  simp_rw [EqualRatesMutation.observationLaw_eq hK]
  exact exists_fourEpoch_observation_match hK hk hr hμ hsym hmom

end Rhone.Statistics.Identifiability.FiniteSiteObservation
