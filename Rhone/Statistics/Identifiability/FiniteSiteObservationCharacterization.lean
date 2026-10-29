/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.FiniteSiteExactMatch
public import Rhone.Statistics.Identifiability.IntegrablePanMutationInterior

/-! # The complete finite equal-rates observation law determines its two mutation moments -/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal

namespace Rhone.Statistics.Identifiability.FiniteSiteObservation

theorem mass_eq_of_law_eq {K : ℕ} {k : ℝ} {μ ν : Measure (ℝ × ℝ)}
    (hK : 2 ≤ K) (hk : 0 ≤ k) (hμ : NonnegativeTimes μ) (hν : NonnegativeTimes ν)
    (heq : law K k μ = law K k ν) (a : Observation K) : mass K k μ a = mass K k ν a := by
  have hs := congrArg (fun ρ : Measure (Observation K) => ρ {a}) heq
  rw [law_singleton, law_singleton] at hs
  have hr := congrArg ENNReal.toReal hs
  simpa only [ENNReal.toReal_ofReal (mass_nonneg hK hk hμ a),
    ENNReal.toReal_ofReal (mass_nonneg hK hk hν a)] using hr

theorem momentPair_eq_of_law_eq {K : ℕ} {k : ℝ} {μ ν : Measure (ℝ × ℝ)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hK : 2 ≤ K) (hk : 0 ≤ k) (hμ : NonnegativeTimes μ) (hν : NonnegativeTimes ν)
    (hsymμ : μ.map Prod.fst = μ.map Prod.snd)
    (hsymν : ν.map Prod.fst = ν.map Prod.snd)
    (heq : law K k μ = law K k ν) : momentPair K k μ = momentPair K k ν := by
  let a : Fin K := ⟨0, by omega⟩
  let b : Fin K := ⟨1, by omega⟩
  have hab : a ≠ b := by
    intro h
    have hv := congrArg Fin.val h
    norm_num [a, b] at hv
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hK0 : (K : ℝ) ≠ 0 := by linarith
  have hK1 : (K : ℝ)-1 ≠ 0 := by linarith
  have hdd := mass_eq_of_law_eq hK hk hμ hν heq ((a,b),(a,b))
  rw [mass_eq_four_patterns hK hk hμ hsymμ,
    mass_eq_four_patterns hK hk hν hsymν] at hdd
  simp only [hab, ↓reduceIte] at hdd
  have hq : jointMoment K k μ = jointMoment K k ν := by
    have hn : (K : ℝ)^2 * ((K : ℝ)-1)^2 ≠ 0 := mul_ne_zero (pow_ne_zero _ hK0)
      (pow_ne_zero _ hK1)
    have h := congrArg (fun x : ℝ => x * ((K : ℝ)^2 * ((K : ℝ)-1)^2)) hdd
    simpa only [div_mul_cancel₀ _ hn] using h
  have hed := mass_eq_of_law_eq hK hk hμ hν heq ((a,a),(a,b))
  rw [mass_eq_four_patterns hK hk hμ hsymμ,
    mass_eq_four_patterns hK hk hν hsymν] at hed
  simp only [hab, ↓reduceIte] at hed
  have hpq : firstMoment K k μ - jointMoment K k μ =
      firstMoment K k ν - jointMoment K k ν := by
    have hn : (K : ℝ)^2 * ((K : ℝ)-1) ≠ 0 := mul_ne_zero (pow_ne_zero _ hK0) hK1
    have h := congrArg (fun x : ℝ => x * ((K : ℝ)^2 * ((K : ℝ)-1))) hed
    simpa only [div_mul_cancel₀ _ hn] using h
  apply Prod.ext
  · change firstMoment K k μ = firstMoment K k ν
    linarith
  · exact hq

theorem law_eq_iff_momentPair_eq {K : ℕ} {k : ℝ} {μ ν : Measure (ℝ × ℝ)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hK : 2 ≤ K) (hk : 0 ≤ k) (hμ : NonnegativeTimes μ) (hν : NonnegativeTimes ν)
    (hsymμ : μ.map Prod.fst = μ.map Prod.snd)
    (hsymν : ν.map Prod.fst = ν.map Prod.snd) :
    law K k μ = law K k ν ↔ momentPair K k μ = momentPair K k ν :=
  ⟨momentPair_eq_of_law_eq hK hk hμ hν hsymμ hsymν,
   law_eq_of_momentPair_eq hK hk hμ hν hsymμ hsymν⟩

theorem equalRatesMutation_law_eq_iff_momentPair_eq {K : ℕ} {k : ℝ}
    {μ ν : Measure (ℝ × ℝ)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hK : 2 ≤ K) (hk : 0 ≤ k) (hμ : NonnegativeTimes μ) (hν : NonnegativeTimes ν)
    (hsymμ : μ.map Prod.fst = μ.map Prod.snd)
    (hsymν : ν.map Prod.fst = ν.map Prod.snd) :
    EqualRatesMutation.observationLaw K k μ = EqualRatesMutation.observationLaw K k ν ↔
      momentPair K k μ = momentPair K k ν := by
  rw [EqualRatesMutation.observationLaw_eq hK, EqualRatesMutation.observationLaw_eq hK]
  exact law_eq_iff_momentPair_eq hK hk hμ hν hsymμ hsymν

theorem law_eq_pan_iff_momentPair_eq {K : ℕ} {k : ℝ} {μ : Measure (ℝ × ℝ)}
    [IsProbabilityMeasure μ] (P : ProperIntegrablePanModel)
    (hK : 2 ≤ K) (hk : 0 ≤ k) (hμ : NonnegativeTimes μ)
    (hsym : μ.map Prod.fst = μ.map Prod.snd) :
    law K k μ = law K k P.pre.jointLaw ↔
      momentPair K k μ = P.mutationMomentPair (limit K) k := by
  let := P.jointLaw_probability
  have hsymP : P.pre.jointLaw.map Prod.fst = P.pre.jointLaw.map Prod.snd := by
    rw [P.jointLaw_map_fst, P.jointLaw_map_snd]
  rw [law_eq_iff_momentPair_eq hK hk hμ (pan_nonnegativeTimes P) hsym hsymP,
    momentPair_eq_panMutationMomentPair]

theorem exists_fixedRecomb_observation_match_iff {K : ℕ} {k r : ℝ}
    {μ : Measure (ℝ × ℝ)} [IsProbabilityMeasure μ]
    (hK : 2 ≤ K) (hk : 0 < k) (hr : 0 ≤ r)
    (hμ : NonnegativeTimes μ) (hsym : μ.map Prod.fst = μ.map Prod.snd) :
    (∃ P : ProperIntegrablePanModel,
      P.pre.recomb = (fun _ => r) ∧ law K k μ = law K k P.pre.jointLaw) ↔
      momentPair K k μ ∈ MutationMomentSurjectivity.momentDomain (limit K) := by
  constructor
  · rintro ⟨P, _, hlaw⟩
    have hm := (law_eq_pan_iff_momentPair_eq P hK hk.le hμ hsym).1 hlaw
    rw [hm]
    exact P.mutationMomentPair_mem_momentDomain (limit_pos hK) hk
  · intro hm
    obtain ⟨P, hrP, heq⟩ := (exists_fixedRecomb_mutationMomentPair_iff
      (limit_pos hK) hk hr (momentPair K k μ)).2 hm
    exact ⟨P, hrP, law_eq_pan_of_momentPair_eq P hK hk.le hμ hsym heq.symm⟩

theorem exists_fixedRecomb_equalRatesMutation_match_iff {K : ℕ} {k r : ℝ}
    {μ : Measure (ℝ × ℝ)} [IsProbabilityMeasure μ]
    (hK : 2 ≤ K) (hk : 0 < k) (hr : 0 ≤ r)
    (hμ : NonnegativeTimes μ) (hsym : μ.map Prod.fst = μ.map Prod.snd) :
    (∃ P : ProperIntegrablePanModel,
      P.pre.recomb = (fun _ => r) ∧
      EqualRatesMutation.observationLaw K k μ =
        EqualRatesMutation.observationLaw K k P.pre.jointLaw) ↔
      momentPair K k μ ∈ MutationMomentSurjectivity.momentDomain (limit K) := by
  simp_rw [EqualRatesMutation.observationLaw_eq hK]
  exact exists_fixedRecomb_observation_match_iff hK hk hr hμ hsym

theorem exists_fourEpoch_equalRatesMutation_match_iff {K : ℕ} {k r : ℝ}
    {μ : Measure (ℝ × ℝ)} [IsProbabilityMeasure μ]
    (hK : 2 ≤ K) (hk : 0 < k) (hr : 0 ≤ r)
    (hμ : NonnegativeTimes μ) (hsym : μ.map Prod.fst = μ.map Prod.snd) :
    (∃ (ε δ M A τ : ℝ) (P : ProperIntegrablePanModel),
      0 < ε ∧ 0 < δ ∧ 0 < M ∧ 0 < A ∧ ε < τ ∧
      P.rate = MutationPulseKernel.fourEpochRate ε δ M A τ ∧
      P.pre.recomb = (fun _ => r) ∧
      (∀ t : ℝ, δ ≤ P.rate t ∧ P.rate t ≤ δ + (A + M) / ε) ∧
      EqualRatesMutation.observationLaw K k μ =
        EqualRatesMutation.observationLaw K k P.pre.jointLaw) ↔
      momentPair K k μ ∈ MutationMomentSurjectivity.momentDomain (limit K) := by
  constructor
  · rintro ⟨ε, δ, M, A, τ, P, _, _, _, _, _, _, hrP, _, hlaw⟩
    exact (exists_fixedRecomb_equalRatesMutation_match_iff hK hk hr hμ hsym).1
      ⟨P, hrP, hlaw⟩
  · exact exists_fourEpoch_equalRatesMutation_match hK hk hr hμ hsym

theorem exists_equalRatesMutation_match_iff {K : ℕ} {k : ℝ}
    {μ : Measure (ℝ × ℝ)} [IsProbabilityMeasure μ]
    (hK : 2 ≤ K) (hk : 0 < k)
    (hμ : NonnegativeTimes μ) (hsym : μ.map Prod.fst = μ.map Prod.snd) :
    (∃ P : ProperIntegrablePanModel,
      EqualRatesMutation.observationLaw K k μ =
        EqualRatesMutation.observationLaw K k P.pre.jointLaw) ↔
      momentPair K k μ ∈ MutationMomentSurjectivity.momentDomain (limit K) := by
  constructor
  · rintro ⟨P, hlaw⟩
    rw [EqualRatesMutation.observationLaw_eq hK, EqualRatesMutation.observationLaw_eq hK]
      at hlaw
    have hm := (law_eq_pan_iff_momentPair_eq P hK hk.le hμ hsym).1 hlaw
    rw [hm]
    exact P.mutationMomentPair_mem_momentDomain (limit_pos hK) hk
  · intro hm
    obtain ⟨P, _, hlaw⟩ := (exists_fixedRecomb_equalRatesMutation_match_iff
      hK hk (r := 0) le_rfl hμ hsym).2 hm
    exact ⟨P, hlaw⟩

end Rhone.Statistics.Identifiability.FiniteSiteObservation
