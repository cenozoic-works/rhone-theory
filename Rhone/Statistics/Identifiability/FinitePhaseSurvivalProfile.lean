/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.FinitePhaseModel
public import Rhone.Statistics.Identifiability.PositiveSurvivalTail

/-! # Every proper finite homogeneous two-stage law supplies the observed smooth survival profile -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory Matrix
open scoped Topology Matrix Matrix.Norms.Operator
namespace Rhone.Statistics.Identifiability.FinitePhase.Model
open FiniteExponentialJets ThreeSampleMembership
variable {n m : ℕ}

lemma u_derivative (M : Model n m) (t : ℝ) : HasDerivAt M.u (M.d t) t :=
  scalar_output_hasDerivAt M.N M.γ M.h t

lemma d_continuous (M : Model n m) : Continuous M.d :=
  continuous_iff_continuousAt.mpr fun t =>
    (scalar_output_hasDerivAt M.N M.γ (M.N *ᵥ M.h) t).continuousAt

lemma u_initial (M : Model n m) : M.u 0 = 1 := by
  rw [M.u_survivals]
  simp [WeightedExit.survival, M.α_sum, M.γ_sum]
  norm_num

lemma u_positive (M : Model n m) {t : ℝ} (ht : 0 ≤ t) : 0 < M.u t := by
  rw [M.u_survivals]
  have hp := WeightedExit.survival_positive M.A M.α M.A_metzler
    M.α_nonnegative M.α_sum ht
  have hn := WeightedExit.survival_nonnegative M.N M.γ M.N_metzler M.γ_nonnegative ht
  linarith

lemma d_nonpositive (M : Model n m) {t : ℝ} (ht : 0 ≤ t) : M.d t ≤ 0 := by
  have hd := ((WeightedExit.survival_derivative M.A M.α t).const_mul (1/3 : ℝ)).add
    ((WeightedExit.survival_derivative M.N M.γ t).const_mul (2/3 : ℝ))
  have heq : M.u =ᶠ[𝓝 t] (fun s => (1/3 : ℝ) * WeightedExit.survival M.A M.α s +
      (2/3 : ℝ) * WeightedExit.survival M.N M.γ s) :=
    Eventually.of_forall M.u_survivals
  have he := (M.u_derivative t).unique (hd.congr_of_eventuallyEq heq)
  have h1 := WeightedExit.density_nonnegative M.A M.α M.A_metzler M.A_rows M.α_nonnegative ht
  have h2 := WeightedExit.density_nonnegative M.N M.γ M.N_metzler M.N_rows M.γ_nonnegative ht
  linarith

lemma u_proper (M : Model n m) [IsProbabilityMeasure M.law] : Tendsto M.u atTop (𝓝 0) := by
  let : IsProbabilityMeasure (M.law.map Prod.fst) :=
    inferInstance
  let : IsProbabilityMeasure (M.law.map Prod.snd) :=
    inferInstance
  have hp1 : ∀ᵐ t ∂M.law.map Prod.fst, 0 < t := by
    rw [M.first_marginal]
    exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioi)
  have hp2 : ∀ᵐ t ∂M.law.map Prod.snd, 0 < t := by
    rw [M.root_marginal]
    exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioi)
  have ht := ((positive_probability_survival_tendsto_zero _ hp1).const_mul (1/3 : ℝ)).add
    ((positive_probability_survival_tendsto_zero _ hp2).const_mul (2/3 : ℝ))
  have hw : Tendsto (weightedSurvival M.law) atTop (𝓝 0) := by
    unfold weightedSurvival
    simpa using ht
  apply hw.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht0
  exact M.weighted_survival_eq t ht0

def profile (M : Model n m) [IsProbabilityMeasure M.law] : SmoothPairSurvival where
  u := M.u
  d := M.d
  continuous_d := M.d_continuous
  derivative := M.u_derivative
  initial := M.u_initial
  positive := fun _ ht => M.u_positive ht
  decreasing := fun _ ht => M.d_nonpositive ht
  proper := M.u_proper

lemma profile_matches (M : Model n m) [IsProbabilityMeasure M.law] :
    M.profile.Matches M.law := M.weighted_survival_eq

end Rhone.Statistics.Identifiability.FinitePhase.Model
