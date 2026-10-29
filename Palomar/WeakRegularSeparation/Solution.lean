module

public import Rhone.Statistics.WeakRegularSeparation.JointCriterion
public import Rhone.Statistics.FiniteBlockModel.IslandCriterion
public import Rhone.Statistics.FiniteBlockModel.FinitePhaseCriterion

@[expose] public section

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators
namespace Rhone.Palomar.WeakRegularSeparation
open Rhone.Algebra MarkovChain Statistics Statistics.WeakRegularSeparation
open CollapsedGenealogy ThreeSiteSeparator ThreeTipSites
open FiniteBlockModel Algebra.Identifiability MarkovChain.Identifiability Statistics.Identifiability
    ThreeSampleMembership

theorem nonnegative_internal_branch_separation_iff {k : ℝ} (hk : 0 < k)
    (μ : Measure Joint) [IsProbabilityMeasure μ]
    (hμ : NonnegativeJoint μ) (hu : ∀ᵐ g ∂μ, 0 < g.1.1)
    (P : FirstSurvivalProfile) (hP : P.Matches (μ.map Prod.fst)) :
    UniformlySeparated k μ ↔ μ ≠ uniformLift (PanThreeSample.durationLaw P.rate) :=
  Statistics.WeakRegularSeparation.nonnegative_internal_branch_separation_iff hk μ hμ hu P hP

theorem regular_profile_uniform_criterion {k : ℝ} (hk : 0 < k)
    (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ]
    (hμ : NonnegativeTimes μ) (hu : ∀ᵐ t ∂μ, 0 < t.1)
    (P : FirstSurvivalProfile) (hP : P.Matches μ) :
    UniformlySeparated k (uniformLift μ) ↔ μ ≠ PanThreeSample.durationLaw P.rate :=
  Statistics.WeakRegularSeparation.regular_profile_uniform_criterion hk μ hμ hu P hP

theorem island_uniformlySeparated_iff (ρ : ThreeSampling.State → ℝ) (n : ℕ)
    (c q : ℝ → ℝ) [IsProbabilityMeasure (ThreeSampling.law ρ n c q)]
    (hρ : ∀ i, 0 ≤ ρ i) (hρsum : ∑ i, ρ i = 1)
    (_hadmissible : n = 0 → ρ 2 = 0)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hcn : ∀ᵐ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t)
    {k : ℝ} (hk : 0 < k) :
    UniformlySeparated k (uniformLift (ThreeSampling.durationLaw ρ n c q)) ↔
      ¬(ρ = Pi.single 0 1 ∧ (∀ᵐ t, 0 ≤ t → q t = 0) ∧
        Tendsto (integrablePanClock c) atTop atTop) :=
  FiniteBlockModel.island_uniformlySeparated_iff ρ n c q hρ hρsum _hadmissible
    hc hq hcn hqn hk

theorem finitePhase_uniformlySeparated_iff {n m : ℕ} (M : IntegrablePhase.History n m)
    [IsProbabilityMeasure M.law] {k : ℝ} (hk : 0 < k) :
    UniformlySeparated k (uniformLift (durations M.law)) ↔ ¬M.DensityIdentity :=
  FiniteBlockModel.finitePhase_uniformlySeparated_iff M hk

end Rhone.Palomar.WeakRegularSeparation
end
