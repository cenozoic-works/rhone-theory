module

public import Rhone.Statistics.LinkedPairMoments.FiniteCriterion
public import Rhone.Statistics.LinkedPairMoments.InfiniteCriterion

@[expose] public section

namespace Rhone.Palomar.LinkedPairPanel

open MeasureTheory
open Statistics.PairObservationChannel Statistics.LinkedPairMoments

attribute [-instance] RCLike.toInnerProductSpaceReal RCLike.innerProductSpace

theorem panel_law_eq_iff_mass {K : ℕ} {H : Type*} [Fintype H] (E : Channel K H)
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {k : ℝ} (hk : 0 ≤ k)
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hν : ∀ᵐ t ∂ν, 0 ≤ t) (L : ℕ) :
    panelLaw E μ hk hμ L = panelLaw E ν hk hν L ↔
      ∀ x : Fin L → H × H, ∫ t, panelWeight E k t L x ∂μ = ∫ t, panelWeight E k t L x ∂ν := by
  constructor
  · intro h x
    exact congrArg (fun P => P.mass x) h
  · intro h
    exact finite_law_ext _ _ h

theorem panel_eq_iff {K : ℕ} {H : Type*} [Fintype H] (E : Channel K H) (hE : Informative E)
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {k : ℝ} (hk : 0 ≤ k)
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hν : ∀ᵐ t ∂ν, 0 ≤ t) (L : ℕ) :
    (∀ x : Fin L → H × H, ∫ t, panelWeight E k t L x ∂μ = ∫ t, panelWeight E k t L x ∂ν) ↔
      ∀ r : ℕ, r ≤ L → pairLaplace μ ((r : ℝ) * k) = pairLaplace ν ((r : ℝ) * k) := by
  rw [← panel_law_eq_iff_mass E μ ν hk hμ hν L]
  exact Rhone.Statistics.LinkedPairMoments.panel_eq_iff E hE μ ν hk hμ hν L

theorem panel_erased {K : ℕ} {H : Type*} [Fintype H] (E : Channel K H)
    (hE : retainedVariance E = 0) (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {k : ℝ} (hk : 0 ≤ k)
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hν : ∀ᵐ t ∂ν, 0 ≤ t) (L : ℕ) (x : Fin L → H × H) :
    ∫ t, panelWeight E k t L x ∂μ = ∫ t, panelWeight E k t L x ∂ν :=
  (panel_law_eq_iff_mass E μ ν hk hμ hν L).mp
    (Rhone.Statistics.LinkedPairMoments.panel_erased E hE μ ν hk hμ hν L) x

theorem next_moment_upgrade {K : ℕ} {H : Type*} [Fintype H] (E : Channel K H)
    (hE : Informative E) (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {k : ℝ} (hk : 0 ≤ k)
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hν : ∀ᵐ t ∂ν, 0 ≤ t) (L : ℕ)
    (hm : ∀ r : ℕ, r ≤ L → pairLaplace μ ((r : ℝ) * k) = pairLaplace ν ((r : ℝ) * k))
    (hnext : pairLaplace μ (((L + 1 : ℕ) : ℝ) * k) ≠
      pairLaplace ν (((L + 1 : ℕ) : ℝ) * k)) :
    (∀ x : Fin L → H × H, ∫ t, panelWeight E k t L x ∂μ = ∫ t, panelWeight E k t L x ∂ν) ∧
      ∃ x : Fin (L + 1) → H × H,
        ∫ t, panelWeight E k t (L + 1) x ∂μ ≠ ∫ t, panelWeight E k t (L + 1) x ∂ν := by
  obtain ⟨h1, h2⟩ :=
    Rhone.Statistics.LinkedPairMoments.next_moment_upgrade E hE μ ν hk hμ hν L hm hnext
  refine ⟨(panel_law_eq_iff_mass E μ ν hk hμ hν L).mp h1, ?_⟩
  by_contra hc
  push Not at hc
  exact h2 ((panel_law_eq_iff_mass E μ ν hk hμ hν (L + 1)).mpr hc)

theorem all_panels_eq_iff {K : ℕ} {H : Type*} [Fintype H] (E : Channel K H)
    (hE : Informative E) (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {k : ℝ} (hk : 0 < k)
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hν : ∀ᵐ t ∂ν, 0 ≤ t) :
    (∀ (L : ℕ) (x : Fin L → H × H),
      ∫ t, panelWeight E k t L x ∂μ = ∫ t, panelWeight E k t L x ∂ν) ↔ μ = ν := by
  rw [← Rhone.Statistics.LinkedPairMoments.all_panels_eq_iff E hE μ ν hk hμ hν]
  exact forall_congr' fun L => (panel_law_eq_iff_mass E μ ν hk.le hμ hν L).symm

end Rhone.Palomar.LinkedPairPanel
