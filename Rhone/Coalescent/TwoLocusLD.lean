/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.TwoLocusArgAgreement
public import Rhone.MarkovChain.WFLDStationaryLimit

/-!
# Stationary LD ratio as the paired-exit probability of the recombination graph

Source: mcvean2002, eq. (9), (12), pp. 988–989; ohta_kimura1971_ld, eq. (9), p. 574;
wilton_carmi_hobolth2015, eq. (5), Figure S1. -/

@[expose] public section
namespace Rhone.Coalescent
open MeasureTheory ProbabilityTheory Filter Finset Rhone.LinearAlgebra MarkovChain TwoLocusGenealogy
  MarkovChain.WFAllocationLD
open scoped ENNReal Topology

def pairedExitEvent : Set (ℕ → ASt 2) :=
  {ω | ∃ k, (∀ j ≤ k, ω j ∈ pairedSet) ∧ ω (k + 1) ∈ doneSet}

/-- Source: wilton_carmi_hobolth2015, eq. (5), Figure S1. -/
theorem argTraj_real_pairedExit (ρ : ℝ) (hρ : 0 ≤ ρ) {s : ASt 2} (hs : IsPaired s) :
    (argTraj 0 0 ρ le_rfl le_rfl hρ s).real pairedExitEvent =
      IntervalProcess.twoLocusValue ρ (tt s) := by
  have hAB : Disjoint pairedSet doneSet := by
    rw [Set.disjoint_left]
    intro M hM hd
    have := (IsPaired.counts hM).1
    have := hd.1
    omega
  exact pathLaw_real_firstExit_of_stayedIn (argChain 0 0 ρ le_rfl le_rfl hρ).toProcess
    (A := pairedSet) (B := doneSet) MeasurableSet.of_discrete MeasurableSet.of_discrete hAB
    (h := fun L : ASt 2 => IntervalProcess.twoLocusValue ρ (tt L)) Measurable.of_discrete
    (M := 1)
    (fun s => abs_le.2 ⟨by
        have := IntervalProcess.twoLocusValue_nonneg ρ hρ (tt s)
        linarith, IntervalProcess.twoLocusValue_le_one ρ hρ _⟩)
    (fun s hs => by
      change ∫ y, pairedSet.indicator (fun L : ASt 2 => IntervalProcess.twoLocusValue ρ (tt L)) y
        ∂(argChain 0 0 ρ le_rfl le_rfl hρ).kernel s +
          ((argChain 0 0 ρ le_rfl le_rfl hρ).kernel s).real doneSet = _
      rw [← integral_indicator_one (MeasurableSet.of_discrete),
        ← integral_add Integrable.of_finite Integrable.of_finite,
        integral_kernel_pairedClass ρ hρ _ (exitValue ρ) (exit_indicator ρ) hs]
      exact pairedStepValue_exitValue ρ hρ (IsPaired.tt_le hs))
    s hs (tendsto_pathLaw_stayedIn_pairedSet ρ hρ s)

/-- Source: mcvean2002, eq. (12), p. 989; ohta_kimura1971_ld, eq. (9), p. 574. -/
theorem twoLocusValue_sigma (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (IntervalProcess.twoLocusValue ρ 2 - 2 * IntervalProcess.twoLocusValue ρ 1 +
        IntervalProcess.twoLocusValue ρ 0) / (1 + IntervalProcess.twoLocusValue ρ 0) =
      (10 + ρ) / (22 + 13 * ρ + ρ ^ 2) := by
  have hD : ρ ^ 2 + 13 * ρ + 18 ≠ 0 := by positivity
  have hE : (22 : ℝ) + 13 * ρ + ρ ^ 2 ≠ 0 := by positivity
  have hF : ρ ^ 2 + 13 * ρ + 18 + 4 ≠ 0 := by positivity
  simp only [IntervalProcess.twoLocusValue]
  field_simp
  ring

/-- Source: mcvean2002, eq. (9), (12), pp. 988–989; ohta_kimura1971_ld, eq. (9), p. 574. -/
theorem ld_stationary_sigma_limit_eq_pairedExit (N : ℕ → ℕ) (u : ℕ → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hN : ∀ n, 3 ≤ N n) (hc : ∀ n, R / (2 * (N n : ℝ)) ≤ 1)
    (hu0 : ∀ n, 0 < u n) (hu1 : ∀ n, u n < 1 / 2)
    (π : (n : ℕ) → Rhone.MarkovChain.AlleleCounts (N n) 4 → ℝ)
    (hπ : ∀ n a, 0 ≤ π n a) (hnorm : ∀ n, ∑ a, π n a = 1)
    (hstat : ∀ n b, ∑ a, π n a *
      forcedCountKernel (N n) (R / (2 * (N n : ℝ))) (u n) a b = π n b)
    (hlarge : Tendsto (fun n => (N n : ℝ)) atTop atTop)
    (hrare : Tendsto (fun n => u n * (N n : ℝ)) atTop (𝓝 0))
    {s₂ s₁ s₀ : ASt 2} (h₂ : IsPaired s₂) (h₁ : IsPaired s₁) (h₀ : IsPaired s₀)
    (ht₂ : tt s₂ = 2) (ht₁ : tt s₁ = 1) (ht₀ : tt s₀ = 0) :
    Tendsto (fun n => ldStationaryMoments (N n) (π n) 2 / ldStationaryMoments (N n) (π n) 0)
      atTop (𝓝 (((argTraj 0 0 R le_rfl le_rfl hR s₂).real pairedExitEvent -
          2 * (argTraj 0 0 R le_rfl le_rfl hR s₁).real pairedExitEvent +
          (argTraj 0 0 R le_rfl le_rfl hR s₀).real pairedExitEvent) /
        (1 + (argTraj 0 0 R le_rfl le_rfl hR s₀).real pairedExitEvent))) := by
  rw [argTraj_real_pairedExit R hR h₂, argTraj_real_pairedExit R hR h₁,
    argTraj_real_pairedExit R hR h₀, ht₂, ht₁, ht₀, twoLocusValue_sigma R hR]
  exact ld_stationary_sigma_limit N u R hR hN hc hu0 hu1 π hπ hnorm hstat hlarge hrare

theorem pairedExit_instance :
    IsPaired ({({0}, {0}), ({1}, {1})} : Finset (Lin 2)) ∧
    IsPaired ({({0}, {0}), ({1}, ∅), (∅, {1})} : Finset (Lin 2)) ∧
    IsPaired ({({0}, ∅), ({1}, ∅), (∅, {0}), (∅, {1})} : Finset (Lin 2)) ∧
    tt ({({0}, {0}), ({1}, {1})} : Finset (Lin 2)) = 2 ∧
    tt ({({0}, {0}), ({1}, ∅), (∅, {1})} : Finset (Lin 2)) = 1 ∧
    tt ({({0}, ∅), ({1}, ∅), (∅, {0}), (∅, {1})} : Finset (Lin 2)) = 0 := by
  refine ⟨Or.inl rfl, Or.inr (Or.inr (Or.inl rfl)),
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))), ?_, ?_, ?_⟩ <;> decide

end Rhone.Coalescent
