/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.FinitePhaseSurvivalProfile

/-! # Exact finite algebraic pan-membership certificate for homogeneous two-stage laws -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory Matrix
open scoped Topology Matrix Matrix.Norms.Operator
namespace Rhone.Statistics.Identifiability.FinitePhase.Model
open FiniteExponentialJets ThreeSampleMembership
variable {n m : ℕ} [NeZero n] [NeZero m]

def Certificate (M : Model n m) : Prop :=
  ∀ i : ℕ, i < n + ((n + m) * (n + m)) * (n + m) → ∀ l : ℕ, l < m + (n + m) →
    kernelValue M.α M.F (exitRate M.B) (M.A ^ i) (M.B ^ l) =
      kernelValue (tensorRow (tensorRow M.γ M.γ) M.γ)
        (tripleFlux M.h (M.N *ᵥ M.h)) (M.N *ᵥ M.h)
        (tripleGenerator M.N ^ i) (M.N ^ l)

theorem pan_representable_iff_certificate (M : Model n m) [IsProbabilityMeasure M.law] :
    PanRepresentable M.law ↔ M.Certificate := by
  have he := finite_realized_pan_membership M.profile M.density M.density_continuous
    (fun _ hp => M.density_nonnegative hp) M.profile_matches
    M.A M.B M.α M.F (exitRate M.B) M.N M.γ M.h
    (fun s t _ _ => orderedKernelDensity_duration M.A M.B M.α M.F (exitRate M.B) s t)
    (fun _ => rfl)
  simpa only [Fintype.card_fin, Certificate, law, FinitePhase.law, density] using he

theorem pan_representable_iff_mass_and_certificate (M : Model n m) :
    PanRepresentable M.law ↔ M.law univ = 1 ∧ M.Certificate := by
  constructor
  · intro hp
    obtain ⟨rate, hr, hn, ht, he⟩ := hp
    have he' := he.trans
      (PanThreeSample.law_congr_halfLine_ae (PanThreeSample.representative_eq_ae hn))
    have hprob : IsProbabilityMeasure M.law := by
      rw [he']
      exact PanThreeSample.isProbability _ (PanThreeSample.representative_locallyIntegrable hr)
        (PanThreeSample.representative_nonneg rate)
        (PanThreeSample.representative_clock_diverges hn ht)
    let := hprob
    exact ⟨measure_univ, (M.pan_representable_iff_certificate).mp ⟨rate, hr, hn, ht, he⟩⟩
  · rintro ⟨hmass, hc⟩
    let : IsProbabilityMeasure M.law := ⟨hmass⟩
    exact M.pan_representable_iff_certificate.mpr hc

def densityResidual (M : Model n m) (s t : ℝ) : ℝ :=
  M.density (s,t) - 3 * M.u s * M.d s * M.d t

theorem exists_densityResidual_ne_zero (M : Model n m) [IsProbabilityMeasure M.law]
    (hc : ¬M.Certificate) : ∃ s t : ℝ, 0 < s ∧ s < t ∧ M.densityResidual s t ≠ 0 := by
  have hne : ¬EqOn M.density M.profile.candidateDensity upperWedge := by
    intro he
    have hp := (M.profile.pan_representable_iff_density M.density M.density_continuous
      (fun _ hp => M.density_nonnegative hp) M.profile_matches).mpr he
    exact hc (M.pan_representable_iff_certificate.mp hp)
  have hex : ∃ p ∈ upperWedge, M.density p ≠ M.profile.candidateDensity p := by
    simpa only [EqOn, not_forall, exists_prop] using hne
  obtain ⟨p, hp, he⟩ := hex
  refine ⟨p.1, p.2, hp.1, hp.2, ?_⟩
  simpa only [densityResidual, sub_ne_zero, SmoothPairSurvival.candidateDensity, profile] using he

end Rhone.Statistics.Identifiability.FinitePhase.Model
