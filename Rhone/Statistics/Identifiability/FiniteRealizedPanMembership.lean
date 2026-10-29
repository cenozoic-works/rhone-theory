/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.SmoothPairSurvivalMembership
public import Rhone.Statistics.Identifiability.TripleSurvivalKernel

/-! # Finite certificates for laws with proved finite survival and density realizations -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory Matrix
open scoped Topology Matrix Matrix.Norms.Operator
namespace Rhone.Statistics.Identifiability.ThreeSampleMembership
open FiniteExponentialJets

variable {ι κ η : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Nonempty κ]
  [Fintype η] [DecidableEq η] [Nonempty η]

theorem finite_realized_pan_membership (P : SmoothPairSurvival) (j : ℝ × ℝ → ℝ)
    (hj : Continuous j) (hn : ∀ p ∈ upperWedge, 0 ≤ j p)
    (hm : P.Matches (triangularDensityLaw j))
    (A : Matrix κ κ ℝ) (B : Matrix η η ℝ) (α : κ → ℝ) (F : Matrix κ η ℝ) (v : η → ℝ)
    (Q : Matrix ι ι ℝ) (γ h : ι → ℝ)
    (hk : ∀ s t : ℝ, 0 < s → 0 < t → j (s,s + t) =
      kernelValue α F v (NormedSpace.exp (s • A)) (NormedSpace.exp (t • B)))
    (hu : ∀ t : ℝ, P.u t = dotProduct γ (NormedSpace.exp (t • Q) *ᵥ h)) :
    PanRepresentable (triangularDensityLaw j) ↔
    (∀ i : ℕ, i < Fintype.card κ + (Fintype.card ι * Fintype.card ι) * Fintype.card ι →
      ∀ l : ℕ, l < Fintype.card η + Fintype.card ι →
      kernelValue α F v (A ^ i) (B ^ l) =
        kernelValue (tensorRow (tensorRow γ γ) γ) (tripleFlux h (Q *ᵥ h)) (Q *ᵥ h)
          (tripleGenerator Q ^ i) (Q ^ l)) := by
  have hd : ∀ t : ℝ, P.d t = dotProduct γ (NormedSpace.exp (t • Q) *ᵥ (Q *ᵥ h)) := by
    intro t
    have hder := scalar_output_hasDerivAt Q γ h t
    exact (P.derivative t).unique (hder.congr_of_eventuallyEq (Eventually.of_forall hu))
  rw [P.pan_representable_iff_density j hj hn hm]
  rw [← candidate_kernel_equal_iff_finite A B α F v Q γ h]
  constructor
  · intro he s t hs ht
    rw [← hk s t hs ht]
    have hw : (s,s + t) ∈ upperWedge := ⟨hs, by linarith⟩
    have hp := he hw
    simpa only [SmoothPairSurvival.candidateDensity, hu, hd] using hp
  · intro he p hp
    have ht : 0 < p.2 - p.1 := sub_pos.mpr hp.2
    have h := he p.1 (p.2 - p.1) hp.1 ht
    rw [← hk p.1 (p.2 - p.1) hp.1 ht] at h
    have hadd : p.1 + (p.2 - p.1) = p.2 := by ring
    simpa only [SmoothPairSurvival.candidateDensity, hu, hd, hadd,
      Prod.mk.eta] using h

end Rhone.Statistics.Identifiability.ThreeSampleMembership
