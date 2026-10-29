/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeSamplingNormalizedODE
public import Rhone.Statistics.Identifiability.ThreeSamplingTraceRigidity

/-! # Conditional trace rigidity for the island flow from an arbitrary initial row -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology
namespace Rhone.Statistics.Identifiability.ThreeSampling

theorem trace_rigidity (ρ : State → ℝ) (k : ℕ) (c q H : ℝ → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (hρsum : ∑ i, ρ i = 1)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hcn : ∀ᵐ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t)
    (hHac : ∀ a b, 0 ≤ a → a ≤ b → AbsolutelyContinuousOnInterval H a b)
    (hHd : ∀ᵐ t, 0 ≤ t → HasDerivAt H (3 * c t * normalizedX ρ k c q t) t)
    (htrace : ∀ᵐ t, 0 ≤ t → 0 < c t →
      normalizedY ρ k c q t = (normalizedX ρ k c q t) ^ 2)
    (hproper : Tendsto H atTop atTop) :
    ρ = Pi.single 0 1 ∧ (∀ᵐ t, 0 ≤ t → q t = 0) := by
  have hbounds (t : ℝ) (ht : 0 ≤ t) :=
    normalized_coordinates_bounds ρ k c q hρ hρsum hc hq hqn ht
  have hn : (1 : ℝ) < k + 2 := by have hk := Nat.cast_nonneg (α := ℝ) k; linarith
  have hnorm := normalized_trace_rigidity (k + 2) hn c q
    (normalizedX ρ k c q) (normalizedY ρ k c q) H hcn hqn
    (fun t ht => (hbounds t ht).1) (fun t ht => (hbounds t ht).2)
    (fun a b ha hab => (normalized_coordinates_ac ρ k c q hρ hρsum hc hq hqn ha hab).1)
    hHac (normalizedX_derivative_ae ρ k c q hρ hρsum hc hq hqn)
    (normalizedY_derivative_ae ρ k c q hρ hρsum hc hq hqn) hHd htrace hproper
  have hinit : survival ρ k c q 0 = 1 := by
    unfold survival
    rw [preRow_initial ρ k c q hc hq]
    exact hρsum
  have hρ0 : ρ 0 = 1 := by
    have hy := (hnorm.1 0 le_rfl).2
    simpa only [normalizedY, hinit, preRow_initial ρ k c q hc hq, div_one] using hy
  refine ⟨?_, hnorm.2⟩
  have hs : ρ 0 + ρ 1 + ρ 2 = 1 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hρsum
  have hρ1 : ρ 1 = 0 := by linarith [hρ 1, hρ 2]
  have hρ2 : ρ 2 = 0 := by linarith [hρ 1, hρ 2]
  ext i
  fin_cases i <;> simp [hρ0, hρ1, hρ2]

end Rhone.Statistics.Identifiability.ThreeSampling
