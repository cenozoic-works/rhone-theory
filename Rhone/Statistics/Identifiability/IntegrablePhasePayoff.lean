/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegrablePhaseDuhamel

/-! # Integrable column kernels and exact post-event payoffs for arbitrary finite L1 histories -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory Matrix
open scoped Topology Matrix
namespace Rhone.Statistics.Identifiability.IntegrablePhase
variable {n m : ℕ}
variable (N : ℝ → Matrix (Fin (n + m)) (Fin (n + m)) ℝ)
  (A : ℝ → Matrix (Fin n) (Fin n) ℝ) (B : ℝ → Matrix (Fin m) (Fin m) ℝ)
  (F : ℝ → Matrix (Fin n) (Fin m) ℝ)
  (hN : ∀ i j, LocallyIntegrable (fun t => N t i j) volume)
  (hA : ∀ i j, LocallyIntegrable (fun t => A t i j) volume)
  (hB : ∀ i j, LocallyIntegrable (fun t => B t i j) volume)
  (hpp : ∀ᵐ t, ∀ i j, N t (Fin.castAdd m i) (Fin.castAdd m j) = A t i j)
  (hlp : ∀ᵐ t, ∀ i j, N t (Fin.natAdd n i) (Fin.castAdd m j) = 0)
  (hpl : ∀ᵐ t, ∀ i j, N t (Fin.castAdd m i) (Fin.natAdd n j) = F t i j)
  (hll : ∀ᵐ t, ∀ i j, N t (Fin.natAdd n i) (Fin.natAdd n j) = B t i j)

include hN hA hB hpp hlp hpl hll

lemma post_transport_integrable (a b : ℝ) (i : Fin n) (j : Fin m) :
    IntervalIntegrable (fun s => (entryRow A F a i s ᵥ* inhomogeneousTransition B s b) j)
      volume a b := by
  apply finiteRow_integrable_transport_intervalIntegrable B hB
    (postRow N a i) (entryRow A F a i) a b b
    (fun j => integrableTransition_entry_ac_right N hN a a b _ _) _ j
  filter_upwards [postRow_ae_hasDerivAt N A B F hN hA hpp hlp hpl hll a i]
    with t ht _
  exact ht

lemma post_payoff_intervalIntegrable (a b : ℝ) (i : Fin n) (w : Fin m → ℝ) :
    IntervalIntegrable (fun s =>
      ((inhomogeneousTransition A a s * F s * inhomogeneousTransition B s b) *ᵥ w) i)
      volume a b := by
  change IntervalIntegrable (fun s => ∑ j,
    (entryRow A F a i s ᵥ* inhomogeneousTransition B s b) j * w j) volume a b
  convert! IntervalIntegrable.sum Finset.univ (fun j _ =>
    (post_transport_integrable N A B F hN hA hB hpp hlp hpl hll a b i j).mul_const (w j)) using 1
  funext s
  simp only [Finset.sum_apply]

lemma post_payoff_integral (a b : ℝ) (i : Fin n) (w : Fin m → ℝ) :
    (∫ s in a..b,
      ((inhomogeneousTransition A a s * F s * inhomogeneousTransition B s b) *ᵥ w) i) =
      ∑ j, postRow N a i b j * w j := by
  change (∫ s in a..b, ∑ j,
    (entryRow A F a i s ᵥ* inhomogeneousTransition B s b) j * w j) = _
  rw [intervalIntegral.integral_finsetSum (fun j _ =>
    (post_transport_integrable N A B F hN hA hB hpp hlp hpl hll a b i j).mul_const (w j))]
  simp_rw [intervalIntegral.integral_mul_const]
  apply Finset.sum_congr rfl
  intro j _
  rw [← post_duhamel N A B F hN hA hB hpp hlp hpl hll]

end Rhone.Statistics.Identifiability.IntegrablePhase
