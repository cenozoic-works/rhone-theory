/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.SilentPureRecombination
public import Rhone.Statistics.Identifiability.DelayedHistorySeparation

/-! # Silent-window witness positivity when migration ceases during recombination -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology Matrix
namespace Rhone.Statistics.Identifiability.SilentWindow
open SimultaneousOnset DelayedOnset

lemma recombinationPrefixRow_nonnegative {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (i : ProductState) : 0 ≤ recombinationPrefixRow x y i := by
  simp only [recombinationPrefixRow, Pi.add_apply, Pi.single_apply]
  split_ifs <;> positivity

lemma recombinationPrefixRow_initial_payoff (x y : ℝ) :
    recombinationPrefixRow x y ⬝ᵥ witnessVec = 0 := by
  have he : recombinationPrefixRow x y ⬝ᵥ witnessVec =
      rowPayoff (recombinationPrefixRow x y) (1 : Matrix ProductState ProductState ℝ)
        witnessVec := by simp [rowPayoff, dotProduct]
  rw [he]
  simp [recombinationPrefixRow, rowPayoff_add, rowPayoff_single, witnessVec,
    MarkovChain.Identifiability.firstATable, MarkovChain.Identifiability.firstAThenBTable]

theorem witness_positive_after_pure_recombination_window (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hqn : ∀ u, 0 ≤ u → 0 ≤ q u)
    (hrn : ∀ u, 0 ≤ u → 0 ≤ r u) {a T : ℝ} (ha : 0 ≤ a) (hT : 0 ≤ T)
    (hbefore : ∀ u ∈ Icc 0 a, r u = 0) (hQ : 0 < ∫ u in (0 : ℝ)..a, q u)
    (hsilent : ∀ u ∈ Icc a (a + T), c u = 0 ∧ q u = 0)
    (hR : 0 < ∫ u in (0 : ℝ)..T, r (a + u)) :
    0 < SimultaneousOnset.witness k c q r (a + T) := by
  have hx := pairRow_together_positive k c q hc hq hqn ha
  have hy := pairRow_apart_positive k c q hc hq hqn ha hQ
  let ρ := recombinationPrefixRow (pairRow k c q a 0) (pairRow k c q a 1)
  have hp := pure_recombination_payoff_positive k (fun u => r (a + u))
    (hr.comp (continuous_const.add continuous_id))
    (fun u hu => hrn _ (add_nonneg ha hu)) ρ
    (recombinationPrefixRow_nonnegative hx.le hy.le)
    (by simpa [ρ, recombinationPrefixRow, Pi.single_apply] using mul_pos hx hy)
    (by simpa only [ρ, recombinationPrefixRow_initial_payoff] using (le_refl (0 : ℝ))) hT hR
  rw [witness_restart k c q r hc hq hr,
    recombination_prefix_of_zero_history k c q r hc hq hr ha hbefore]
  have he := inhomogeneousTransition_eq_of_eqOn
    (fun u => productGenerator k (c (a + u)) (q (a + u)) (r (a + u)))
    (fun u => productGenerator k 0 0 (r (a + u)))
    (productGenerator_history_continuous k (fun u => c (a + u)) (fun u => q (a + u))
      (fun u => r (a + u)) (hc.comp (continuous_const.add continuous_id))
      (hq.comp (continuous_const.add continuous_id)) (hr.comp (continuous_const.add continuous_id)))
    (productGenerator_history_continuous k (fun _ => 0) (fun _ => 0) (fun u => r (a + u))
      continuous_const continuous_const (hr.comp (continuous_const.add continuous_id))) hT
    (fun u hu => by
      have h := hsilent (a + u) ⟨by linarith [hu.1], by linarith [hu.2]⟩
      dsimp only
      rw [h.1, h.2])
  rw [he]
  exact hp

end Rhone.Statistics.Identifiability.SilentWindow
