/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ReachableAbsorption
public import Rhone.Statistics.Identifiability.PairAbsorption
public import Rhone.Statistics.Identifiability.PairProjection

/-! # Eventual first coalescence, derived from the B-pair projection certificate -/

@[expose] public section

open scoped Matrix Matrix.Norms.Operator Topology
open Filter
namespace Rhone.Statistics.Identifiability

noncomputable def islandLyapunov (k : Nat) (c q : ℝ) : MarkovChain.Identifiability.State → ℝ :=
  bProjection *ᵥ pairLyapunov k c q

theorem islandLyapunov_ge_one (k : Nat) {c q : ℝ} (hc : 0 < c) (hq : 0 < q) :
    ∀ i, 1 ≤ islandLyapunov k c q i := by
  intro i
  have h0 := pairLyapunov_ge_one k hc hq 0
  have h1 := pairLyapunov_ge_one k hc hq 1
  simp only [islandLyapunov, bProjection, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  split <;> simpa using (by assumption : 1 ≤ pairLyapunov k c q _)

theorem islandLyapunov_drift (k : Nat) {c q r : ℝ}
    (hc : 0 < c) (hq : 0 < q) (i : MarkovChain.Identifiability.State) (hi : Admissible k i) :
    (MarkovChain.Identifiability.generator k c q r *ᵥ islandLyapunov k c q) i ≤ -1 := by
  have h := Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) =>
    congrArg (fun z : ℝ => z * pairLyapunov k c q j)
      (pair_projection_generator k c q r i hi j))
  change ((MarkovChain.Identifiability.generator k c q r * bProjection + firstAKernel c) *ᵥ
      pairLyapunov k c q) i =
    ((bProjection * MarkovChain.Identifiability.pairGenerator k c q) *ᵥ pairLyapunov k c q) i at h
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at h
  have hE : 0 ≤ (firstAKernel c *ᵥ pairLyapunov k c q) i :=
    matrix_mulVec_nonneg _ _ (firstAKernel_nonneg hc.le)
      (fun j => le_trans zero_le_one (pairLyapunov_ge_one k hc hq j)) i
  have hR : (bProjection *ᵥ (MarkovChain.Identifiability.pairGenerator k c q *ᵥ pairLyapunov k c q))
      i ≤ -1 := by
    rw [pairLyapunov_drift k hc.ne' hq.ne']
    simp only [bProjection, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    split <;> simp
    linarith
  change (MarkovChain.Identifiability.generator k c q r *ᵥ islandLyapunov k c q) i +
    (firstAKernel c *ᵥ pairLyapunov k c q) i = _ at h
  linarith

theorem island_survival_tendsto_zero (k : Nat) {c q r : ℝ}
    (hc : 0 < c) (hq : 0 < q) (hr : 0 ≤ r) :
    Tendsto (flowOutput (MarkovChain.Identifiability.generator k c q r) 0 (fun _ => 1) 0) atTop
        (𝓝 0) :=
  survival_tendsto_zero_of_reachable_lyapunov _ (generator_metzler k hc.le hq.le hr)
    (Admissible k) (generator_no_escape k c q r) (islandLyapunov k c q)
    (islandLyapunov_ge_one k hc hq) zero_lt_one (islandLyapunov_drift k hc hq)
    0 (initial_admissible k)

end Rhone.Statistics.Identifiability
