/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.DelayedOnsetRestart
public import Rhone.Statistics.Identifiability.TimeVaryingProjectionDuhamel

/-! # Exact two-carrier prefix reconstruction before recombination starts -/

@[expose] public section

open Set
open scoped BigOperators Topology Matrix
namespace Rhone.Statistics.Identifiability.DelayedOnset
open SimultaneousOnset

noncomputable def extendPair (v : Fin 2 → ℝ) : MarkovChain.Identifiability.State → ℝ :=
  Pi.single 0 (v 0) + Pi.single 1 (v 1)

set_option maxHeartbeats 600000 in
lemma extendPair_vecMul (k : ℕ) (c q : ℝ) (v : Fin 2 → ℝ) :
    extendPair v ᵥ* MarkovChain.Identifiability.generator k c q 0 = extendPair
        (v ᵥ* MarkovChain.Identifiability.pairGenerator k c q) := by
  ext j
  fin_cases j <;>
    simp [extendPair, Matrix.vecMul, dotProduct, Fin.sum_univ_succ, Pi.single_apply,
      MarkovChain.Identifiability.generator, MarkovChain.Identifiability.pairGenerator,
          MarkovChain.Identifiability.totalMigration, MarkovChain.Identifiability.coalescenceTable,
          MarkovChain.Identifiability.occupiedTable,
      MarkovChain.Identifiability.emptyTable, MarkovChain.Identifiability.occupiedDemes] <;> ring

lemma extendPair_hasDerivAt (k : ℕ) (c q : ℝ → ℝ) (hc : Continuous c) (hq : Continuous q)
    (t : ℝ) (j : MarkovChain.Identifiability.State) :
    HasDerivAt (fun u => extendPair (pairRow k c q u) j)
      ((extendPair (pairRow k c q t) ᵥ* MarkovChain.Identifiability.generator k (c t) (q t) 0) j)
          t := by
  rw [extendPair_vecMul]
  have hd (i : Fin 2) := inhomogeneousTransition_hasDerivAt_right
    (fun u => MarkovChain.Identifiability.pairGenerator k (c u) (q u))
        (pairGenerator_continuous k c q hc hq) 0 t 0 i
  by_cases h0 : j = 0
  · subst j
    simpa [extendPair, Pi.single_apply, pairRow, Matrix.mul_apply, Matrix.vecMul, dotProduct]
      using hd 0
  · by_cases h1 : j = 1
    · subst j
      simpa [extendPair, Pi.single_apply, pairRow, Matrix.mul_apply, Matrix.vecMul, dotProduct]
        using hd 1
    · simpa [extendPair, Pi.single_apply, h0, h1] using hasDerivAt_const t (0 : ℝ)

theorem preRow_zero_recombination (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (t : ℝ) :
    preRow k c q (fun _ => 0) t = extendPair (pairRow k c q t) := by
  let z := fun u => extendPair (pairRow k c q u)
  have hz : ∀ u j, HasDerivAt (fun s => z s j)
      ((z u ᵥ* (fun u => MarkovChain.Identifiability.generator k (c u) (q u) 0) u -
          (0 : MarkovChain.Identifiability.State → ℝ)) j) u := by
    intro u j
    simpa only [sub_zero] using extendPair_hasDerivAt k c q hc hq u j
  have h := finiteRow_projection_duhamel
      (fun u => MarkovChain.Identifiability.generator k (c u) (q u) 0)
    (preGenerator_continuous k c q (fun _ => 0) hc hq continuous_const) z (fun _ => 0)
    continuous_const hz t
  have h0 : z 0 = Pi.single 0 (1 : ℝ) := by
    simp [z, extendPair, pairRow, inhomogeneousTransition_self,
      pairGenerator_continuous k c q hc hq]
  simp only [Matrix.zero_vecMul, Pi.zero_apply, intervalIntegral.integral_zero] at h
  rw [h0] at h
  ext j
  have hj := congrFun h j
  simpa [z, preRow, Matrix.vecMul, dotProduct, Pi.single_apply] using hj.symm

end Rhone.Statistics.Identifiability.DelayedOnset
