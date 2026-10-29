/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.MarkedLaw

/-! # A normalized two-locus event law -/

@[expose] public section

open scoped Matrix Matrix.Norms.Operator Topology ENNReal
open Filter Set MeasureTheory
namespace Rhone.Statistics.Identifiability

theorem pair_firstExitLaw_probability (k : Nat) {c q : ℝ}
    (hc : 0 < c) (hq : 0 < q) (i : Fin 2) :
    IsProbabilityMeasure (firstExitLaw (MarkovChain.Identifiability.pairGenerator k c q) i) := by
  apply firstExitLaw_probability _ (pairGenerator_metzler k hq.le) _ i
    (pair_survival_tendsto_zero k hc hq i)
  intro j
  fin_cases j
  · simpa [MarkovChain.Identifiability.pairGenerator, MarkovChain.Identifiability.totalMigration,
      Fin.sum_univ_succ] using hc.le
  · simp [MarkovChain.Identifiability.pairGenerator, Fin.sum_univ_succ]

def postPairState (m : Fin 5) : Fin 2 := if m = 1 ∨ m = 3 then 0 else 1

noncomputable def lagLaw (k : Nat) (c q : ℝ) (m : Fin 5) : Measure ℝ :=
  if m = 0 then Measure.dirac 0 else firstExitLaw (MarkovChain.Identifiability.pairGenerator k c q)
      (postPairState m)

theorem lagLaw_probability (k : Nat) {c q : ℝ}
    (hc : 0 < c) (hq : 0 < q) (m : Fin 5) : IsProbabilityMeasure (lagLaw k c q m) := by
  unfold lagLaw
  split
  · infer_instance
  · exact pair_firstExitLaw_probability k hc hq _

def recoverTimes (m : Fin 5) (p : ℝ × ℝ) : ℝ × ℝ :=
  if m = 0 then (p.1, p.1) else
  if m = 1 ∨ m = 2 then (p.1, p.1 + p.2) else (p.1 + p.2, p.1)

theorem recoverTimes_continuous (m : Fin 5) : Continuous (recoverTimes m) := by
  unfold recoverTimes
  split
  · exact continuous_fst.prodMk continuous_fst
  · split
    · exact continuous_fst.prodMk (continuous_fst.add continuous_snd)
    · exact (continuous_fst.add continuous_snd).prodMk continuous_fst

noncomputable def jointLaw (k : Nat) (c q r : ℝ) : Measure (ℝ × ℝ) :=
  Measure.sum (fun m : Fin 5 =>
    ((markLaw k c q r m).prod (lagLaw k c q m)).map (recoverTimes m))

theorem jointLaw_probability (k : Nat) {c q r : ℝ}
    (hc : 0 < c) (hq : 0 < q) (hr : 0 ≤ r) : IsProbabilityMeasure (jointLaw k c q r) := by
  constructor
  rw [jointLaw, Measure.sum_apply _ MeasurableSet.univ]
  calc
    (∑' m : Fin 5, (((markLaw k c q r m).prod (lagLaw k c q m)).map
      (recoverTimes m)) univ) = ∑' m : Fin 5, markLaw k c q r m univ := by
        apply tsum_congr
        intro m
        have := lagLaw_probability k hc hq m
        rw [Measure.map_apply (recoverTimes_continuous m).measurable MeasurableSet.univ,
          preimage_univ, ← univ_prod_univ, Measure.prod_prod,
          measure_univ (μ := lagLaw k c q m), mul_one]
    _ = 1 := markLaw_total_mass k hc hq hr

end Rhone.Statistics.Identifiability
