/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.CommonClockIslandPhase
public import Rhone.Statistics.Identifiability.TimeVaryingARGSymmetry
public import Rhone.Statistics.Identifiability.UpperBranch

/-! # Locus-exchange symmetry of mark fluxes in the common-clock island model -/

@[expose] public section

open scoped Matrix Matrix.Norms.Operator
namespace Rhone.Statistics.Identifiability

theorem commonClock_exp_locusExchange (k : ℕ) (c q r s : ℝ)
    (i j : MarkovChain.Identifiability.State) :
    NormedSpace.exp (s • MarkovChain.Identifiability.generator k c q r) (locusExchangeState i)
      (locusExchangeState j) = NormedSpace.exp (s • MarkovChain.Identifiability.generator k c q r) i
          j := by
  let e := Matrix.reindexAlgEquiv ℝ ℝ locusExchangeEquiv
  have he : Continuous e := by
    exact continuous_id.matrix_reindex locusExchangeEquiv locusExchangeEquiv
  have hQ : e (s • MarkovChain.Identifiability.generator k c q r) = s •
      MarkovChain.Identifiability.generator k c q r := by
    ext a b
    change s * MarkovChain.Identifiability.generator k c q r (locusExchangeState a)
        (locusExchangeState b) = _
    rw [generator_locusExchange]
    rfl
  have h := NormedSpace.map_exp e he (s • MarkovChain.Identifiability.generator k c q r)
  rw [hQ] at h
  exact congrArg (fun M : Matrix MarkovChain.Identifiability.State MarkovChain.Identifiability.State
      ℝ => M i j) h

theorem commonClock_exp_row_locusExchange (k : ℕ) (c q r s : ℝ)
    (i : MarkovChain.Identifiability.State) :
    NormedSpace.exp (s • MarkovChain.Identifiability.generator k c q r) 0 (locusExchangeState i) =
      NormedSpace.exp (s • MarkovChain.Identifiability.generator k c q r) 0 i := by
  simpa using commonClock_exp_locusExchange k c q r s 0 i

theorem commonClock_markFlux_same (k : ℕ) (c q r s : ℝ) :
    markFlux k c q r 1 s = markFlux k c q r 3 s := by
  simp only [markFlux, flowOutput, pow_zero, Matrix.one_mul, Matrix.mulVec, dotProduct]
  rw [← locusExchangeEquiv.sum_comp (fun i =>
    NormedSpace.exp (s • MarkovChain.Identifiability.generator k c q r) 0 i * markRates c i 1)]
  apply Finset.sum_congr rfl
  intro i _
  change NormedSpace.exp (s • MarkovChain.Identifiability.generator k c q r) 0
      (locusExchangeState i) *
    (c * (markCount (locusExchangeState i) 1 : ℝ)) = _
  rw [commonClock_exp_row_locusExchange, (locusExchangeState_markCounts i).1]
  rfl

theorem commonClock_markFlux_apart (k : ℕ) (c q r s : ℝ) :
    markFlux k c q r 2 s = markFlux k c q r 4 s := by
  simp only [markFlux, flowOutput, pow_zero, Matrix.one_mul, Matrix.mulVec, dotProduct]
  rw [← locusExchangeEquiv.sum_comp (fun i =>
    NormedSpace.exp (s • MarkovChain.Identifiability.generator k c q r) 0 i * markRates c i 2)]
  apply Finset.sum_congr rfl
  intro i _
  change NormedSpace.exp (s • MarkovChain.Identifiability.generator k c q r) 0
      (locusExchangeState i) *
    (c * (markCount (locusExchangeState i) 2 : ℝ)) = _
  rw [commonClock_exp_row_locusExchange, (locusExchangeState_markCounts i).2]
  rfl

theorem markFlux1_eq3 (k : ℕ) (c q r s : ℝ) :
    markFlux k c q r 1 s = markFlux k c q r 3 s :=
  commonClock_markFlux_same k c q r s

theorem markFlux2_eq4 (k : ℕ) (c q r s : ℝ) :
    markFlux k c q r 2 s = markFlux k c q r 4 s :=
  commonClock_markFlux_apart k c q r s

theorem commonClock_markFlux_sum (k : ℕ) (c q r s : ℝ) (m : Fin 5) :
    (∑ i, NormedSpace.exp (s • MarkovChain.Identifiability.generator k c q r) 0 i * markRates c i
        m) =
      markFlux k c q r m s := by
  simp only [markFlux, flowOutput, pow_zero, Matrix.one_mul, Matrix.mulVec, dotProduct]

theorem commonClock_firstRate_same (k : ℕ) (c q r s : ℝ) :
    (∑ i, NormedSpace.exp (s • MarkovChain.Identifiability.generator k c q r) 0 i *
        commonClockFirstRate c i 0) =
      2 * markFlux k c q r 1 s := by
  simp only [commonClockFirstRate, ↓reduceIte, mul_add, Finset.sum_add_distrib]
  rw [commonClock_markFlux_sum, commonClock_markFlux_sum]
  rw [← commonClock_markFlux_same]
  ring

theorem commonClock_firstRate_apart (k : ℕ) (c q r s : ℝ) :
    (∑ i, NormedSpace.exp (s • MarkovChain.Identifiability.generator k c q r) 0 i *
        commonClockFirstRate c i 1) =
      2 * markFlux k c q r 2 s := by
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp only [commonClockFirstRate, h10, ↓reduceIte, mul_add, Finset.sum_add_distrib]
  rw [commonClock_markFlux_sum, commonClock_markFlux_sum]
  rw [← commonClock_markFlux_apart]
  ring

theorem commonClock_firstRate_upperDensity (k : ℕ) (c q r s t : ℝ) :
    ((NormedSpace.exp (s • MarkovChain.Identifiability.generator k c q r) * commonClockFirstRate c)
        *ᵥ
      (NormedSpace.exp ((2 * (t-s)) • MarkovChain.Identifiability.pairGenerator k c q) *ᵥ
          MarkovChain.Identifiability.pairDensity c)) 0 =
        2 * upperDensity k c q r s (2*t-s) := by
  rw [upperDensity_markFlux]
  have ht : (2*t-s)-s = 2*(t-s) := by ring
  rw [ht]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.mul_apply]
  rw [commonClock_firstRate_same, commonClock_firstRate_apart]
  simp only [forwardDensity, flowOutput, pow_zero, Matrix.one_mul, Matrix.mulVec,
    dotProduct, Fin.sum_univ_two]
  ring

theorem commonClock_firstRate_upperDensity_nested (k : ℕ) (c q r s t : ℝ) :
    (NormedSpace.exp (s • MarkovChain.Identifiability.generator k c q r) *ᵥ
      (commonClockFirstRate c *ᵥ
        (NormedSpace.exp ((t-s) • ((2 : ℝ) • MarkovChain.Identifiability.pairGenerator k c q)) *ᵥ
            MarkovChain.Identifiability.pairDensity c))) 0 =
          2 * upperDensity k c q r s (2*t-s) := by
  rw [Matrix.mulVec_mulVec]
  have hscale : (t-s) • ((2 : ℝ) • MarkovChain.Identifiability.pairGenerator k c q) =
      (2*(t-s)) • MarkovChain.Identifiability.pairGenerator k c q := by
    rw [smul_smul, mul_comm]
  rw [hscale]
  exact commonClock_firstRate_upperDensity k c q r s t

end Rhone.Statistics.Identifiability
