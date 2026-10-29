/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Computation.KingmanRateProof
public import Rhone.Coalescent.KingmanRateScaling

/-!
# Accepted genealogy reports equal the supplied-rate law's moments

Source: kingman1982, sec. 1, eq. (1.1)–(1.4), (1.7). -/

@[expose] public section
noncomputable section
open MeasureTheory

namespace Rhone.Computation.KingmanRate
open Lean KingmanWire Coalescent Rhone.Combinatorics MarkovChain Statistics
theorem requestAst_accept_supplied_rate_law (doc : Json) (count : Nat)
    (haccept : requestAst doc = .ok (stamp (true, count))) :
    ∃ (r : Request) (hc : 0 < (r.pairRate : ℝ)), decode doc = .ok r ∧ valid r = true ∧
      (∫⁻ p, tmrcaAtRate r.geneCopies r.pairRate hc p
        ∂(blockChainAtRate r.geneCopies r.pairRate hc).jumpHoldLaw (Fin.last r.geneCopies)) =
          ENNReal.ofReal (r.meanTmrca : ℝ) ∧
      ProbabilityTheory.variance (fun p => (tmrcaAtRate r.geneCopies r.pairRate hc p).toReal)
        ((blockChainAtRate r.geneCopies r.pairRate hc).jumpHoldLaw (Fin.last r.geneCopies)) =
          (r.varianceTmrca : ℝ) ∧
      (∫⁻ p, treeLengthAtRate r.geneCopies r.pairRate hc p
        ∂(blockChainAtRate r.geneCopies r.pairRate hc).jumpHoldLaw (Fin.last r.geneCopies)) =
          ENNReal.ofReal (r.meanTotalBranchLength : ℝ) ∧
      ProbabilityTheory.variance (fun p => (treeLengthAtRate r.geneCopies r.pairRate hc p).toReal)
        ((blockChainAtRate r.geneCopies r.pairRate hc).jumpHoldLaw (Fin.last r.geneCopies)) =
          (r.varianceTotalBranchLength : ℝ) := by
  obtain ⟨r, hdecode, hvalid, hc, h1, h2, h3, h4⟩ := requestAst_accept_law doc count haccept
  have hcr : 0 < (r.pairRate : ℝ) := by exact_mod_cast hc
  refine ⟨r, hcr, hdecode, hvalid, ?_, ?_, ?_, ?_⟩
  · simp only [tmrcaAtRate_eq, blockChainAtRate, RateChain.scaled_jumpHoldLaw]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_lt_top.ne, h1,
      ← ENNReal.ofReal_mul (by positivity), Rat.cast_mul]
    congr 1
    field_simp
  · simp only [tmrcaAtRate_eq, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 / (r.pairRate : ℝ)), blockChainAtRate,
      RateChain.scaled_jumpHoldLaw]
    rw [ProbabilityTheory.variance_const_mul, h2, Rat.cast_mul, Rat.cast_pow]
    field_simp
  · simp only [treeLengthAtRate_eq, blockChainAtRate, RateChain.scaled_jumpHoldLaw]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_lt_top.ne, h3,
      ← ENNReal.ofReal_mul (by positivity), Rat.cast_mul]
    congr 1
    field_simp
  · simp only [treeLengthAtRate_eq, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 / (r.pairRate : ℝ)), blockChainAtRate,
      RateChain.scaled_jumpHoldLaw]
    rw [ProbabilityTheory.variance_const_mul, h4, Rat.cast_mul, Rat.cast_pow]
    field_simp
end Rhone.Computation.KingmanRate
