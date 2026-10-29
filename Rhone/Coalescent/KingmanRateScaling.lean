/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.RateScale
public import Rhone.Coalescent.KingmanVariances

/-!
# Kingman genealogy moments at a supplied positive pair rate

Source: kingman1982, sec. 1, eq. (1.1)–(1.4), (1.7). -/

@[expose] public section
noncomputable section
open MeasureTheory

namespace Rhone.Coalescent
open MarkovChain

def blockChainAtRate (n : ℕ) (c : ℝ) (hc : 0 < c) := (blockChain n).scaled c hc
theorem blockChainAtRate_rate (n : ℕ) (c : ℝ) (hc : 0 < c) (k : Fin (n + 1)) :
    (blockChainAtRate n c hc).rate k = c * ((Nat.choose (k : ℕ) 2 : ℚ) : ℝ) := by
  rw [blockChainAtRate, RateChain.scaled_rate, blockChain_rate, coalRate_eq_choose]
def tmrcaAtRate (n : ℕ) (c : ℝ) (hc : 0 < c) :=
  (blockChainAtRate n c hc).timeBefore (coalesced n)
def treeLengthAtRate (n : ℕ) (c : ℝ) (hc : 0 < c) :=
  (blockChainAtRate n c hc).costBefore (coalesced n) (fun k => ((k : ℕ) : ℝ))

theorem tmrcaAtRate_eq (n : ℕ) (c : ℝ) (hc : 0 < c) (p) :
    tmrcaAtRate n c hc p = ENNReal.ofReal (1 / c) * tmrca n p :=
  (blockChain n).scaled_costBefore c hc (coalesced n) (fun _ => 1) p

theorem treeLengthAtRate_eq (n : ℕ) (c : ℝ) (hc : 0 < c) (p) :
    treeLengthAtRate n c hc p = ENNReal.ofReal (1 / c) * treeLength n p :=
  (blockChain n).scaled_costBefore c hc (coalesced n) (fun k => ((k : ℕ) : ℝ)) p

theorem lintegral_tmrcaAtRate (n : ℕ) (c : ℝ) (hc : 0 < c) :
    ∫⁻ p, tmrcaAtRate n c hc p ∂(blockChainAtRate n c hc).jumpHoldLaw (Fin.last n) =
      ENNReal.ofReal ((expTMRCA n : ℝ) / c) := by
  simp only [tmrcaAtRate_eq, blockChainAtRate, RateChain.scaled_jumpHoldLaw]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_lt_top.ne, lintegral_tmrca,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

theorem lintegral_treeLengthAtRate (n : ℕ) (c : ℝ) (hc : 0 < c) :
    ∫⁻ p, treeLengthAtRate n c hc p ∂(blockChainAtRate n c hc).jumpHoldLaw (Fin.last n) =
      ENNReal.ofReal ((expLength n : ℝ) / c) := by
  simp only [treeLengthAtRate_eq, blockChainAtRate, RateChain.scaled_jumpHoldLaw]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_lt_top.ne, lintegral_treeLength,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

theorem variance_tmrcaAtRate (n : ℕ) (c : ℝ) (hc : 0 < c) :
    ProbabilityTheory.variance (fun p => (tmrcaAtRate n c hc p).toReal)
      ((blockChainAtRate n c hc).jumpHoldLaw (Fin.last n)) = (varTMRCA n : ℝ) / c ^ 2 := by
  simp only [tmrcaAtRate_eq, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 / c),
    blockChainAtRate, RateChain.scaled_jumpHoldLaw]
  rw [ProbabilityTheory.variance_const_mul, variance_tmrca]
  ring

theorem variance_treeLengthAtRate (n : ℕ) (c : ℝ) (hc : 0 < c) :
    ProbabilityTheory.variance (fun p => (treeLengthAtRate n c hc p).toReal)
      ((blockChainAtRate n c hc).jumpHoldLaw (Fin.last n)) = (varLength n : ℝ) / c ^ 2 := by
  simp only [treeLengthAtRate_eq, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 / c),
    blockChainAtRate, RateChain.scaled_jumpHoldLaw]
  rw [ProbabilityTheory.variance_const_mul, variance_treeLength]
  ring

end Rhone.Coalescent
