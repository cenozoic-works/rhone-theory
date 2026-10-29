/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.SmcPrimeTvProof
public import Rhone.Computation.SmcPrimeTvCheck
public import Rhone.Coalescent.SmcPrimeTVBound

/-! # Exact rational bounds reach the full-ARG and SMC′ genealogy measure laws -/

@[expose] public section
namespace Rhone.Computation.SmcPrimeTv
open Coalescent.IntervalProcess MarkovChain Probability

theorem fullARG_smcPrime_tv_bound (N : Nat) (hN : 1 ≤ N)
    (R : Rat) (hR : 0 ≤ R) :
    eventTV (fullARGGenealogyLaw N (R : Real)) (smcPrimeGenealogyLaw N (R : Real)) ≤
      ENNReal.ofReal (doubleBound R (N - 1) : Real) ∧
    (doubleBound R (N - 1) : Real) ≤ (clippedQuadraticBound R (N - 1) : Real) := by
  have h := Coalescent.SmcPrime.fullARG_smcPrime_tv_bound
    N hN (R : Real) (by exact_mod_cast hR)
  simpa only [doubleBound_cast, clippedQuadraticBound_cast] using h

theorem fullARG_smcPrime_tv_quadratic (N : Nat) (hN : 1 ≤ N)
    (R : Rat) (hR : 0 ≤ R) :
    eventTV (fullARGGenealogyLaw N (R : Real)) (smcPrimeGenealogyLaw N (R : Real)) ≤
      ENNReal.ofReal (clippedQuadraticBound R (N - 1) : Real) := by
  have h := Coalescent.SmcPrime.fullARG_smcPrime_tv_quadratic
    N hN (R : Real) (by exact_mod_cast hR)
  simpa only [clippedQuadraticBound_cast] using h

theorem checkReport_sound (N : Nat) (R : Rat) (claim : Array Rat)
    (accepted : checkReport N R claim = true) :
    claim = reportValues N R ∧
    eventTV (fullARGGenealogyLaw N (R : Real)) (smcPrimeGenealogyLaw N (R : Real)) ≤
      ENNReal.ofReal (claim.getD 0 0 : Real) ∧
    (claim.getD 0 0 : Real) ≤ (claim.getD 3 0 : Real) := by
  obtain ⟨hN, hR, hclaim⟩ := (checkReport_iff N R claim).mp accepted
  refine ⟨hclaim, ?_⟩
  rw [hclaim]
  simpa [reportValues] using fullARG_smcPrime_tv_bound N hN R hR

end Rhone.Computation.SmcPrimeTv
