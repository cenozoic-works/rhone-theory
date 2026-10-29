/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.Drift
public import Rhone.MarkovChain.CoreBridge
public import Rhone.MarkovChain.DriftHeterozygosity
public import Rhone.MarkovChain.FixationHarmonic

/-! # Exact executable drift formulas equal the existing specifications -/

@[expose] public section
namespace Rhone.Computation.Drift
open Finset

theorem factorial_eq (n : Nat) : factorial n = Nat.factorial n := by
  induction n with
  | zero => simp [factorial]
  | succ n ih => simp [factorial, Nat.factorial_succ, ih]

theorem choose_eq (n j : Nat) : choose n j = n.choose j := by
  by_cases hj : j ≤ n
  · simp only [choose, ite_eq_left hj, factorial_eq]
    exact (Nat.choose_eq_factorial_div_factorial hj).symm
  · simp [choose, hj, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hj)]

theorem wfRow_cast (n i j : Nat) :
    (wfRow n i j : Real) = Rhone.MarkovChain.wfRow n i j := by
  simp [wfRow, choose_eq, Rhone.MarkovChain.wfRow, Rhone.MarkovChain.binomRow]

theorem moranUp_cast (n : Nat) (r : Rat) (i : Nat) :
    (moranUp n r i : Real) = Rhone.MarkovChain.moranUp n (r : Real) i := by
  simp [moranUp, Rhone.MarkovChain.moranUp]

theorem moranDown_cast (n : Nat) (r : Rat) (i : Nat) :
    (moranDown n r i : Real) = Rhone.MarkovChain.moranDown n (r : Real) i := by
  simp [moranDown, Rhone.MarkovChain.moranDown]

private theorem rat_cast_ite (p : Prop) [Decidable p] (a b : Rat) :
    ((if p then a else b : Rat) : Real) = if p then (a : Real) else (b : Real) := by
  split_ifs <;> rfl

theorem moranRow_cast (n : Nat) (r : Rat) (i j : Nat) :
    (moranRow n r i j : Real) = Rhone.MarkovChain.moranRow n (r : Real) i j := by
  simp only [moranRow, Rhone.MarkovChain.moranRow, Rat.cast_add, rat_cast_ite,
    Rat.cast_sub, Rat.cast_one, Rat.cast_zero, moranUp_cast, moranDown_cast]

theorem wfChain_P_eq (n : Nat) (i j : Fin (n + 1)) :
    (wfRow n i j : Real) = (Rhone.MarkovChain.wfChain n).P i j :=
  wfRow_cast n i j

theorem moranChain_P_eq (n : Nat) (r : Rat) (hr : 0 < (r : Real))
    (i j : Fin (n + 1)) :
    (moranRow n r i j : Real) = (Rhone.MarkovChain.moranChain n (r : Real) hr).P i j :=
  moranRow_cast n r i j

theorem wfTransition_size (n i : Nat) : (wfTransition n i).size = n + 1 := by
  simp [wfTransition]

theorem moranTransition_size (n : Nat) (r : Rat) (i : Nat) :
    (moranTransition n r i).size = n + 1 := by simp [moranTransition]

theorem wfTransition_getD_eq (n : Nat) (i j : Fin (n + 1)) :
    ((wfTransition n i).getD j 0 : Real) = (Rhone.MarkovChain.wfChain n).P i j := by
  simp [wfTransition, Array.getD, j.isLt, List.getElem_toArray,
    List.getElem_map, List.getElem_range, wfChain_P_eq]

theorem moranTransition_getD_eq (n : Nat) (r : Rat) (hr : 0 < (r : Real))
    (i j : Fin (n + 1)) :
    ((moranTransition n r i).getD j 0 : Real) =
      (Rhone.MarkovChain.moranChain n (r : Real) hr).P i j := by
  simp [moranTransition, Array.getD, j.isLt, List.getElem_toArray,
    List.getElem_map, List.getElem_range, moranChain_P_eq n r hr]

theorem heterozygosity_cast (n i : Nat) :
    (heterozygosity n i : Real) = Rhone.MarkovChain.het n i := by
  simp [heterozygosity, Rhone.MarkovChain.het]

theorem wfHeterozygosity_cast (n t : Nat) (i : Fin (n + 1)) :
    (wfHeterozygosity n i t : Real) =
      (Rhone.MarkovChain.wf n).expectIter t (fun j => Rhone.MarkovChain.het n j) i := by
  rw [Rhone.MarkovChain.wf_expectIter_het]
  simp [wfHeterozygosity, heterozygosity_cast]

theorem moranHeterozygosity_cast (n t : Nat) (i : Fin (n + 1)) :
    (moranHeterozygosity n i t : Real) =
      (Rhone.MarkovChain.moran n 1).expectIter t (fun j => Rhone.MarkovChain.het n j) i := by
  rw [Rhone.MarkovChain.moran_expectIter_het]
  simp [moranHeterozygosity, heterozygosity_cast]

theorem neutralFixation_cast (n i : Nat) :
    (neutralFixation n i : Real) = (i : Real) / n := by simp [neutralFixation]

theorem geometric_cast (x : Rat) (n : Nat) :
    (geometric x n : Real) = ∑ k ∈ range n, (x : Real) ^ k := by
  induction n with
  | zero => simp [geometric]
  | succ n ih => simp [geometric, sum_range_succ, ih]

theorem moranFixation_cast (n : Nat) (r : Rat) (i : Nat) :
    (moranFixation n r i : Real) = Rhone.MarkovChain.moranFixProb n (r : Real) i := by
  simp [moranFixation, geometric_cast, Rhone.MarkovChain.moranFixProb, one_div]

end Rhone.Computation.Drift
