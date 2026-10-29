/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.FirstExit
public import Rhone.Statistics.Identifiability.IntervalRank

/-! # Backward-transported first-A flux and its first two derivatives -/

@[expose] public section

open scoped Matrix Matrix.Norms.Operator
open Finset
namespace Rhone.Statistics.Identifiability

noncomputable def transferJet (k : Nat) (c q r : ℝ) (a : Nat) (j : Fin 2) (s : ℝ) : ℝ :=
  flowOutput (MarkovChain.Identifiability.generator k c q r) 0 (fun i => firstAKernel c i j) a s

noncomputable def pairEntryJet (k : Nat) (c q : ℝ) (a : Nat) (i j : Fin 2) (s : ℝ) : ℝ :=
  flowOutput (MarkovChain.Identifiability.pairGenerator k c q) i (Pi.single j 1) a s

noncomputable def backwardFlux (k : Nat) (c q r : ℝ) (j : Fin 2) (s : ℝ) : ℝ :=
  ∑ i : Fin 2, transferJet k c q r 0 i s * pairEntryJet k c q 0 i j (-s)

noncomputable def backwardFluxD (k : Nat) (c q r : ℝ) (j : Fin 2) (s : ℝ) : ℝ :=
  ∑ i : Fin 2, (transferJet k c q r 1 i s * pairEntryJet k c q 0 i j (-s) -
    transferJet k c q r 0 i s * pairEntryJet k c q 1 i j (-s))

noncomputable def backwardFluxDD (k : Nat) (c q r : ℝ) (j : Fin 2) (s : ℝ) : ℝ :=
  ∑ i : Fin 2, (transferJet k c q r 2 i s * pairEntryJet k c q 0 i j (-s) -
    2 * transferJet k c q r 1 i s * pairEntryJet k c q 1 i j (-s) +
    transferJet k c q r 0 i s * pairEntryJet k c q 2 i j (-s))

set_option backward.isDefEq.respectTransparency false in
theorem pairEntryJet_neg_deriv (k : Nat) (c q : ℝ) (a : Nat) (i j : Fin 2) (s : ℝ) :
    HasDerivAt (fun x => pairEntryJet k c q a i j (-x))
      (-pairEntryJet k c q (a+1) i j (-s)) s := by
  convert! (flowOutput_hasDerivAt (MarkovChain.Identifiability.pairGenerator k c q) i
      (Pi.single j 1) a (-s)).comp s
    (hasDerivAt_neg s) using 1
  simp [pairEntryJet]

set_option backward.isDefEq.respectTransparency false in
theorem backwardFlux_hasDerivAt (k : Nat) (c q r : ℝ) (j : Fin 2) (s : ℝ) :
    HasDerivAt (backwardFlux k c q r j) (backwardFluxD k c q r j s) s := by
  have h := HasDerivAt.sum (u := Finset.univ) (fun i (_ : i ∈ Finset.univ) =>
    (flowOutput_hasDerivAt (MarkovChain.Identifiability.generator k c q r) 0
        (fun z => firstAKernel c z i) 0 s).mul
      (pairEntryJet_neg_deriv k c q 0 i j s))
  convert! h using 1
  unfold backwardFluxD
  apply Finset.sum_congr rfl
  intro i _
  dsimp [transferJet]
  ring

set_option backward.isDefEq.respectTransparency false in
theorem backwardFluxD_hasDerivAt (k : Nat) (c q r : ℝ) (j : Fin 2) (s : ℝ) :
    HasDerivAt (backwardFluxD k c q r j) (backwardFluxDD k c q r j s) s := by
  have h := HasDerivAt.sum (u := Finset.univ) (fun i (_ : i ∈ Finset.univ) =>
    ((flowOutput_hasDerivAt (MarkovChain.Identifiability.generator k c q r) 0
        (fun z => firstAKernel c z i) 1 s).mul
      (pairEntryJet_neg_deriv k c q 0 i j s)).sub
    ((flowOutput_hasDerivAt (MarkovChain.Identifiability.generator k c q r) 0
        (fun z => firstAKernel c z i) 0 s).mul
      (pairEntryJet_neg_deriv k c q 1 i j s)))
  convert! h using 1
  unfold backwardFluxDD
  apply Finset.sum_congr rfl
  intro i _
  dsimp [transferJet]
  ring

theorem transferJet_same_mul_c (k : Nat) (c q r : ℝ) (a : Nat) (s : ℝ) :
    c * transferJet k c q r a 0 s = postBJet k c q r a s := by
  simp only [transferJet, postBJet, flowOutput, firstAKernel, ↓reduceIte,
    MarkovChain.Identifiability.nextB, Matrix.mulVec, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem transferJet_total (k : Nat) (c q r : ℝ) (a : Nat) (s : ℝ) :
    transferJet k c q r a 0 s + transferJet k c q r a 1 s = firstAJet k c q r a s := by
  simp only [transferJet, firstAJet, flowOutput, Matrix.mulVec, dotProduct]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change _ * (c * (MarkovChain.Identifiability.firstAThenBTable i : ℝ)) +
    _ * (c * ((MarkovChain.Identifiability.firstATable i : ℝ) -
        (MarkovChain.Identifiability.firstAThenBTable i : ℝ))) = _ *
        (c * (MarkovChain.Identifiability.firstATable i : ℝ))
  ring

@[simp] theorem transferJet_initial (k : Nat) (c q r : ℝ) (j : Fin 2) :
    transferJet k c q r 0 j 0 = 0 := by
  simp [transferJet, firstAKernel, MarkovChain.Identifiability.firstATable,
      MarkovChain.Identifiability.firstAThenBTable]

theorem transferJet_one_initial (k : Nat) (c q r : ℝ) (j : Fin 2) :
    transferJet k c q r 1 j 0 = if j = 0 then 2*r*c else 0 := by
  simp only [transferJet, flowOutput_zero, pow_one, MarkovChain.Identifiability.row_zero]
  fin_cases j <;> simp
      [firstAKernel, MarkovChain.Identifiability.firstATable,
      MarkovChain.Identifiability.firstAThenBTable]

theorem transferJet_two_same (k : Nat) {c q r : ℝ} (hc : c ≠ 0) :
    transferJet k c q r 2 0 0 = -2*r*c*(4*c+5*MarkovChain.Identifiability.totalMigration k q+2*r) :=
        by
  apply mul_left_cancel₀ hc
  rw [transferJet_same_mul_c]
  simp only [postBJet, flowOutput_zero, MarkovChain.Identifiability.nextB_jet_two]
  ring

theorem transferJet_two_apart (k : Nat) {c q r : ℝ} (hc : c ≠ 0) :
    transferJet k c q r 2 1 0 = 2*r*c*MarkovChain.Identifiability.totalMigration k q := by
  have h := transferJet_total k c q r 2 0
  rw [transferJet_two_same k hc] at h
  simp only [firstAJet, flowOutput_zero, MarkovChain.Identifiability.firstA_jet_two] at h
  linarith

@[simp] theorem backwardFlux_zero (k : Nat) (c q r : ℝ) (j : Fin 2) :
    backwardFlux k c q r j 0 = 0 := by simp [backwardFlux]

theorem backwardFluxD_zero (k : Nat) (c q r : ℝ) (j : Fin 2) :
    backwardFluxD k c q r j 0 = if j = 0 then 2*r*c else 0 := by
  fin_cases j <;> simp [backwardFluxD, transferJet_one_initial, pairEntryJet,
    flowOutput, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem backwardFluxDD_apart_zero (k : Nat) {c q r : ℝ} (hc : c ≠ 0) :
    backwardFluxDD k c q r 1 0 = -6*r*c*MarkovChain.Identifiability.totalMigration k q := by
  simp only [backwardFluxDD, neg_zero, transferJet_initial, zero_mul, add_zero,
    pairEntryJet, flowOutput_zero, pow_zero, pow_one]
  simp [transferJet_one_initial, transferJet_two_same k hc,
    transferJet_two_apart k hc, Fin.sum_univ_succ,
    Matrix.mulVec, dotProduct, MarkovChain.Identifiability.pairGenerator]
  ring

end Rhone.Statistics.Identifiability
