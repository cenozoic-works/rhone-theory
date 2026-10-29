/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.KingmanLawProof
public import Rhone.Computation.KingmanCheckProof

/-! # Acceptance by the Kingman moment checker against the jump-and-hold law -/

@[expose] public section
namespace Rhone.Computation.Kingman
open MeasureTheory Coalescent Rhone.Combinatorics MarkovChain Statistics

structure Request where
  geneCopies : Nat
  pairRate : Rat

def Request.valid (q : Request) : Bool :=
  decide (1 ≤ q.geneCopies ∧ q.geneCopies ≤ 4096 ∧ q.pairRate = 1)

def Request.check (q : Request) (claim : Array Rat) : Bool :=
  checkReport q.geneCopies claim

theorem Request.valid_iff (q : Request) :
    q.valid = true ↔ 1 ≤ q.geneCopies ∧ q.geneCopies ≤ 4096 ∧ q.pairRate = 1 := by
  simp [Request.valid]

private theorem array_eq_of_getD {a b : Array Rat} (hs : a.size = b.size)
    (h : ∀ i, i < a.size → a.getD i 0 = b.getD i 0) : a = b := by
  apply Array.ext hs
  intro i h1 h2
  have := h i h1
  simpa [Array.getD, h1, h2] using this

private theorem harmonic_nonneg (n : Nat) : 0 ≤ Sfs.harmonic n := by
  induction n with
  | zero => simp [Sfs.harmonic]
  | succ n ih =>
    rw [Sfs.harmonic]
    have : (0 : Rat) ≤ 1 / ((n + 1 : Nat) : Rat) := by positivity
    linarith

private theorem meanTmrca_nonneg (n : Nat) : 0 ≤ (moments n).meanTmrca := by
  by_cases hn : n = 0
  · simp [moments, hn]
  · have h1 : (1 : Rat) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have h2 : 1 / (n : Rat) ≤ 1 := by
      rw [div_le_one (by linarith)]
      exact h1
    simp only [moments, hn, ite_false]
    linarith

private theorem meanTotalBranchLength_nonneg (n : Nat) :
    0 ≤ (moments n).meanTotalBranchLength := by
  change 0 ≤ 2 * Sfs.harmonic (n - 1)
  have := harmonic_nonneg (n - 1)
  linarith

theorem Request.check_sound (q : Request) (claim : Array Rat)
    (accepted : q.check claim = true) :
    claim.size = 4 ∧
    0 ≤ (claim.getD 0 0 : Real) ∧
    (∫⁻ p, tmrca q.geneCopies p
        ∂(blockChain q.geneCopies).jumpHoldLaw (Fin.last q.geneCopies)) =
      ENNReal.ofReal (claim.getD 0 0 : Real) ∧
    ProbabilityTheory.variance (fun p => (tmrca q.geneCopies p).toReal)
        ((blockChain q.geneCopies).jumpHoldLaw (Fin.last q.geneCopies)) =
      (claim.getD 1 0 : Real) ∧
    0 ≤ (claim.getD 2 0 : Real) ∧
    (∫⁻ p, treeLength q.geneCopies p
        ∂(blockChain q.geneCopies).jumpHoldLaw (Fin.last q.geneCopies)) =
      ENNReal.ofReal (claim.getD 2 0 : Real) ∧
    ProbabilityTheory.variance (fun p => (treeLength q.geneCopies p).toReal)
        ((blockChain q.geneCopies).jumpHoldLaw (Fin.last q.geneCopies)) =
      (claim.getD 3 0 : Real) := by
  have h : claim = reportValues q.geneCopies := (checkReport_iff _ _).mp accepted
  subst h
  refine ⟨rfl, ?_, lintegral_tmrca_eq_compute _, variance_tmrca_eq_compute _, ?_,
    lintegral_treeLength_eq_compute _, variance_treeLength_eq_compute _⟩
  · exact_mod_cast meanTmrca_nonneg q.geneCopies
  · exact_mod_cast meanTotalBranchLength_nonneg q.geneCopies

theorem Request.check_complete (q : Request) (claim : Array Rat)
    (hsize : claim.size = 4)
    (h0 : 0 ≤ (claim.getD 0 0 : Real))
    (hmean : (∫⁻ p, tmrca q.geneCopies p
        ∂(blockChain q.geneCopies).jumpHoldLaw (Fin.last q.geneCopies)) =
      ENNReal.ofReal (claim.getD 0 0 : Real))
    (hvar : ProbabilityTheory.variance (fun p => (tmrca q.geneCopies p).toReal)
        ((blockChain q.geneCopies).jumpHoldLaw (Fin.last q.geneCopies)) =
      (claim.getD 1 0 : Real))
    (h2 : 0 ≤ (claim.getD 2 0 : Real))
    (hlength : (∫⁻ p, treeLength q.geneCopies p
        ∂(blockChain q.geneCopies).jumpHoldLaw (Fin.last q.geneCopies)) =
      ENNReal.ofReal (claim.getD 2 0 : Real))
    (hvarLength : ProbabilityTheory.variance (fun p => (treeLength q.geneCopies p).toReal)
        ((blockChain q.geneCopies).jumpHoldLaw (Fin.last q.geneCopies)) =
      (claim.getD 3 0 : Real)) :
    q.check claim = true := by
  obtain ⟨vsize, v0, vmean, vvar, v2, vlength, vvarLength⟩ :=
    Request.check_sound q (reportValues q.geneCopies) (checkReport_complete _)
  have e0 : claim.getD 0 0 = (reportValues q.geneCopies).getD 0 0 := by
    have := (ENNReal.ofReal_eq_ofReal_iff h0 v0).mp (hmean.symm.trans vmean)
    exact_mod_cast this
  have e1 : claim.getD 1 0 = (reportValues q.geneCopies).getD 1 0 := by
    have := hvar.symm.trans vvar
    exact_mod_cast this
  have e2 : claim.getD 2 0 = (reportValues q.geneCopies).getD 2 0 := by
    have := (ENNReal.ofReal_eq_ofReal_iff h2 v2).mp (hlength.symm.trans vlength)
    exact_mod_cast this
  have e3 : claim.getD 3 0 = (reportValues q.geneCopies).getD 3 0 := by
    have := hvarLength.symm.trans vvarLength
    exact_mod_cast this
  refine (checkReport_iff _ _).mpr (array_eq_of_getD (hsize.trans vsize.symm) ?_)
  intro i hi
  rw [hsize] at hi
  interval_cases i
  · exact e0
  · exact e1
  · exact e2
  · exact e3

theorem Request.zero_copies (r : Rat) :
    (⟨0, r⟩ : Request).valid = false ∧ reportValues 0 = #[0, 0, 0, 0] := by
  refine ⟨by simp [Request.valid], ?_⟩
  simp [reportValues, moments, varianceTime, Sfs.coefficients, Sfs.harmonic, Sfs.harmonic2]

theorem Request.pairRate_ignored (n : Nat) (r : Rat) (claim : Array Rat) :
    (⟨n, r⟩ : Request).check claim = (⟨n, 1⟩ : Request).check claim ∧
    (r ≠ 1 → (⟨n, r⟩ : Request).valid = false) := by
  refine ⟨rfl, fun hr => ?_⟩
  simp [Request.valid, hr]

end Rhone.Computation.Kingman
