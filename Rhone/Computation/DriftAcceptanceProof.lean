/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.DriftTrajectoryProof
public import Rhone.Computation.DriftCheckProof

/-! # Acceptance by the drift checkers against the trajectory law -/

@[expose] public section
namespace Rhone.Computation.Drift
open MeasureTheory

structure WfRequest where
  geneCopies : Nat
  initialCount : Nat
  steps : Nat

structure MoranRequest where
  geneCopies : Nat
  fitness : Rat
  initialCount : Nat
  steps : Nat

def WfRequest.valid (q : WfRequest) : Bool :=
  decide (1 ≤ q.geneCopies ∧ q.geneCopies ≤ 64 ∧ q.initialCount ≤ q.geneCopies ∧
    q.steps ≤ 256)

def MoranRequest.valid (q : MoranRequest) : Bool :=
  decide (1 ≤ q.geneCopies ∧ q.geneCopies ≤ 64 ∧ q.initialCount ≤ q.geneCopies ∧
    q.steps ≤ 256 ∧ 0 < q.fitness)

def WfRequest.check (q : WfRequest) (claim : Array Rat) : Bool :=
  checkWfReport q.geneCopies q.initialCount q.steps claim

def MoranRequest.check (q : MoranRequest) (claim : Array Rat) : Bool :=
  checkMoranReport q.geneCopies q.fitness q.initialCount q.steps claim

theorem WfRequest.valid_iff (q : WfRequest) :
    q.valid = true ↔ 1 ≤ q.geneCopies ∧ q.geneCopies ≤ 64 ∧
      q.initialCount ≤ q.geneCopies ∧ q.steps ≤ 256 := by
  simp [WfRequest.valid]

theorem MoranRequest.valid_iff (q : MoranRequest) :
    q.valid = true ↔ 1 ≤ q.geneCopies ∧ q.geneCopies ≤ 64 ∧
      q.initialCount ≤ q.geneCopies ∧ q.steps ≤ 256 ∧ 0 < q.fitness := by
  simp [MoranRequest.valid]

private theorem array_eq_of_getD {a b : Array Rat} (hs : a.size = b.size)
    (h : ∀ i, i < a.size → a.getD i 0 = b.getD i 0) : a = b := by
  apply Array.ext hs
  intro i h1 h2
  have := h i h1
  simpa [Array.getD, h1, h2] using this

private theorem wfReport_size (n i t : Nat) : (wfReportValues n i t).size = n + 3 := by
  simp [wfReportValues, wfTransition]

private theorem wfReport_getD_row (n i t j : Nat) (hj : j < n + 1) :
    (wfReportValues n i t).getD j 0 = wfRow n i j := by
  simp only [Array.getD, wfReportValues, wfTransition, List.append_toArray, List.size_toArray,
    List.length_append, List.length_map, List.length_range, List.length_cons, List.length_nil,
    zero_add, Nat.reduceAdd, Array.getInternal_eq_getElem, List.getElem_toArray, hj,
    List.getElem_append_left, List.getElem_map, List.getElem_range, dite_eq_ite, ite_eq_left_iff,
    not_lt]
  intro h
  omega

private theorem wfReport_getD_fix (n i t : Nat) :
    (wfReportValues n i t).getD (n + 1) 0 = neutralFixation n i := by
  simp [wfReportValues, wfTransition, Array.getD]

private theorem wfReport_getD_het (n i t : Nat) :
    (wfReportValues n i t).getD (n + 2) 0 = wfHeterozygosity n i t := by
  simp [wfReportValues, wfTransition, Array.getD]

private theorem moranReport_size (n : Nat) (r : Rat) (i t : Nat) :
    (moranReportValues n r i t).size = n + 2 + (if r = 1 then 1 else 0) := by
  by_cases hr : r = 1 <;> simp [moranReportValues, moranTransition, hr]

private theorem moranReport_getD_row (n : Nat) (r : Rat) (i t j : Nat) (hj : j < n + 1) :
    (moranReportValues n r i t).getD j 0 = moranRow n r i j := by
  have hj' : j < n + 1 + 1 := by omega
  have h3 : ¬ (n + 1 + 2 ≤ j) := by omega
  by_cases hr : r = 1 <;>
    simp [moranReportValues, moranTransition, Array.getD, hj, hj', hr, h3]

private theorem moranReport_getD_fix (n : Nat) (r : Rat) (i t : Nat) :
    (moranReportValues n r i t).getD (n + 1) 0 = moranFixation n r i := by
  by_cases hr : r = 1 <;>
    simp [moranReportValues, moranTransition, Array.getD, hr]

private theorem moranReport_getD_het (n i t : Nat) :
    (moranReportValues n 1 i t).getD (n + 2) 0 = moranHeterozygosity n i t := by
  simp [moranReportValues, moranTransition, Array.getD]

theorem WfRequest.check_sound (q : WfRequest) (claim : Array Rat)
    (hvalid : q.valid = true) (accepted : q.check claim = true)
    (x : Fin (q.geneCopies + 1)) (hx : (x : Nat) = q.initialCount) :
    claim.size = q.geneCopies + 3 ∧
    (∀ j : Fin (q.geneCopies + 1), (claim.getD j 0 : Real) =
      ((Rhone.MarkovChain.wfChain q.geneCopies).pathLaw x).real {ω | ω 1 = j}) ∧
    (claim.getD (q.geneCopies + 1) 0 : Real) =
      ((Rhone.MarkovChain.wfChain q.geneCopies).pathLaw x).real
        {ω | ∃ s, ω s = Fin.last q.geneCopies} ∧
    (claim.getD (q.geneCopies + 2) 0 : Real) =
      ∫ ω, Rhone.MarkovChain.het q.geneCopies (ω q.steps)
        ∂(Rhone.MarkovChain.wfChain q.geneCopies).pathLaw x := by
  obtain ⟨n, i, t⟩ := q
  obtain ⟨hn, -, -, -⟩ := (WfRequest.valid_iff _).mp hvalid
  dsimp only at hn x hx ⊢
  subst hx
  have h : claim = wfReportValues n x t := (checkWfReport_iff _ _ _ _).mp accepted
  subst h
  refine ⟨wfReport_size _ _ _, ?_, ?_, ?_⟩
  · intro j
    rw [wfReport_getD_row _ _ _ _ j.isLt, Rhone.MarkovChain.FinChain.pathLaw_real_eval,
      Rhone.MarkovChain.FinChain.stepN_one]
    exact wfChain_P_eq n x j
  · rw [wfReport_getD_fix]
    exact wf_fixation_real n hn x
  · rw [wfReport_getD_het]
    exact wf_heterozygosity_integral n t x

theorem WfRequest.check_complete (q : WfRequest) (claim : Array Rat)
    (hvalid : q.valid = true)
    (x : Fin (q.geneCopies + 1)) (hx : (x : Nat) = q.initialCount)
    (hsize : claim.size = q.geneCopies + 3)
    (hrow : ∀ j : Fin (q.geneCopies + 1), (claim.getD j 0 : Real) =
      ((Rhone.MarkovChain.wfChain q.geneCopies).pathLaw x).real {ω | ω 1 = j})
    (hfix : (claim.getD (q.geneCopies + 1) 0 : Real) =
      ((Rhone.MarkovChain.wfChain q.geneCopies).pathLaw x).real
        {ω | ∃ s, ω s = Fin.last q.geneCopies})
    (hhet : (claim.getD (q.geneCopies + 2) 0 : Real) =
      ∫ ω, Rhone.MarkovChain.het q.geneCopies (ω q.steps)
        ∂(Rhone.MarkovChain.wfChain q.geneCopies).pathLaw x) :
    q.check claim = true := by
  obtain ⟨vsize, vrow, vfix, vhet⟩ := WfRequest.check_sound q
    (wfReportValues q.geneCopies q.initialCount q.steps) hvalid
    (checkWfReport_complete _ _ _) x hx
  refine (checkWfReport_iff _ _ _ _).mpr (array_eq_of_getD (hsize.trans vsize.symm) ?_)
  intro k hk
  rw [hsize] at hk
  rcases Nat.lt_or_ge k (q.geneCopies + 1) with h | h
  · have := (hrow ⟨k, h⟩).trans (vrow ⟨k, h⟩).symm
    exact_mod_cast this
  · rcases (by omega : k = q.geneCopies + 1 ∨ k = q.geneCopies + 2) with rfl | rfl
    · have := hfix.trans vfix.symm
      exact_mod_cast this
    · have := hhet.trans vhet.symm
      exact_mod_cast this

private theorem moran_het_cast_one (n t : Nat) (x : Fin (n + 1)) (s : Real) (hs : 0 < s)
    (h1 : s = 1) :
    (moranHeterozygosity n x t : Real) =
      ∫ ω, Rhone.MarkovChain.het n (ω t) ∂(Rhone.MarkovChain.moranChain n s hs).pathLaw x := by
  subst h1
  exact moran_heterozygosity_integral n t x

theorem MoranRequest.check_sound (q : MoranRequest) (claim : Array Rat)
    (hvalid : q.valid = true) (accepted : q.check claim = true)
    (hr : 0 < (q.fitness : Real))
    (x : Fin (q.geneCopies + 1)) (hx : (x : Nat) = q.initialCount) :
    claim.size = q.geneCopies + 2 + (if q.fitness = 1 then 1 else 0) ∧
    (∀ j : Fin (q.geneCopies + 1), (claim.getD j 0 : Real) =
      ((Rhone.MarkovChain.moranChain q.geneCopies (q.fitness : Real) hr).pathLaw x).real
        {ω | ω 1 = j}) ∧
    (claim.getD (q.geneCopies + 1) 0 : Real) =
      ((Rhone.MarkovChain.moranChain q.geneCopies (q.fitness : Real) hr).pathLaw x).real
        {ω | ∃ s, ω s = Fin.last q.geneCopies} ∧
    (q.fitness = 1 → (claim.getD (q.geneCopies + 2) 0 : Real) =
      ∫ ω, Rhone.MarkovChain.het q.geneCopies (ω q.steps)
        ∂(Rhone.MarkovChain.moranChain q.geneCopies (q.fitness : Real) hr).pathLaw x) := by
  obtain ⟨n, r, i, t⟩ := q
  obtain ⟨hn, -, -, -, -⟩ := (MoranRequest.valid_iff _).mp hvalid
  dsimp only at hn hr x hx ⊢
  subst hx
  have h : claim = moranReportValues n r x t := (checkMoranReport_iff _ _ _ _ _).mp accepted
  subst h
  refine ⟨moranReport_size _ _ _ _, ?_, ?_, ?_⟩
  · intro j
    rw [moranReport_getD_row _ _ _ _ _ j.isLt, Rhone.MarkovChain.FinChain.pathLaw_real_eval,
      Rhone.MarkovChain.FinChain.stepN_one]
    exact moranChain_P_eq n r hr x j
  · rw [moranReport_getD_fix]
    exact moran_fixation_real n hn r hr x
  · intro h1
    subst h1
    rw [moranReport_getD_het]
    exact moran_het_cast_one n t x _ hr (by simp)

theorem MoranRequest.check_complete (q : MoranRequest) (claim : Array Rat)
    (hvalid : q.valid = true) (hr : 0 < (q.fitness : Real))
    (x : Fin (q.geneCopies + 1)) (hx : (x : Nat) = q.initialCount)
    (hsize : claim.size = q.geneCopies + 2 + (if q.fitness = 1 then 1 else 0))
    (hrow : ∀ j : Fin (q.geneCopies + 1), (claim.getD j 0 : Real) =
      ((Rhone.MarkovChain.moranChain q.geneCopies (q.fitness : Real) hr).pathLaw x).real
        {ω | ω 1 = j})
    (hfix : (claim.getD (q.geneCopies + 1) 0 : Real) =
      ((Rhone.MarkovChain.moranChain q.geneCopies (q.fitness : Real) hr).pathLaw x).real
        {ω | ∃ s, ω s = Fin.last q.geneCopies})
    (hhet : q.fitness = 1 → (claim.getD (q.geneCopies + 2) 0 : Real) =
      ∫ ω, Rhone.MarkovChain.het q.geneCopies (ω q.steps)
        ∂(Rhone.MarkovChain.moranChain q.geneCopies (q.fitness : Real) hr).pathLaw x) :
    q.check claim = true := by
  obtain ⟨vsize, vrow, vfix, vhet⟩ := MoranRequest.check_sound q
    (moranReportValues q.geneCopies q.fitness q.initialCount q.steps) hvalid
    (checkMoranReport_complete _ _ _ _) hr x hx
  refine (checkMoranReport_iff _ _ _ _ _).mpr
    (array_eq_of_getD (hsize.trans vsize.symm) ?_)
  intro k hk
  rw [hsize] at hk
  rcases Nat.lt_or_ge k (q.geneCopies + 1) with h | h
  · have := (hrow ⟨k, h⟩).trans (vrow ⟨k, h⟩).symm
    exact_mod_cast this
  · by_cases h1 : q.fitness = 1
    · simp only [h1, ↓reduceIte] at hk
      rcases (by omega : k = q.geneCopies + 1 ∨ k = q.geneCopies + 2) with rfl | rfl
      · have := hfix.trans vfix.symm
        exact_mod_cast this
      · have := (hhet h1).trans (vhet h1).symm
        exact_mod_cast this
    · simp only [h1, ↓reduceIte] at hk
      obtain rfl : k = q.geneCopies + 1 := by omega
      have := hfix.trans vfix.symm
      exact_mod_cast this

private theorem geometric_zero_succ (k : Nat) : geometric 0 (k + 1) = 1 := by
  induction k with
  | zero => simp [geometric]
  | succ k ih => rw [geometric, ih]; simp

theorem WfRequest.zero_copies (i t : Nat) :
    (⟨0, i, t⟩ : WfRequest).valid = false ∧ wfReportValues 0 i t = #[1, 0, 0] := by
  refine ⟨by simp [WfRequest.valid], ?_⟩
  simp [wfReportValues, wfTransition, wfRow, choose, factorial, neutralFixation,
    wfHeterozygosity, heterozygosity]

theorem WfRequest.count_above_size (n i t : Nat) (hn : 0 < n) (hi : n < i) :
    (⟨n, i, t⟩ : WfRequest).valid = false ∧
      1 < (wfReportValues n i t).getD (n + 1) 0 := by
  refine ⟨?_, ?_⟩
  · simp only [WfRequest.valid, decide_eq_false_iff_not]
    omega
  · rw [wfReport_getD_fix, neutralFixation]
    have hn' : (0 : Rat) < n := by exact_mod_cast hn
    rw [lt_div_iff₀ hn', one_mul]
    exact_mod_cast hi

theorem MoranRequest.zero_fitness (n i t : Nat) (hn : 1 ≤ n) (hi : 1 ≤ i) :
    (⟨n, 0, i, t⟩ : MoranRequest).valid = false ∧
      (moranReportValues n 0 i t).getD (n + 1) 0 = 1 := by
  refine ⟨by simp [MoranRequest.valid], ?_⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  rw [moranReport_getD_fix, moranFixation]
  simp [geometric_zero_succ]

end Rhone.Computation.Drift
