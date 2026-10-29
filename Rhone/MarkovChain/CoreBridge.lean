/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.Absorption
public import Rhone.MarkovChain.Moran

/-! # Count kernels as finite Markov chains: fixation boundary and Wright–Fisher chain -/

@[expose] public section

namespace Rhone.MarkovChain

open Finset

variable {N : ℕ}

namespace CountKernel

def toFinChain (P : CountKernel N) (hP : P.IsStochastic) : FinChain (Fin (N + 1)) where
  P := P
  nonneg := hP.1
  row_sum := hP.2

variable (P : CountKernel N) (hP : P.IsStochastic)

theorem toFinChain_P : (P.toFinChain hP).P = P := rfl

theorem toFinChain_expect (f : Fin (N + 1) → ℝ) : (P.toFinChain hP).expect f = P.expect f :=
  rfl

theorem toFinChain_expectN (n : ℕ) (f : Fin (N + 1) → ℝ) :
    (P.toFinChain hP).expectN n f = P.expectIter n f := by
  induction n with
  | zero =>
    funext i
    simp [FinChain.expectN_apply, FinChain.stepN_zero, Matrix.one_apply, expectIter]
  | succ n ih => rw [FinChain.expectN_succ, ih, toFinChain_expect, expectIter]

theorem toFinChain_isHarmonic (h : Fin (N + 1) → ℝ) :
    (P.toFinChain hP).IsHarmonic h ↔ P.IsHarmonic h :=
  funext_iff

end CountKernel

def fixationBoundary (N : ℕ) : Finset (Fin (N + 1)) := {0, Fin.last N}

theorem mem_fixationBoundary {i : Fin (N + 1)} :
    i ∈ fixationBoundary N ↔ i = 0 ∨ i = Fin.last N := by
  simp [fixationBoundary]

theorem pos_and_lt_of_notMem_fixationBoundary {i : Fin (N + 1)} (hi : i ∉ fixationBoundary N) :
    0 < (i : ℕ) ∧ (i : ℕ) < N := by
  rw [mem_fixationBoundary, not_or] at hi
  refine ⟨Nat.pos_of_ne_zero fun h => hi.1 (Fin.ext h), lt_of_le_of_ne (Fin.is_le i) fun h => ?_⟩
  exact hi.2 (Fin.ext h)

noncomputable def wfChain (N : ℕ) : FinChain (Fin (N + 1)) :=
  (wf N).toFinChain (wf_isStochastic N)

theorem wfChain_isAbsorbing_zero (N : ℕ) : (wfChain N).IsAbsorbing 0 := by
  change wf N 0 0 = 1
  simp [wf_apply, wfRow, binomRow]

theorem wfChain_isAbsorbing_last (hN : 0 < N) : (wfChain N).IsAbsorbing (Fin.last N) := by
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  change wf N (Fin.last N) (Fin.last N) = 1
  simp [wf_apply, wfRow, binomRow, div_self hNr]

theorem wfChain_isAbsorbingSet (hN : 0 < N) :
    (wfChain N).IsAbsorbingSet (fixationBoundary N) := by
  intro a ha
  rcases mem_fixationBoundary.1 ha with rfl | rfl
  · exact wfChain_isAbsorbing_zero N
  · exact wfChain_isAbsorbing_last hN

theorem wfChain_P_zero_pos {i : Fin (N + 1)} (hi : (i : ℕ) < N) : 0 < (wfChain N).P i 0 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) hi)
  have hlt : (i : ℝ) / N < 1 := by
    rw [div_lt_one hN]
    exact_mod_cast hi
  change 0 < wf N i 0
  simp only [wf_apply, wfRow, binomRow, Fin.val_zero, Nat.choose_zero_right, Nat.cast_one,
    pow_zero, one_mul, Nat.sub_zero]
  exact pow_pos (sub_pos.2 hlt) _

theorem wfChain_reaches (N : ℕ) : (wfChain N).Reaches (fixationBoundary N) :=
  FinChain.reaches_of_rank _ _ (fun i => (i : ℕ)) fun _ hi =>
    ⟨0, wfChain_P_zero_pos (pos_and_lt_of_notMem_fixationBoundary hi).2,
      (pos_and_lt_of_notMem_fixationBoundary hi).1⟩

noncomputable def moranChain (N : ℕ) (r : ℝ) (hr : 0 < r) : FinChain (Fin (N + 1)) :=
  (moran N r).toFinChain (moran_isStochastic hr N)

variable {r : ℝ}

theorem moranChain_isAbsorbing_zero (N : ℕ) (hr : 0 < r) :
    (moranChain N r hr).IsAbsorbing 0 := by
  change moran N r 0 0 = 1
  simp [moran_apply, moranRow, moranUp_zero, moranDown_zero]

theorem moranChain_isAbsorbing_last (N : ℕ) (hr : 0 < r) :
    (moranChain N r hr).IsAbsorbing (Fin.last N) := by
  change moran N r (Fin.last N) (Fin.last N) = 1
  simp [moran_apply, moranRow, moranUp_self, moranDown_self]

theorem moranChain_isAbsorbingSet (N : ℕ) (hr : 0 < r) :
    (moranChain N r hr).IsAbsorbingSet (fixationBoundary N) := by
  intro a ha
  rcases mem_fixationBoundary.1 ha with rfl | rfl
  · exact moranChain_isAbsorbing_zero N hr
  · exact moranChain_isAbsorbing_last N hr

theorem moranChain_reaches (N : ℕ) (hr : 0 < r) :
    (moranChain N r hr).Reaches (fixationBoundary N) := by
  refine FinChain.reaches_of_rank _ _ (fun i => (i : ℕ)) fun i hi => ?_
  obtain ⟨hpos, hlt⟩ := pos_and_lt_of_notMem_fixationBoundary hi
  have hjlt : (i : ℕ) - 1 < N + 1 := by omega
  refine ⟨⟨(i : ℕ) - 1, hjlt⟩, ?_, by simp only; omega⟩
  have hi1 : (i : ℕ) = (i : ℕ) - 1 + 1 := by omega
  have hne1 : (i : ℕ) - 1 ≠ (i : ℕ) := by omega
  have hne2 : (i : ℕ) - 1 ≠ (i : ℕ) + 1 := by omega
  have hiR : (0 : ℝ) < (i : ℕ) := by exact_mod_cast hpos
  have hNi : (0 : ℝ) < (N : ℝ) - (i : ℕ) := by
    have : ((i : ℕ) : ℝ) < N := by exact_mod_cast hlt
    linarith
  have hNR : (0 : ℝ) < N := by exact_mod_cast (lt_trans hpos hlt)
  change 0 < moranRow N r (i : ℕ) ((i : ℕ) - 1)
  rw [moranRow, ite_eq_right hne1, ite_eq_right hne2, ite_eq_left hi1, zero_add, zero_add,
    moranDown]
  positivity

end Rhone.MarkovChain
