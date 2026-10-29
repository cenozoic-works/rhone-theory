/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.FiniteIntervalMaterialKernel
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-! # Genealogy observations: ancestor labels at a genomic probe along an event path -/
@[expose] public section

namespace Rhone.Coalescent.IntervalProcess
open MeasureTheory
open scoped ENNReal NNReal

abbrev GenomicProbe := {q : ℚ // 0 ≤ q ∧ q < 1}

abbrev Genealogy (N : ℕ) := GenomicProbe → Fin N → Fin N → ℝ≥0∞

abbrev EventPath := ℕ → AugmentedState

def liveLabelAt (s : State) (i : ℕ) : ℕ :=
  if h : i < s.2.2.1 then (s.2.2.2 ⟨i, h⟩).1 else 0

noncomputable def ancestorStep (s : State) (e : Event)
    (q : GenomicProbe) (a : ℕ) : ℕ :=
  match e with
  | .inl _ => a
  | .inr (.inl ij) =>
      if ij.1 < ij.2 ∧ ij.2 < s.2.2.1 then
        if a = liveLabelAt s ij.1 ∨ a = liveLabelAt s ij.2 then s.2.1 else a
      else a
  | .inr (.inr ix) =>
      if ix.1 < s.2.2.1 ∧ a = liveLabelAt s ix.1 then
        if (q.val : ℝ) < ix.2 then s.2.1 else s.2.1 + 1
      else a

noncomputable def ancestorLabel (N : ℕ) (ω : EventPath)
    (q : GenomicProbe) (i : Fin N) : ℕ → ℕ
  | 0 => i.val
  | k + 1 => ancestorStep (ω k).1 (ω (k + 1)).2.2 q
      (ancestorLabel N ω q i k)

noncomputable def genealogyObservation (N : ℕ) (ω : EventPath) : Genealogy N :=
  fun q i j => ⨅ k : ℕ,
    if ancestorLabel N ω q i k = ancestorLabel N ω q j k
    then ENNReal.ofReal (ω k).1.1 else ⊤

theorem ancestorLabel_equal_next (N : ℕ) (ω : EventPath)
    (q : GenomicProbe) (i j : Fin N) (k : ℕ)
    (h : ancestorLabel N ω q i k = ancestorLabel N ω q j k) :
    ancestorLabel N ω q i (k + 1) = ancestorLabel N ω q j (k + 1) := by
  simp only [ancestorLabel, h]

theorem ancestorLabel_equal_later (N : ℕ) (ω : EventPath)
    (q : GenomicProbe) (i j : Fin N) (k l : ℕ) (hkl : k ≤ l)
    (h : ancestorLabel N ω q i k = ancestorLabel N ω q j k) :
    ancestorLabel N ω q i l = ancestorLabel N ω q j l := by
  induction l, hkl using Nat.le_induction with
  | base => exact h
  | succ l hl ih => exact ancestorLabel_equal_next N ω q i j l ih

end Rhone.Coalescent.IntervalProcess
