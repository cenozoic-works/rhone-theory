/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.ClosedHitting

/-! # Chains with an allele count, and the neutral fixation probability -/

@[expose] public section

namespace Rhone.MarkovChain

open Finset MeasureTheory

structure CountedChain (S : Type*) [Fintype S] (N : ℕ) extends FinChain S where
  count : S → Fin (N + 1)

namespace CountedChain

variable {S : Type*} [Fintype S] {N : ℕ} (C : CountedChain S N)

noncomputable def freq (s : S) : ℝ := ((C.count s : ℕ) : ℝ) / N

def IsNeutral : Prop := C.toFinChain.IsHarmonic fun s => ((C.count s : ℕ) : ℝ) / N

def fixedSet [DecidableEq S] : Finset S := univ.filter fun s => C.count s = Fin.last N

def lostSet [DecidableEq S] : Finset S := univ.filter fun s => C.count s = 0

def boundary [DecidableEq S] : Finset S := C.fixedSet ∪ C.lostSet

def HasAbsorbingBoundary [DecidableEq S] : Prop :=
  C.toFinChain.IsClosedSet C.fixedSet ∧ C.toFinChain.IsClosedSet C.lostSet

variable [DecidableEq S] {C}

theorem mem_fixedSet {s : S} : s ∈ C.fixedSet ↔ C.count s = Fin.last N := by
  simp [fixedSet]

theorem mem_lostSet {s : S} : s ∈ C.lostSet ↔ C.count s = 0 := by
  simp [lostSet]

theorem mem_boundary {s : S} : s ∈ C.boundary ↔ C.count s = Fin.last N ∨ C.count s = 0 := by
  simp [boundary, mem_fixedSet, mem_lostSet]

theorem disjoint_fixedSet_lostSet (hN : 0 < N) : Disjoint C.fixedSet C.lostSet := by
  refine Finset.disjoint_left.2 fun s h1 h0 => ?_
  have h := (mem_fixedSet.1 h1).symm.trans (mem_lostSet.1 h0)
  have := congrArg Fin.val h
  simp only [Fin.val_last, Fin.val_zero] at this
  omega

theorem hasAbsorbingBoundary_of_isAbsorbing
    (h : ∀ s, (C.count s = 0 ∨ C.count s = Fin.last N) → C.toFinChain.IsAbsorbing s) :
    C.HasAbsorbingBoundary :=
  ⟨FinChain.IsAbsorbingSet.isClosedSet fun s hs => h s (Or.inr (mem_fixedSet.1 hs)),
    FinChain.IsAbsorbingSet.isClosedSet fun s hs => h s (Or.inl (mem_lostSet.1 hs))⟩

theorem freq_of_mem_fixedSet (hN : 0 < N) {s : S} (hs : s ∈ C.fixedSet) :
    ((C.count s : ℕ) : ℝ) / N = 1 := by
  rw [mem_fixedSet.1 hs, Fin.val_last]
  exact div_self (Nat.cast_ne_zero.2 hN.ne')

theorem freq_of_mem_lostSet {s : S} (hs : s ∈ C.lostSet) : ((C.count s : ℕ) : ℝ) / N = 0 := by
  rw [mem_lostSet.1 hs]
  simp

theorem enterProb_fixedSet (hN : 0 < N) (hn : C.IsNeutral) (hb : C.HasAbsorbingBoundary)
    (hR : C.toFinChain.Reaches C.boundary) (s : S) :
    C.toFinChain.enterProb C.fixedSet s = ((C.count s : ℕ) : ℝ) / N :=
  congrFun (FinChain.enterProb_eq_of_harmonicOff hb.1 hb.2 (disjoint_fixedSet_lostSet hN) hR
    (fun x _ => congrFun hn x) (fun _ ha => freq_of_mem_fixedSet hN ha)
    fun _ ha => freq_of_mem_lostSet ha) s

variable [MeasurableSpace S] [DiscreteMeasurableSpace S]

theorem fixation_real (hN : 0 < N) (hn : C.IsNeutral) (hb : C.HasAbsorbingBoundary)
    (hR : C.toFinChain.Reaches C.boundary) (s : S) :
    (C.toFinChain.pathLaw s).real {ω | ∃ n, C.count (ω n) = Fin.last N} =
      ((C.count s : ℕ) : ℝ) / N := by
  have hset : {ω : ℕ → S | ∃ n, C.count (ω n) = Fin.last N} = {ω | ∃ n, ω n ∈ C.fixedSet} := by
    ext ω
    simp [mem_fixedSet]
  rw [hset, hb.1.pathLaw_enter_eq_enterProb, enterProb_fixedSet hN hn hb hR]

theorem fixation_real_eventually (hN : 0 < N) (hn : C.IsNeutral) (hb : C.HasAbsorbingBoundary)
    (hR : C.toFinChain.Reaches C.boundary) (s : S) :
    (C.toFinChain.pathLaw s).real {ω | ∃ n, ∀ m, n ≤ m → C.count (ω m) = Fin.last N} =
      ((C.count s : ℕ) : ℝ) / N := by
  have hset : {ω : ℕ → S | ∃ n, ∀ m, n ≤ m → C.count (ω m) = Fin.last N} =
      {ω | ∃ n, ∀ m, n ≤ m → ω m ∈ C.fixedSet} := by
    ext ω
    simp [mem_fixedSet]
  rw [hset, hb.1.pathLaw_eventually_mem_eq_enter, hb.1.pathLaw_enter_eq_enterProb,
    enterProb_fixedSet hN hn hb hR]

theorem loss_real (hN : 0 < N) (hn : C.IsNeutral) (hb : C.HasAbsorbingBoundary)
    (hR : C.toFinChain.Reaches C.boundary) (s : S) :
    (C.toFinChain.pathLaw s).real {ω | ∃ n, C.count (ω n) = 0} =
      1 - ((C.count s : ℕ) : ℝ) / N := by
  have hset : {ω : ℕ → S | ∃ n, C.count (ω n) = 0} = {ω | ∃ n, ω n ∈ C.lostSet} := by
    ext ω
    simp [mem_lostSet]
  have hsum := FinChain.enterProb_add_enterProb hb.1 hb.2 (disjoint_fixedSet_lostSet hN) hR s
  rw [hset, hb.2.pathLaw_enter_eq_enterProb, ← enterProb_fixedSet hN hn hb hR s]
  linarith

theorem ae_fixed_or_lost (hb : C.HasAbsorbingBoundary) (hR : C.toFinChain.Reaches C.boundary)
    (s : S) :
    ∀ᵐ ω ∂C.toFinChain.pathLaw s,
      ∃ n, ∀ m, n ≤ m → C.count (ω m) = Fin.last N ∨ C.count (ω m) = 0 := by
  filter_upwards [(hb.1.union hb.2).ae_eventually_mem hR s] with ω ⟨n, hn⟩
  exact ⟨n, fun m hm => mem_boundary.1 (hn m hm)⟩

end CountedChain

end Rhone.MarkovChain
