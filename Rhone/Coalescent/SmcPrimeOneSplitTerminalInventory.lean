/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitGlobalInventory

/-! # Terminal lineage inventory of the extraction -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess

theorem OneSplitPrefixSupported.sample_pos {N : ℕ}
    {h : Rhone.Coalescent.SmcSupport.ARGPrefix (N + 1)}
    (hs : OneSplitPrefixSupported N h) : 0 < N := by
  obtain ⟨s, hsplit, hcoal⟩ := hs.2.2.2.2.1
  let k : Fin (N + 1) := ⟨0, by omega⟩
  have ht := hs.2.2.1 k
  rw [hs.1] at ht
  by_cases he : k = s
  · have hm : (h ⟨1, Finset.mem_Iic.mpr (by omega)⟩).2.2 ∈ splitSet := by
      simpa only [← he] using hsplit
    obtain ⟨i, _, _, _, _, _, _⟩ := ht.split_case (SmcSupport.initialState_valid N) hm
    exact Nat.zero_lt_of_lt i.isLt
  · obtain ⟨i, _, _, _, _, _⟩ := ht.coal_case (hcoal k he)
    exact Nat.zero_lt_of_lt i.isLt

theorem ExtractionInventory.terminal {N : ℕ} {z : OneSplitExtractionState N}
    {s : State} (h : ExtractionInventory z s) (hN : 0 < N)
    (hc : s.2.2.1 = 1) : z.detached = none ∧ z.old.1.2.2.1 = 1 := by
  let a : Fin N := ⟨0, hN⟩
  have hfin : ∀ i j : Fin s.2.2.1, i = j := by
    intro i j
    apply Fin.ext
    have := i.isLt
    have := j.isLt
    omega
  have hsame : ∀ b : Fin N, z.argLabels b = z.argLabels a := by
    intro b
    obtain ⟨i, hi⟩ := h.2.1.1 b
    obtain ⟨j, hj⟩ := h.2.1.1 a
    exact hi.symm.trans ((congrArg (fun k => (s.2.2.2 k).1) (hfin i j)).trans hj)
  have hd : z.detached = none := by
    cases he : z.detached with
    | none => rfl
    | some d =>
      obtain ⟨⟨i, hi⟩, hnot⟩ := h.2.1.2.2 d he
      obtain ⟨j, hj⟩ := h.2.1.1 a
      exact False.elim (hnot a (hj.symm.trans
        ((congrArg (fun k => (s.2.2.2 k).1) (hfin j i)).trans hi)))
  have hidx : ∀ i j : Fin z.old.1.2.2.1, i = j := by
    intro i j
    obtain ⟨b, hb⟩ := h.2.2.2.1 i
    obtain ⟨c, hc⟩ := h.2.2.2.1 j
    have hp : z.argLabels b = z.argLabels c := (hsame b).trans (hsame c).symm
    exact h.1.2.2.2 (hb.symm.trans (((h.2.2.2.2 b c).mp hp).trans hc))
  obtain ⟨i, _⟩ := h.2.2.1 a
  refine ⟨hd, ?_⟩
  have hlo : 0 < z.old.1.2.2.1 := Nat.zero_lt_of_lt i.isLt
  by_contra hn
  have htwo : 1 < z.old.1.2.2.1 := by omega
  have he := congrArg Fin.val (hidx ⟨0, by omega⟩ ⟨1, htwo⟩)
  change (0 : ℕ) = 1 at he
  omega

theorem extractionRun_terminal_inventory (N : ℕ)
    (h : Rhone.Coalescent.SmcSupport.ARGPrefix (N + 1)) (hs : OneSplitPrefixSupported N h) :
    (extractionRun N h (N + 1)).detached = none ∧
      (extractionRun N h (N + 1)).old.1.2.2.1 = 1 :=
  (extractionRun_inventory N h hs (N + 1) le_rfl).terminal hs.sample_pos hs.2.2.2.2.2

end Rhone.Coalescent.SmcPrime
