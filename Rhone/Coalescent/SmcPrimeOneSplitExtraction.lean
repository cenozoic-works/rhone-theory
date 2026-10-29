/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeRebuildLookups
public import Rhone.Coalescent.SmcPrimeKingmanObservation
public import Rhone.Coalescent.SmcSupport.ARGFiniteHistory

/-! # The one-split extraction: state, step, and run -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess

structure OneSplitExtractionState (N : ℕ) where
  old : AugmentedState
  oldLabels : Fin N → ℕ
  argLabels : Fin N → ℕ
  detached : Option ℕ
  oldHistory : KingmanHistory N
  mergers : ℕ
  cut : Finset (Fin N) × ℝ × ℝ
  attachment : ℝ × Finset (Fin N)

noncomputable def extractionClade {N : ℕ} (f : Fin N → ℕ) (a : ℕ) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter (fun i => f i = a)

noncomputable def extractionInitial (N : ℕ) : OneSplitExtractionState N :=
  { old := (initialState N, (0, .inl ()))
    oldLabels := fun i => i.val
    argLabels := fun i => i.val
    detached := none
    oldHistory := fun _ => (initialState N, (0, .inl ()))
    mergers := 0
    cut := (∅, 0, 0)
    attachment := (0, ∅) }

noncomputable def extractionStep {N : ℕ} (z : OneSplitExtractionState N)
    (pre next : AugmentedState) : OneSplitExtractionState N := by
  classical
  let f := fun i => ancestorStep pre.1 next.2.2 leftBoundaryProbe (z.argLabels i)
  exact match next.2.2 with
    | .inl _ => { z with argLabels := f }
    | .inr (.inr ix) =>
      { z with argLabels := f
               detached := some (pre.1.2.1 + 1)
               cut := (extractionClade z.argLabels (liveLabelAt pre.1 ix.1),
                 next.1.1, ix.2) }
    | .inr (.inl ij) =>
      let a := liveLabelAt pre.1 ij.1
      let b := liveLabelAt pre.1 ij.2
      if ∃ d, z.detached = some d ∧ (d = a ∨ d = b) then
        let target := if z.detached = some a then b else a
        { z with argLabels := f
                 detached := none
                 attachment := (next.1.1, extractionClade z.argLabels target) }
      else
        let c := extractionClade z.argLabels a
        let d := extractionClade z.argLabels b
        let oldReplay : RebuildState N := (z.old, z.oldLabels, z.oldLabels, none)
        let oldNext := rebuildCoal oldReplay next.1.1
          (rebuildSampleUID z.oldLabels c) (rebuildSampleUID z.oldLabels d)
        { z with old := oldNext.1
                 oldLabels := oldNext.2.1
                 argLabels := f
                 oldHistory := if hj : z.mergers + 1 < N then
                   Function.update z.oldHistory ⟨z.mergers + 1, hj⟩ oldNext.1
                   else z.oldHistory
                 mergers := z.mergers + 1 }

noncomputable def extractionRun (N : ℕ)
    (h : Rhone.Coalescent.SmcSupport.ARGPrefix (N + 1)) (n : ℕ) :
    OneSplitExtractionState N :=
  ((List.finRange (N + 1)).take n).foldl (fun z k => extractionStep z
    (h ⟨k.val, Finset.mem_Iic.mpr (by have := k.isLt; omega)⟩)
    (h ⟨k.val + 1, Finset.mem_Iic.mpr (by have := k.isLt; omega)⟩)) (extractionInitial N)

noncomputable def extractionCutIndex {N : ℕ} (T : Tree N) (c : Finset (Fin N)) (t : ℝ) : ℕ := by
  classical
  exact match (List.finRange T.1).find?
      (fun i => i ∈ activeBranches T t ∧ (T.2 i).1 = c) with
    | none => T.1
    | some i => i.val

noncomputable def extractOneSplitSkeleton (N : ℕ)
    (h : Rhone.Coalescent.SmcSupport.ARGPrefix (N + 1)) : OneSplitSkeleton N :=
  let z := extractionRun N h (N + 1)
  (z.oldHistory, extractionCutIndex (metricTreeFromHistory N z.oldHistory) z.cut.1 z.cut.2.1,
    z.cut.2.1, z.cut.2.2, z.attachment.1, z.attachment.2)

theorem extractionRun_zero (N : ℕ) (h : Rhone.Coalescent.SmcSupport.ARGPrefix (N + 1)) :
    extractionRun N h 0 = extractionInitial N := by
  rfl

theorem extractionCutIndex_active {N : ℕ} (T : Tree N) (hu : TreeActiveUnique T)
    (t : ℝ) (ht : 0 ≤ t) (i : Fin T.1) (hi : i ∈ activeBranches T t) :
    extractionCutIndex T (T.2 i).1 t = i.val := by
  classical
  unfold extractionCutIndex
  generalize he : (List.finRange T.1).find?
    (fun j => decide (j ∈ activeBranches T t ∧ (T.2 j).1 = (T.2 i).1)) = o
  cases o with
  | none =>
    have hex : ((List.finRange T.1).find?
        (fun j => decide (j ∈ activeBranches T t ∧ (T.2 j).1 = (T.2 i).1))).isSome :=
      List.find?_isSome.mpr ⟨i, by simp, by simpa using hi⟩
    rw [he] at hex
    cases hex
  | some j =>
    have hj : j ∈ activeBranches T t ∧ (T.2 j).1 = (T.2 i).1 := by
      simpa using List.find?_some he
    exact congrArg Fin.val (hu t ht j hj.1 i hi hj.2)

end Rhone.Coalescent.SmcPrime
