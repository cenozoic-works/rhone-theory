/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeKingmanCompletion

/-! # Rebuilding ARG prefixes from event traces: states, events, and steps -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess

abbrev RebuildState (N : ℕ) := AugmentedState × (Fin N → ℕ) × (Fin N → ℕ) × Option ℕ

abbrev RebuildEvent (N : ℕ) := Fin (N - 1) ⊕ Bool

noncomputable def rebuildSampleUID {N : ℕ} (f : Fin N → ℕ) (c : Finset (Fin N)) : ℕ := by
  classical
  exact match (List.finRange N).find? (fun i => i ∈ c) with
    | none => 0
    | some i => f i

noncomputable def rebuildUIDIndex (s : State) (a : ℕ) : ℕ := by
  classical
  exact match (List.finRange s.2.2.1).find? (fun i => (s.2.2.2 i).1 = a) with
    | none => s.2.2.1
    | some i => i.val

noncomputable def rebuildCoal {N : ℕ} (z : RebuildState N) (t : ℝ) (a b : ℕ) : RebuildState N :=
  let i := rebuildUIDIndex z.1.1 a
  let j := rebuildUIDIndex z.1.1 b
  let ij := (min i j, max i j)
  let e : Event := .inr (.inl ij)
  ((atTime t (coalSuccessorNat z.1.1 ij), (t, e)),
    (fun k => ancestorStep z.1.1 e leftBoundaryProbe (z.2.1 k)),
    (fun k => ancestorStep z.1.1 e leftBoundaryProbe (z.2.2.1 k)), z.2.2.2)

noncomputable def rebuildSplit {N : ℕ} (z : RebuildState N) (t x : ℝ) (a : ℕ) :
    RebuildState N := by
  classical
  let i := rebuildUIDIndex z.1.1 a
  exact if hi : i < z.1.1.2.2.1 then
    ((atTime t (splitSuccessor z.1.1 ⟨i, hi⟩ x), (t, .inr (.inr (i, x)))),
      (fun k => if z.2.1 k = a then z.1.1.2.1 else z.2.1 k),
      (fun k => if z.2.2.1 k = a then z.1.1.2.1 + 1 else z.2.2.1 k),
      some (z.1.1.2.1 + 1))
  else z

noncomputable def rebuildCutClade {N : ℕ} (η : OneSplitSkeleton N) : Finset (Fin N) :=
  let T := metricTreeFromHistory N η.1
  if hi : η.2.1 < T.1 then (T.2 ⟨η.2.1, hi⟩).1 else ∅

noncomputable def rebuildEventTime {N : ℕ} (η : OneSplitSkeleton N) : RebuildEvent N → ℝ
  | .inl k => (η.1 ⟨k.val + 1, by omega⟩).1.1
  | .inr false => η.2.2.1
  | .inr true => η.2.2.2.2.1

noncomputable def rebuildStep {N : ℕ} (η : OneSplitSkeleton N)
    (z : RebuildState N) : RebuildEvent N → RebuildState N
  | .inl k =>
    let old := η.1 ⟨k.val, by omega⟩
    match (η.1 ⟨k.val + 1, by omega⟩).2.2 with
    | .inr (.inl ij) =>
      let c := historyClade N η.1 k.val (liveLabelAt old.1 ij.1)
      let d := historyClade N η.1 k.val (liveLabelAt old.1 ij.2)
      rebuildCoal z (rebuildEventTime η (.inl k))
        (rebuildSampleUID z.2.1 c) (rebuildSampleUID z.2.1 d)
    | _ => z
  | .inr false => rebuildSplit z η.2.2.1 η.2.2.2.1
      (rebuildSampleUID z.2.1 (rebuildCutClade η))
  | .inr true =>
    match z.2.2.2 with
    | none => z
    | some a =>
      let z' := rebuildCoal z η.2.2.2.2.1 a (rebuildSampleUID z.2.1 η.2.2.2.2.2)
      (z'.1, z'.2.1, z'.2.2.1, none)

noncomputable def rebuildEvents {N : ℕ} (η : OneSplitSkeleton N) : List (RebuildEvent N) :=
  ((List.finRange (N - 1)).map Sum.inl ++
    ([.inr false, .inr true] : List (RebuildEvent N))).mergeSort
    (fun a b => decide (rebuildEventTime η a ≤ rebuildEventTime η b))

noncomputable def rebuildInitial (N : ℕ) : RebuildState N :=
  ((initialState N, (0, .inl ())), (fun i => i.val), (fun i => i.val), none)

noncomputable def oneSplitRebuild (N : ℕ) (η : OneSplitSkeleton N) :
    Fin (N + 2) → AugmentedState :=
  fun k => (((rebuildEvents η).take k.val).foldl (rebuildStep η) (rebuildInitial N)).1

theorem rebuildEvents_length {N : ℕ} (η : OneSplitSkeleton N) (hN : 0 < N) :
    (rebuildEvents η).length = N + 1 := by
  simp only [rebuildEvents, List.length_mergeSort, List.length_append, List.length_map,
    List.length_finRange, List.length_cons, List.length_nil]
  omega

theorem oneSplitRebuild_zero (N : ℕ) (η : OneSplitSkeleton N) :
    oneSplitRebuild N η 0 = (initialState N, (0, .inl ())) := by
  rfl

end Rhone.Coalescent.SmcPrime
