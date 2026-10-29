/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.Data.Finset.Lattice.Fold
public import Lean.Elab.Tactic.Omega

/-! # Concrete finite arrays for an unpruned continuous-interval ancestral process -/
@[expose] public section

namespace Rhone.Coalescent.IntervalProcess

abbrev Material := (k : ℕ) × (Fin (k + 1) → (ℝ × ℝ))
abbrev LiveState := (m : ℕ) × (Fin m → (ℕ × Material))
abbrev State := ℝ × ℕ × LiveState
abbrev Action := (ℕ × ℕ) ⊕ ℕ
abbrev Event := Unit ⊕ ((ℕ × ℕ) ⊕ (ℕ × ℝ))
abbrev EventRecord := ℝ × Event
abbrev Noise := Fin 3 → ℝ
abbrev Mode := Bool

def MaterialValid (a : Material) : Prop :=
  (∀ i, 0 ≤ (a.2 i).1 ∧ (a.2 i).1 ≤ (a.2 i).2 ∧ (a.2 i).2 ≤ 1) ∧
  ∃ i, (a.2 i).1 < (a.2 i).2

def Valid (s : State) : Prop :=
  0 ≤ s.1 ∧
  (∀ i, MaterialValid (s.2.2.2 i).2) ∧
  (∀ i, (s.2.2.2 i).1 < s.2.1) ∧
  Function.Injective (fun i => (s.2.2.2 i).1)

noncomputable def hullLo (a : Material) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty
    (fun i => if (a.2 i).1 < (a.2 i).2 then (a.2 i).1 else 1)

noncomputable def hullHi (a : Material) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun i => if (a.2 i).1 < (a.2 i).2 then (a.2 i).2 else 0)

noncomputable def hullLength (a : Material) : ℝ := max 0 (hullHi a - hullLo a)

noncomputable def touches (a b : Material) : Prop :=
  hullLo a ≤ hullHi b ∧ hullLo b ≤ hullHi a

noncomputable def splitMaterial (a : Material) (x : ℝ) : Material × Material :=
  (⟨a.1, fun i => ((a.2 i).1, max (a.2 i).1 (min (a.2 i).2 x))⟩,
   ⟨a.1, fun i => (max (a.2 i).1 (min (a.2 i).2 x), (a.2 i).2)⟩)

def mergeMaterial (a b : Material) : Material :=
  ⟨a.1 + b.1 + 1, fun i =>
    if h : i.val < a.1 + 1 then a.2 ⟨i.val, h⟩
    else b.2 ⟨i.val - (a.1 + 1), by omega⟩⟩

def liveOfList (l : List (ℕ × Material)) : LiveState :=
  ⟨l.length, fun i => l.get i⟩

def coalSuccessor (s : State) (i j : Fin s.2.2.1) : State :=
  if i.val < j.val then
    let survivors := (List.finRange s.2.2.1).filter (fun k => k ≠ i ∧ k ≠ j)
    let lineages := survivors.map s.2.2.2 ++
      [(s.2.1, mergeMaterial (s.2.2.2 i).2 (s.2.2.2 j).2)]
    (s.1, s.2.1 + 1, liveOfList lineages)
  else s

def initialState (n : ℕ) : State :=
  (0, n, ⟨n, fun i => (i.val, ⟨0, fun _ => (0, 1)⟩)⟩)

noncomputable def splitSuccessor (s : State) (i : Fin s.2.2.1) (x : ℝ) : State :=
  let survivors := (List.finRange s.2.2.1).filter (fun k => k ≠ i)
  let daughters := splitMaterial (s.2.2.2 i).2 x
  let lineages := survivors.map s.2.2.2 ++
    [(s.2.1, daughters.1), (s.2.1 + 1, daughters.2)]
  (s.1, s.2.1 + 2, liveOfList lineages)

end Rhone.Coalescent.IntervalProcess
