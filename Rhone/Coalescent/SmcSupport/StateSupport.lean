/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcSupport.Material

/-! # Concrete interval-material support and finite race calculations -/
@[expose] public section

namespace Rhone.Coalescent.SmcSupport
open IntervalProcess

def AllMaterials (P : Material → Prop) (s : State) : Prop :=
  ∀ i, P (s.2.2.2 i).2

theorem liveOfList_all (P : Material → Prop) (l : List (ℕ × Material))
    (h : ∀ p ∈ l, P p.2) : ∀ i, P ((liveOfList l).2 i).2 := by
  intro i
  exact h (l.get i) (List.get_mem _ _)

theorem coalSuccessor_all (P : Material → Prop) (s : State)
    (hs : AllMaterials P s)
    (hm : ∀ a b, P a → P b → P (mergeMaterial a b))
    (i j : Fin s.2.2.1) : AllMaterials P (coalSuccessor s i j) := by
  classical
  unfold coalSuccessor
  split_ifs
  · apply liveOfList_all
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
      exact hs k
    · have he : p = (s.2.1, mergeMaterial (s.2.2.2 i).2 (s.2.2.2 j).2) :=
        by simpa using hp
      rw [he]
      exact hm _ _ (hs i) (hs j)
  · exact hs

theorem splitSuccessor_all (P : Material → Prop) (s : State)
    (hs : AllMaterials P s) (i : Fin s.2.2.1) (x : ℝ)
    (hl : P (splitMaterial (s.2.2.2 i).2 x).1)
    (hr : P (splitMaterial (s.2.2.2 i).2 x).2) :
    AllMaterials P (splitSuccessor s i x) := by
  apply liveOfList_all
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
    exact hs k
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl
    · exact hl
    · exact hr

def Anchored (x : ℝ) (a : Material) : Prop := hullLo a ≤ x ∧ x ≤ hullHi a

theorem full_anchored (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (a : Material) (ha : FullAtoms a) : Anchored x a := by
  obtain ⟨hl, hr⟩ := constant_atoms_hull a 0 1 (by norm_num) ha
  simpa only [Anchored, hl, hr] using And.intro hx0 hx1

theorem merge_anchored (x : ℝ) (a b : Material) (ha : Anchored x a) :
    Anchored x (mergeMaterial a b) := by
  constructor
  · rw [hullLo_merge]
    exact (min_le_left _ _).trans ha.1
  · rw [hullHi_merge]
    exact ha.2.trans (le_max_left _ _)

inductive ZeroSplitReachable : State → Prop
  | initial (n) : ZeroSplitReachable (initialState n)
  | clock {s} : ZeroSplitReachable s → (t : ℝ) → ZeroSplitReachable (t, s.2)
  | coal {s} : ZeroSplitReachable s →
      (i j : Fin s.2.2.1) → ZeroSplitReachable (coalSuccessor s i j)

theorem zeroSplit_full {s : State} (hs : ZeroSplitReachable s) :
    AllMaterials FullAtoms s := by
  induction hs with
  | initial n => intro i j; rfl
  | clock hs t ih => exact ih
  | coal hs i j ih => exact coalSuccessor_all FullAtoms _ ih mergeMaterial_full i j

theorem full_recombinationRate (R : ℝ) {s : State}
    (hf : AllMaterials FullAtoms s) :
    recombinationRate R s = R * (s.2.2.1 : ℝ) / 2 := by
  have hlen : ∀ i, hullLength (s.2.2.2 i).2 = 1 := by
    intro i
    obtain ⟨hl, hr⟩ := constant_atoms_hull _ 0 1 (by norm_num) (hf i)
    simp [hullLength, hl, hr]
  simp [recombinationRate, hlen]
  ring

theorem zeroSplit_recombinationRate (R : ℝ) {s : State}
    (hs : ZeroSplitReachable s) :
    recombinationRate R s = R * (s.2.2.1 : ℝ) / 2 :=
  full_recombinationRate R (zeroSplit_full hs)

inductive OneSplitReachable (x : ℝ) : State → Prop
  | split {s} : ZeroSplitReachable s →
      (i : Fin s.2.2.1) → OneSplitReachable x (splitSuccessor s i x)
  | clock {s} : OneSplitReachable x s → (t : ℝ) → OneSplitReachable x (t, s.2)
  | coal {s} : OneSplitReachable x s →
      (i j : Fin s.2.2.1) → OneSplitReachable x (coalSuccessor s i j)

theorem oneSplit_anchored (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    {s : State} (hs : OneSplitReachable x s) : AllMaterials (Anchored x) s := by
  induction hs with
  | clock hs t ih => exact ih
  | @split s hs i =>
    have hf := zeroSplit_full hs
    have hm := fun j => full_anchored x hx0.le hx1.le _ (hf j)
    obtain ⟨hl, hr⟩ := first_split_atoms _ (hf i) x hx0 hx1
    apply splitSuccessor_all (Anchored x) s hm i x
    · obtain ⟨hlo, hhi⟩ := constant_atoms_hull _ 0 x hx0 hl
      exact ⟨by rw [hlo]; exact hx0.le, by rw [hhi]⟩
    · obtain ⟨hlo, hhi⟩ := constant_atoms_hull _ x 1 hx1 hr
      exact ⟨by rw [hlo], by rw [hhi]; exact hx1.le⟩
  | coal hs i j ih =>
    exact coalSuccessor_all (Anchored x) _ ih
      (fun a b ha _ => merge_anchored x a b ha) i j

theorem oneSplit_contacts (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    {s : State} (hs : OneSplitReachable x s) (i j : Fin s.2.2.1) :
    touches (s.2.2.2 i).2 (s.2.2.2 j).2 := by
  have h := oneSplit_anchored x hx0 hx1 hs
  exact ⟨(h i).1.trans (h j).2, (h j).1.trans (h i).2⟩

end Rhone.Coalescent.SmcSupport
