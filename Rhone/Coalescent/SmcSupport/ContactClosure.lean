/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcSupport.StateSupport

/-! # Contact closure of lineages under coalescence and split -/
@[expose] public section
namespace Rhone.Coalescent.SmcSupport
open IntervalProcess

theorem contacts_common_anchor (s : State) (hm : 0 < s.2.2.1)
    (hs : ∀ i j, touches (s.2.2.2 i).2 (s.2.2.2 j).2) :
    ∃ x, AllMaterials (Anchored x) s := by
  classical
  have hn : (Finset.univ : Finset (Fin s.2.2.1)).Nonempty :=
    ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  refine ⟨Finset.univ.sup' hn (fun i => hullLo (s.2.2.2 i).2), ?_⟩
  intro i
  constructor
  · exact Finset.le_sup' (fun j : Fin s.2.2.1 => hullLo (s.2.2.2 j).2)
      (Finset.mem_univ i)
  · apply Finset.sup'_le
    intro j hj
    exact (hs j i).1

theorem coalSuccessor_contacts (s : State) (hm : 0 < s.2.2.1)
    (hs : ∀ i j, touches (s.2.2.2 i).2 (s.2.2.2 j).2)
    (i j : Fin s.2.2.1) :
    ∀ k l, touches ((coalSuccessor s i j).2.2.2 k).2
      ((coalSuccessor s i j).2.2.2 l).2 := by
  obtain ⟨x, hx⟩ := contacts_common_anchor s hm hs
  have ha := coalSuccessor_all (Anchored x) s hx
    (fun a b ha _ => merge_anchored x a b ha) i j
  intro k l
  exact ⟨(ha k).1.trans (ha l).2, (ha l).1.trans (ha k).2⟩

theorem full_contacts (s : State) (hs : AllMaterials FullAtoms s) :
    ∀ i j, touches (s.2.2.2 i).2 (s.2.2.2 j).2 := by
  have h := fun i => full_anchored 0 (by norm_num) (by norm_num) _ (hs i)
  intro i j
  exact ⟨(h i).1.trans (h j).2, (h j).1.trans (h i).2⟩

theorem splitFull_anchored (s : State) (hs : AllMaterials FullAtoms s)
    (i : Fin s.2.2.1) (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    AllMaterials (Anchored x) (splitSuccessor s i x) := by
  have hm := fun j => full_anchored x hx0.le hx1.le _ (hs j)
  obtain ⟨hl, hr⟩ := first_split_atoms _ (hs i) x hx0 hx1
  apply splitSuccessor_all (Anchored x) s hm i x
  · obtain ⟨hlo, hhi⟩ := constant_atoms_hull _ 0 x hx0 hl
    exact ⟨by rw [hlo]; exact hx0.le, by rw [hhi]⟩
  · obtain ⟨hlo, hhi⟩ := constant_atoms_hull _ x 1 hx1 hr
    exact ⟨by rw [hlo], by rw [hhi]; exact hx1.le⟩

theorem splitFull_contacts (s : State) (hs : AllMaterials FullAtoms s)
    (i : Fin s.2.2.1) (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    ∀ k l, touches ((splitSuccessor s i x).2.2.2 k).2
      ((splitSuccessor s i x).2.2.2 l).2 := by
  have h := splitFull_anchored s hs i x hx0 hx1
  intro k l
  exact ⟨(h k).1.trans (h l).2, (h l).1.trans (h k).2⟩

end Rhone.Coalescent.SmcSupport
