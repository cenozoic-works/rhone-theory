/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcSupport.Rates
public import Rhone.Coalescent.SmcSpan.Spans

/-! # Concrete concatenation and the exact first split of full material -/
@[expose] public section
namespace Rhone.Coalescent.SmcSupport
open IntervalProcess

theorem mergeMaterial_all (a b : Material) (P : ℝ × ℝ → Prop)
    (ha : ∀ i, P (a.2 i)) (hb : ∀ i, P (b.2 i)) :
    ∀ i, P ((mergeMaterial a b).2 i) := by
  intro i
  unfold mergeMaterial
  dsimp
  split_ifs
  · exact ha _
  · exact hb _

theorem mergeMaterial_left_atom (a b : Material) (i : Fin (a.1 + 1)) :
    (mergeMaterial a b).2 ⟨i.val, by change i.val < a.1 + b.1 + 1 + 1; omega⟩ = a.2 i := by
  simp only [mergeMaterial, dite_eq_left i.isLt]

theorem mergeMaterial_right_atom (a b : Material) (i : Fin (b.1 + 1)) :
    (mergeMaterial a b).2 ⟨a.1 + 1 + i.val,
      by change a.1 + 1 + i.val < a.1 + b.1 + 1 + 1; omega⟩ = b.2 i := by
  simp only [mergeMaterial]
  rw [dite_eq_right (by omega)]
  apply congrArg b.2
  apply Fin.ext
  simp

theorem hullLo_le_atom (a : Material) (i : Fin (a.1 + 1)) :
    hullLo a ≤ if (a.2 i).1 < (a.2 i).2 then (a.2 i).1 else 1 :=
  Finset.inf'_le _ (Finset.mem_univ i)

theorem atom_le_hullHi (a : Material) (i : Fin (a.1 + 1)) :
    (if (a.2 i).1 < (a.2 i).2 then (a.2 i).2 else 0) ≤ hullHi a :=
  Finset.le_sup' (fun j => if (a.2 j).1 < (a.2 j).2 then (a.2 j).2 else 0)
    (Finset.mem_univ i)

theorem mergeMaterial_valid (a b : Material)
    (ha : MaterialValid a) (hb : MaterialValid b) :
    MaterialValid (mergeMaterial a b) := by
  constructor
  · exact mergeMaterial_all a b
      (fun p => 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 1) ha.1 hb.1
  · obtain ⟨i, hi⟩ := ha.2
    exact ⟨⟨i.val, by change i.val < a.1 + b.1 + 1 + 1; omega⟩,
      by simpa only [mergeMaterial_left_atom] using hi⟩

theorem hullLo_merge (a b : Material) :
    hullLo (mergeMaterial a b) = min (hullLo a) (hullLo b) := by
  classical
  apply le_antisymm
  · apply le_min
    · obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
        (fun j : Fin (a.1 + 1) => if (a.2 j).1 < (a.2 j).2 then (a.2 j).1 else 1)
      have h := hullLo_le_atom (mergeMaterial a b)
        ⟨i.val, by change i.val < a.1 + b.1 + 1 + 1; omega⟩
      rw [mergeMaterial_left_atom a b i] at h
      exact h.trans (le_of_eq hi.symm)
    · obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
        (fun j : Fin (b.1 + 1) => if (b.2 j).1 < (b.2 j).2 then (b.2 j).1 else 1)
      have h := hullLo_le_atom (mergeMaterial a b)
        ⟨a.1 + 1 + i.val, by change a.1 + 1 + i.val < a.1 + b.1 + 1 + 1; omega⟩
      rw [mergeMaterial_right_atom a b i] at h
      exact h.trans (le_of_eq hi.symm)
  · unfold hullLo
    apply Finset.le_inf'
    intro i hi
    have hin : i.val < a.1 + b.1 + 1 + 1 := i.isLt
    change min (hullLo a) (hullLo b) ≤ _
    by_cases h : i.val < a.1 + 1
    · have he : (mergeMaterial a b).2 i = a.2 ⟨i.val, h⟩ := by
        simp only [mergeMaterial, dite_eq_left h]
      rw [he]
      exact (min_le_left _ _).trans (hullLo_le_atom a _)
    · have he : (mergeMaterial a b).2 i = b.2 ⟨i.val - (a.1 + 1), by omega⟩ := by
        simp only [mergeMaterial, dite_eq_right h]
      rw [he]
      exact (min_le_right _ _).trans (hullLo_le_atom b _)

theorem hullHi_merge (a b : Material) :
    hullHi (mergeMaterial a b) = max (hullHi a) (hullHi b) := by
  classical
  apply le_antisymm
  · unfold hullHi
    apply Finset.sup'_le
    intro i hi
    have hin : i.val < a.1 + b.1 + 1 + 1 := i.isLt
    change _ ≤ max (hullHi a) (hullHi b)
    by_cases h : i.val < a.1 + 1
    · have he : (mergeMaterial a b).2 i = a.2 ⟨i.val, h⟩ := by
        simp only [mergeMaterial, dite_eq_left h]
      rw [he]
      exact (atom_le_hullHi a _).trans (le_max_left _ _)
    · have he : (mergeMaterial a b).2 i = b.2 ⟨i.val - (a.1 + 1), by omega⟩ := by
        simp only [mergeMaterial, dite_eq_right h]
      rw [he]
      exact (atom_le_hullHi b _).trans (le_max_right _ _)
  · apply max_le
    · obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
        (fun j : Fin (a.1 + 1) => if (a.2 j).1 < (a.2 j).2 then (a.2 j).2 else 0)
      have h := atom_le_hullHi (mergeMaterial a b)
        ⟨i.val, by change i.val < a.1 + b.1 + 1 + 1; omega⟩
      rw [mergeMaterial_left_atom a b i] at h
      exact (le_of_eq hi).trans h
    · obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
        (fun j : Fin (b.1 + 1) => if (b.2 j).1 < (b.2 j).2 then (b.2 j).2 else 0)
      have h := atom_le_hullHi (mergeMaterial a b)
        ⟨a.1 + 1 + i.val, by change a.1 + 1 + i.val < a.1 + b.1 + 1 + 1; omega⟩
      rw [mergeMaterial_right_atom a b i] at h
      exact (le_of_eq hi).trans h

def FullAtoms (a : Material) : Prop := ∀ i, a.2 i = (0, 1)

theorem mergeMaterial_full (a b : Material)
    (ha : FullAtoms a) (hb : FullAtoms b) : FullAtoms (mergeMaterial a b) :=
  mergeMaterial_all a b (fun p => p = (0, 1)) ha hb

theorem first_split_atoms (a : Material) (ha : FullAtoms a)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    (∀ i, ((splitMaterial a x).1.2 i) = (0, x)) ∧
      (∀ i, ((splitMaterial a x).2.2 i) = (x, 1)) := by
  constructor <;> intro i <;>
    simp [splitMaterial, ha i, min_eq_right hx1.le, max_eq_right hx0.le]

theorem constant_atoms_hull (a : Material) (l r : ℝ) (hlr : l < r)
    (ha : ∀ i, a.2 i = (l, r)) : hullLo a = l ∧ hullHi a = r := by
  classical
  simp [hullLo, hullHi, ha, hlr]

inductive Tagged (x : ℝ) : Material → Rhone.Coalescent.SmcSpan.Span → Prop
  | full (a) : FullAtoms a → Tagged x a .full
  | left (a) : (∀ i, a.2 i = (0, x)) → Tagged x a .left
  | right (a) : (∀ i, a.2 i = (x, 1)) → Tagged x a .right
  | merge {a b u v} : Tagged x a u → Tagged x b v →
      Tagged x (mergeMaterial a b) (Rhone.Coalescent.SmcSpan.merge u v)

theorem tagged_hull (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    {a : Material} {u : Rhone.Coalescent.SmcSpan.Span} (h : Tagged x a u) :
    hullLo a = Rhone.Coalescent.SmcSpan.lo x u ∧
      hullHi a = Rhone.Coalescent.SmcSpan.hi x u := by
  induction h with
  | full a ha => exact constant_atoms_hull a 0 1 (by norm_num) ha
  | left a ha => exact constant_atoms_hull a 0 x hx0 ha
  | right a ha => exact constant_atoms_hull a x 1 hx1 ha
  | @merge a b u v ha hb iha ihb =>
    obtain ⟨hl, hh⟩ := Rhone.Coalescent.SmcSpan.merge_endpoints x hx0.le hx1.le u v
    constructor
    · rw [hullLo_merge, iha.1, ihb.1, hl]
    · rw [hullHi_merge, iha.2, ihb.2, hh]

theorem tagged_contact (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    {a b : Material} {u v : Rhone.Coalescent.SmcSpan.Span}
    (ha : Tagged x a u) (hb : Tagged x b v)
    (huv : Rhone.Coalescent.SmcSpan.Compatible u v) : touches a b := by
  obtain ⟨hal, hah⟩ := tagged_hull x hx0 hx1 ha
  obtain ⟨hbl, hbh⟩ := tagged_hull x hx0 hx1 hb
  unfold touches
  rw [hal, hah, hbl, hbh]
  exact Rhone.Coalescent.SmcSpan.compatible_touches x hx0.le hx1.le u v huv

end Rhone.Coalescent.SmcSupport
