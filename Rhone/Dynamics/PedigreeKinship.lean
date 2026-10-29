/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Combinatorics.Pedigree
public import Rhone.Dynamics.Inbreeding
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Kinship and inbreeding coefficients on a finite pedigree

Source: malecot1969, ch. 1, pp. 8–10; felsenstein_teg2019, pp. 226–227, eq. (V-13)–(V-18). -/

@[expose] public section

namespace Rhone.Combinatorics.Pedigree

variable {n : ℕ}

def kinship (P : Pedigree n) (i j : Fin n) : ℚ :=
  if _hij : i = j then
    match h : P.parents i with
    | none => 1 / 2
    | some p => (1 + kinship P p.1 p.2) / 2
  else if i < j then
    match h : P.parents j with
    | none => 0
    | some p => (kinship P i p.1 + kinship P i p.2) / 2
  else
    match h : P.parents i with
    | none => 0
    | some p => (kinship P p.1 j + kinship P p.2 j) / 2
termination_by i.val + j.val
decreasing_by
  all_goals
    have hlt := P.parents_lt _ _ h
    first
      | (have hij : i = j := by assumption
         rw [← hij]
         exact Nat.add_lt_add (Fin.lt_def.mp hlt.1) (Fin.lt_def.mp hlt.2))
      | exact Nat.add_lt_add_left (Fin.lt_def.mp hlt.1) _
      | exact Nat.add_lt_add_left (Fin.lt_def.mp hlt.2) _
      | exact Nat.add_lt_add_right (Fin.lt_def.mp hlt.1) _
      | exact Nat.add_lt_add_right (Fin.lt_def.mp hlt.2) _

def inbreeding (P : Pedigree n) (i : Fin n) : ℚ :=
  match P.parents i with
  | none => 0
  | some p => kinship P p.1 p.2

theorem pair_induction {motive : Fin n → Fin n → Prop}
    (h : ∀ i j, (∀ i' j', i'.val + j'.val < i.val + j.val → motive i' j') → motive i j)
    (i j : Fin n) : motive i j := by
  induction hN : i.val + j.val using Nat.strong_induction_on generalizing i j with
  | _ N ih =>
    refine h i j fun i' j' hlt => ih (i'.val + j'.val) ?_ i' j' rfl
    rw [← hN]
    exact hlt

theorem inbreeding_founder (P : Pedigree n) {i : Fin n} (hi : P.parents i = none) :
    P.inbreeding i = 0 := by
  simp [inbreeding, hi]

theorem inbreeding_of_parents (P : Pedigree n) {i : Fin n} {p : Fin n × Fin n}
    (hi : P.parents i = some p) : P.inbreeding i = P.kinship p.1 p.2 := by
  simp [inbreeding, hi]

theorem kinship_self (P : Pedigree n) (i : Fin n) :
    P.kinship i i = (1 + P.inbreeding i) / 2 := by
  rw [kinship]
  simp only [↓reduceDIte]
  split
  · next h => rw [inbreeding_founder P h, add_zero]
  · next p h => rw [inbreeding_of_parents P h]

theorem kinship_of_lt_founder (P : Pedigree n) {i j : Fin n} (hij : i < j)
    (hj : P.parents j = none) : P.kinship i j = 0 := by
  rw [kinship]
  simp only [hij.ne, hij, ↓reduceDIte, ↓reduceIte]
  split
  · rfl
  · next p h => rw [hj] at h; cases h

theorem kinship_of_lt (P : Pedigree n) {i j : Fin n} {p : Fin n × Fin n} (hij : i < j)
    (hj : P.parents j = some p) :
    P.kinship i j = (P.kinship i p.1 + P.kinship i p.2) / 2 := by
  rw [kinship]
  simp only [hij.ne, hij, ↓reduceDIte, ↓reduceIte]
  split
  · next h => rw [hj] at h; cases h
  · next q h =>
    rw [hj] at h
    cases h
    rfl

theorem kinship_of_gt_founder (P : Pedigree n) {i j : Fin n} (hji : j < i)
    (hi : P.parents i = none) : P.kinship i j = 0 := by
  rw [kinship]
  simp only [ne_of_gt hji, not_lt.mpr hji.le, ↓reduceDIte, ↓reduceIte]
  split
  · rfl
  · next p h => rw [hi] at h; cases h

theorem kinship_of_gt (P : Pedigree n) {i j : Fin n} {p : Fin n × Fin n} (hji : j < i)
    (hi : P.parents i = some p) :
    P.kinship i j = (P.kinship p.1 j + P.kinship p.2 j) / 2 := by
  rw [kinship]
  simp only [ne_of_gt hji, not_lt.mpr hji.le, ↓reduceDIte, ↓reduceIte]
  split
  · next h => rw [hi] at h; cases h
  · next q h =>
    rw [hi] at h
    cases h
    rfl

theorem kinship_comm (P : Pedigree n) (i j : Fin n) : P.kinship i j = P.kinship j i := by
  refine pair_induction (motive := fun i j => P.kinship i j = P.kinship j i) ?_ i j
  intro i j ih
  rcases lt_trichotomy i j with hij | rfl | hji
  · cases hj : P.parents j with
    | none => rw [kinship_of_lt_founder P hij hj, kinship_of_gt_founder P hij hj]
    | some p =>
      have hlt := P.parents_lt j p hj
      rw [kinship_of_lt P hij hj, kinship_of_gt P hij hj,
        ih i p.1 (Nat.add_lt_add_left (Fin.lt_def.mp hlt.1) _),
        ih i p.2 (Nat.add_lt_add_left (Fin.lt_def.mp hlt.2) _)]
  · rfl
  · cases hi : P.parents i with
    | none => rw [kinship_of_lt_founder P hji hi, kinship_of_gt_founder P hji hi]
    | some p =>
      have hlt := P.parents_lt i p hi
      rw [kinship_of_lt P hji hi, kinship_of_gt P hji hi,
        ih p.1 j (Nat.add_lt_add_right (Fin.lt_def.mp hlt.1) _),
        ih p.2 j (Nat.add_lt_add_right (Fin.lt_def.mp hlt.2) _)]

private theorem kinship_mem_Icc (P : Pedigree n) (i j : Fin n) :
    0 ≤ P.kinship i j ∧ P.kinship i j ≤ 1 := by
  refine pair_induction (motive := fun i j => 0 ≤ P.kinship i j ∧ P.kinship i j ≤ 1) ?_ i j
  intro i j ih
  rcases lt_trichotomy i j with hij | rfl | hji
  · cases hj : P.parents j with
    | none => rw [kinship_of_lt_founder P hij hj]; exact ⟨le_rfl, zero_le_one⟩
    | some p =>
      have hlt := P.parents_lt j p hj
      have h1 := ih i p.1 (Nat.add_lt_add_left (Fin.lt_def.mp hlt.1) _)
      have h2 := ih i p.2 (Nat.add_lt_add_left (Fin.lt_def.mp hlt.2) _)
      rw [kinship_of_lt P hij hj]
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  · rw [kinship_self]
    cases hi : P.parents i with
    | none => rw [inbreeding_founder P hi]; norm_num
    | some p =>
      have hlt := P.parents_lt i p hi
      have h1 := ih p.1 p.2
        (Nat.add_lt_add (Fin.lt_def.mp hlt.1) (Fin.lt_def.mp hlt.2))
      rw [inbreeding_of_parents P hi]
      constructor <;> linarith [h1.1, h1.2]
  · cases hi : P.parents i with
    | none => rw [kinship_of_gt_founder P hji hi]; exact ⟨le_rfl, zero_le_one⟩
    | some p =>
      have hlt := P.parents_lt i p hi
      have h1 := ih p.1 j (Nat.add_lt_add_right (Fin.lt_def.mp hlt.1) _)
      have h2 := ih p.2 j (Nat.add_lt_add_right (Fin.lt_def.mp hlt.2) _)
      rw [kinship_of_gt P hji hi]
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem kinship_nonneg (P : Pedigree n) (i j : Fin n) : 0 ≤ P.kinship i j :=
  (kinship_mem_Icc P i j).1

theorem kinship_le_one (P : Pedigree n) (i j : Fin n) : P.kinship i j ≤ 1 :=
  (kinship_mem_Icc P i j).2

theorem inbreeding_nonneg (P : Pedigree n) (i : Fin n) : 0 ≤ P.inbreeding i := by
  cases hi : P.parents i with
  | none => rw [inbreeding_founder P hi]
  | some p => rw [inbreeding_of_parents P hi]; exact kinship_nonneg P _ _

theorem inbreeding_le_one (P : Pedigree n) (i : Fin n) : P.inbreeding i ≤ 1 := by
  cases hi : P.parents i with
  | none => rw [inbreeding_founder P hi]; exact zero_le_one
  | some p => rw [inbreeding_of_parents P hi]; exact kinship_le_one P _ _

theorem kinship_founders (P : Pedigree n) {i j : Fin n} (hij : i ≠ j)
    (hi : P.parents i = none) (hj : P.parents j = none) : P.kinship i j = 0 := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact kinship_of_lt_founder P h hj
  · exact kinship_of_gt_founder P h hi

theorem inbreeding_selfed (P : Pedigree n) {i f : Fin n} (hi : P.parents i = some (f, f)) :
    P.inbreeding i = (1 + P.inbreeding f) / 2 := by
  rw [inbreeding_of_parents P hi, kinship_self]

theorem kinship_full_sibs (P : Pedigree n) {i j f m : Fin n} (hij : i ≠ j)
    (hi : P.parents i = some (f, m)) (hj : P.parents j = some (f, m)) :
    P.kinship i j = (2 + P.inbreeding f + P.inbreeding m + 4 * P.kinship f m) / 8 := by
  have key : ∀ {i j : Fin n}, i < j → P.parents i = some (f, m) →
      P.parents j = some (f, m) →
      P.kinship i j = (2 + P.inbreeding f + P.inbreeding m + 4 * P.kinship f m) / 8 := by
    intro i j hlt hi hj
    have hf := (P.parents_lt i (f, m) hi).1
    have hm := (P.parents_lt i (f, m) hi).2
    rw [kinship_of_lt P hlt hj]
    change (P.kinship i f + P.kinship i m) / 2 = _
    rw [kinship_of_gt P hf hi, kinship_of_gt P hm hi]
    change ((P.kinship f f + P.kinship m f) / 2 + (P.kinship f m + P.kinship m m) / 2) / 2 = _
    rw [kinship_self, kinship_self, kinship_comm P m f]
    ring
  rcases lt_or_gt_of_ne hij with h | h
  · exact key h hi hj
  · rw [kinship_comm]
    exact key h hj hi

theorem inbreeding_of_full_sib_parents (P : Pedigree n) {x i j f m : Fin n}
    (hx : P.parents x = some (i, j)) (hij : i ≠ j)
    (hi : P.parents i = some (f, m)) (hj : P.parents j = some (f, m)) :
    P.inbreeding x = (2 + P.inbreeding f + P.inbreeding m + 4 * P.inbreeding i) / 8 := by
  rw [inbreeding_of_parents P hx, inbreeding_of_parents P hi]
  exact kinship_full_sibs P hij hi hj

theorem inbreeding_full_sib_step (P : Pedigree n) {x i j f m : Fin n} {a : ℚ}
    (hx : P.parents x = some (i, j)) (hij : i ≠ j)
    (hi : P.parents i = some (f, m)) (hj : P.parents j = some (f, m))
    (hf : P.inbreeding f = a) (hm : P.inbreeding m = a) :
    ((P.inbreeding x : ℚ) : ℝ) =
      (Rhone.Dynamics.Inbreeding.fullSibStep ((a : ℝ), ((P.inbreeding i : ℚ) : ℝ))).2 := by
  rw [inbreeding_of_full_sib_parents P hx hij hi hj, hf, hm]
  simp only [Rhone.Dynamics.Inbreeding.fullSibStep]
  push_cast
  ring

def sibMating : Pedigree 5 where
  parents := ![none, none, some (0, 1), some (0, 1), some (2, 3)]
  parents_lt := by decide

def selfingLine : Pedigree 3 where
  parents := ![none, some (0, 0), some (1, 1)]
  parents_lt := by decide

theorem sibMating_kinship_sibs : sibMating.kinship 2 3 = 1 / 4 := by
  rw [kinship_full_sibs sibMating (f := 0) (m := 1) (by decide) rfl rfl,
    inbreeding_founder sibMating (i := 0) rfl, inbreeding_founder sibMating (i := 1) rfl,
    kinship_founders sibMating (i := 0) (j := 1) (by decide) rfl rfl]
  norm_num

theorem sibMating_inbreeding_offspring : sibMating.inbreeding 4 = 1 / 4 := by
  rw [inbreeding_of_parents sibMating (i := 4) (p := (2, 3)) rfl]
  exact sibMating_kinship_sibs

theorem sibMating_kinship_parent_offspring : sibMating.kinship 2 4 = 3 / 8 := by
  rw [kinship_of_lt sibMating (i := 2) (j := 4) (p := (2, 3)) (by decide) rfl]
  change (sibMating.kinship 2 2 + sibMating.kinship 2 3) / 2 = _
  rw [kinship_self, sibMating_kinship_sibs,
    inbreeding_of_parents sibMating (i := 2) (p := (0, 1)) rfl,
    kinship_founders sibMating (i := 0) (j := 1) (by decide) rfl rfl]
  norm_num

theorem selfingLine_inbreeding_one : selfingLine.inbreeding 1 = 1 / 2 := by
  rw [inbreeding_selfed selfingLine (i := 1) (f := 0) rfl,
    inbreeding_founder selfingLine (i := 0) rfl]
  norm_num

theorem selfingLine_inbreeding_two : selfingLine.inbreeding 2 = 3 / 4 := by
  rw [inbreeding_selfed selfingLine (i := 2) (f := 1) rfl, selfingLine_inbreeding_one]
  norm_num

end Rhone.Combinatorics.Pedigree
