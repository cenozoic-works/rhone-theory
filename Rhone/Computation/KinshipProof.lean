/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.Kinship
public import Rhone.Dynamics.PedigreeKinship

/-! # Executable pedigree kinship equals the specification -/

@[expose] public section
namespace Rhone.Computation.Kinship
open Rhone.Combinatorics

def pedList {n : Nat} (P : Pedigree n) : Ped :=
  List.ofFn fun i => (P.parents i).map fun p => (p.1.val, p.2.val)

theorem parents_pedList {n : Nat} (P : Pedigree n) (i : Fin n) :
    parents (pedList P) i.val = (P.parents i).map fun p => (p.1.val, p.2.val) := by
  simp [parents, pedList]

theorem kinshipF_eq {n : Nat} (P : Pedigree n) (i j : Fin n) :
    ∀ f, i.val + j.val < f → kinshipF (pedList P) f i.val j.val = P.kinship i j := by
  refine Pedigree.pair_induction (motive := fun i j =>
    ∀ f, i.val + j.val < f → kinshipF (pedList P) f i.val j.val = P.kinship i j) ?_ i j
  intro i j ih f hf
  cases f with
  | zero => omega
  | succ f =>
    rcases lt_trichotomy i j with hij | rfl | hji
    · have hne : i.val ≠ j.val := fun h => hij.ne (Fin.ext h)
      have hlt : i.val < j.val := hij
      cases hj : P.parents j with
      | none =>
        rw [Pedigree.kinship_of_lt_founder P hij hj]
        simp [kinshipF, parents_pedList, hj, hne, hlt]
      | some p =>
        have hp := P.parents_lt j p hj
        have h1 := ih i p.1 (Nat.add_lt_add_left (Fin.lt_def.mp hp.1) _) f
          (by have := Fin.lt_def.mp hp.1; omega)
        have h2 := ih i p.2 (Nat.add_lt_add_left (Fin.lt_def.mp hp.2) _) f
          (by have := Fin.lt_def.mp hp.2; omega)
        rw [Pedigree.kinship_of_lt P hij hj, ← h1, ← h2]
        simp [kinshipF, parents_pedList, hj, hne, hlt]
    · cases hi : P.parents i with
      | none =>
        have h : P.kinship i i = 1 / 2 := by
          rw [Pedigree.kinship_self, Pedigree.inbreeding_founder P hi]; norm_num
        rw [h]
        simp [kinshipF, parents_pedList, hi]
      | some p =>
        have hp := P.parents_lt i p hi
        have h1 := ih p.1 p.2 (Nat.add_lt_add (Fin.lt_def.mp hp.1) (Fin.lt_def.mp hp.2)) f
          (by have := Fin.lt_def.mp hp.1; have := Fin.lt_def.mp hp.2; omega)
        rw [Pedigree.kinship_self, Pedigree.inbreeding_of_parents P hi, ← h1]
        simp [kinshipF, parents_pedList, hi]
    · have hne : i.val ≠ j.val := fun h => hji.ne (Fin.ext h.symm)
      have hlt : ¬ i.val < j.val := not_lt.2 (le_of_lt hji)
      cases hi : P.parents i with
      | none =>
        rw [Pedigree.kinship_of_gt_founder P hji hi]
        simp [kinshipF, parents_pedList, hi, hne, hlt]
      | some p =>
        have hp := P.parents_lt i p hi
        have h1 := ih p.1 j (Nat.add_lt_add_right (Fin.lt_def.mp hp.1) _) f
          (by have := Fin.lt_def.mp hp.1; omega)
        have h2 := ih p.2 j (Nat.add_lt_add_right (Fin.lt_def.mp hp.2) _) f
          (by have := Fin.lt_def.mp hp.2; omega)
        rw [Pedigree.kinship_of_gt P hji hi, ← h1, ← h2]
        simp [kinshipF, parents_pedList, hi, hne, hlt]

theorem kinship_eq {n : Nat} (P : Pedigree n) (i j : Fin n) :
    kinship (pedList P) i.val j.val = P.kinship i j :=
  kinshipF_eq P i j _ (by omega)

theorem inbreeding_eq {n : Nat} (P : Pedigree n) (i : Fin n) :
    inbreeding (pedList P) i.val = P.inbreeding i := by
  unfold inbreeding Pedigree.inbreeding
  rw [parents_pedList]
  cases hi : P.parents i with
  | none => rfl
  | some p => simpa using kinship_eq P p.1 p.2

theorem kinshipMatrix_getD {n : Nat} (P : Pedigree n) (i j : Fin n) :
    (((kinshipMatrix (pedList P) n).getD i []).getD j 0) = P.kinship i j := by
  simp [kinshipMatrix, List.getD_eq_getElem?_getD, kinship_eq]

example : kinship [none, none, some (0, 1), some (0, 1)] 2 3 = 1 / 4 ∧
    kinship [none, none, some (0, 1), some (0, 1)] 0 1 = 0 := by
  constructor <;> norm_num [kinship, kinshipF, parents]

end Rhone.Computation.Kinship
