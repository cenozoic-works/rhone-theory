/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.KilledSystem.Closure

/-! # The killed-PIM recursion as a finite linear system -/

@[expose] public section

namespace Rhone.Algebra.KilledSystem

open St

def rterms (s : St) : List (ℕ × ℕ × St) :=
  [
    (s.a0 * (s.a0 - 1 + 2 * s.cr0), 0, {s with a0 := s.a0 - 1}),
    (s.a1 * (s.a1 - 1 + 2 * s.cr1), 0, {s with a1 := s.a1 - 1}),
    (s.b0 * (s.b0 - 1 + 2 * s.cc0), 0, {s with b0 := s.b0 - 1}),
    (s.b1 * (s.b1 - 1 + 2 * s.cc1), 0, {s with b1 := s.b1 - 1}),
    (s.c00 * (s.c00 - 1), 0, {s with c00 := s.c00 - 1}),
    (s.c01 * (s.c01 - 1), 0, {s with c01 := s.c01 - 1}),
    (s.c10 * (s.c10 - 1), 0, {s with c10 := s.c10 - 1}),
    (s.c11 * (s.c11 - 1), 0, {s with c11 := s.c11 - 1}),
    (2 * s.a0 * s.b0, 0, {s with a0 := s.a0 - 1, b0 := s.b0 - 1, c00 := s.c00 + 1}),
    (2 * s.a0 * s.b1, 0, {s with a0 := s.a0 - 1, b1 := s.b1 - 1, c01 := s.c01 + 1}),
    (2 * s.a1 * s.b0, 0, {s with a1 := s.a1 - 1, b0 := s.b0 - 1, c10 := s.c10 + 1}),
    (2 * s.a1 * s.b1, 0, {s with a1 := s.a1 - 1, b1 := s.b1 - 1, c11 := s.c11 + 1}),
    (s.a0, 1, {s with a0 := s.a0 - 1}),
    (s.c00, 1, {s with b0 := s.b0 + 1, c00 := s.c00 - 1}),
    (s.c01, 1, {s with b1 := s.b1 + 1, c01 := s.c01 - 1}),
    (s.a1, 2, {s with a1 := s.a1 - 1}),
    (s.c10, 2, {s with b0 := s.b0 + 1, c10 := s.c10 - 1}),
    (s.c11, 2, {s with b1 := s.b1 + 1, c11 := s.c11 - 1}),
    (s.b0, 3, {s with b0 := s.b0 - 1}),
    (s.c00, 3, {s with a0 := s.a0 + 1, c00 := s.c00 - 1}),
    (s.c10, 3, {s with a1 := s.a1 + 1, c10 := s.c10 - 1}),
    (s.b1, 4, {s with b1 := s.b1 - 1}),
    (s.c01, 4, {s with a0 := s.a0 + 1, c01 := s.c01 - 1}),
    (s.c11, 4, {s with a1 := s.a1 + 1, c11 := s.c11 - 1}),
    (s.c00, 5, {s with a0 := s.a0 + 1, b0 := s.b0 + 1, c00 := s.c00 - 1}),
    (s.c01, 5, {s with a0 := s.a0 + 1, b1 := s.b1 + 1, c01 := s.c01 - 1}),
    (s.c10, 5, {s with a1 := s.a1 + 1, b0 := s.b0 + 1, c10 := s.c10 - 1}),
    (s.c11, 5, {s with a1 := s.a1 + 1, b1 := s.b1 + 1, c11 := s.c11 - 1}) ]

theorem recStates_targets_inClosure :
    ∀ s ∈ recStates, ∀ x ∈ rterms s, x.1 = 0 ∨ x.2.2.InClosure := by decide

theorem recStates_targets_mem :
    ∀ s ∈ recStates, ∀ x ∈ rterms s, x.1 = 0 ∨ x.2.2 ∈ closureList := fun s hs x hx =>
  (recStates_targets_inClosure s hs x hx).imp id mem_closureList_of_inClosure

section Ring

variable {R : Type*} [CommRing R]

def pfac (w0 w1 w2 w3 w4 w5 : R) : ℕ → R
  | 0 => w0
  | 1 => w1
  | 2 => w2
  | 3 => w3
  | 4 => w4
  | 5 => w5
  | _ => 0

def lhsC (tA tB r : R) (s : St) : R :=
  ((s.n * (s.n - 1) : ℕ) : R) + tA * (s.nA : ℕ) + tB * (s.nB : ℕ) + r * (s.t : ℕ)

def rhsC (w0 w1 w2 w3 w4 w5 : R) (q : St → R) (s : St) : R :=
  ((rterms s).map fun x => (x.1 : R) * pfac w0 w1 w2 w3 w4 w5 x.2.1 * q x.2.2).sum

def bdryC (pA0 pA1 pB0 pB1 : R) (s : St) : R :=
  if s = ⟨1, 0, 0, 0, 0, 0, 0, 0⟩ then pA0
  else if s = ⟨0, 1, 0, 0, 0, 0, 0, 0⟩ then pA1
  else if s = ⟨0, 0, 1, 0, 0, 0, 0, 0⟩ then pB0
  else if s = ⟨0, 0, 0, 1, 0, 0, 0, 0⟩ then pB1
  else if s = ⟨0, 0, 0, 0, 1, 0, 0, 0⟩ then pA0 * pB0
  else if s = ⟨0, 0, 0, 0, 0, 1, 0, 0⟩ then pA0 * pB1
  else if s = ⟨0, 0, 0, 0, 0, 0, 1, 0⟩ then pA1 * pB0
  else if s = ⟨0, 0, 0, 0, 0, 0, 0, 1⟩ then pA1 * pB1
  else 0

end Ring

section Transfer

variable {R R2 : Type*} [CommRing R] [CommRing R2]

theorem pfac_map (f : R →+* R2) (w0 w1 w2 w3 w4 w5 : R) (k : ℕ) :
    f (pfac w0 w1 w2 w3 w4 w5 k) = pfac (f w0) (f w1) (f w2) (f w3) (f w4) (f w5) k := by
  match k with
  | 0 => simp [pfac]
  | 1 => simp [pfac]
  | 2 => simp [pfac]
  | 3 => simp [pfac]
  | 4 => simp [pfac]
  | 5 => simp [pfac]
  | (k + 6) => simp [pfac]

theorem lhsC_map (f : R →+* R2) (tA tB r : R) (s : St) :
    f (lhsC tA tB r s) = lhsC (f tA) (f tB) (f r) s := by
  simp [lhsC]

theorem rhsC_map (f : R →+* R2) (w0 w1 w2 w3 w4 w5 : R) (q : St → R) (s : St) :
    f (rhsC w0 w1 w2 w3 w4 w5 q s)
      = rhsC (f w0) (f w1) (f w2) (f w3) (f w4) (f w5) (fun z => f (q z)) s := by
  simp only [rhsC, map_list_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun x _ => ?_
  simp [pfac_map f]

theorem bdryC_map (f : R →+* R2) (pA0 pA1 pB0 pB1 : R) (s : St) :
    f (bdryC pA0 pA1 pB0 pB1 s) = bdryC (f pA0) (f pA1) (f pB0) (f pB1) s := by
  unfold bdryC
  split_ifs <;> simp

end Transfer

section Linear

variable {R : Type*} [CommRing R]

theorem rhsC_scale (m w0 w1 w2 w3 w4 w5 : R) (q : St → R) (s : St) :
    rhsC (m * w0) (m * w1) (m * w2) (m * w3) (m * w4) (m * w5) q s
      = m * rhsC w0 w1 w2 w3 w4 w5 q s := by
  have hp : ∀ k : ℕ, pfac (m * w0) (m * w1) (m * w2) (m * w3) (m * w4) (m * w5) k
      = m * pfac w0 w1 w2 w3 w4 w5 k := by
    intro k
    match k with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | 3 => rfl
    | 4 => rfl
    | 5 => rfl
    | (k + 6) => simp [pfac]
  simp only [rhsC, ← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun x _ => ?_
  simp only [hp]
  ring

theorem rhsC_mul_const (w0 w1 w2 w3 w4 w5 : R) (q : St → R) (g : R) (s : St) :
    rhsC w0 w1 w2 w3 w4 w5 (fun z => q z * g) s = rhsC w0 w1 w2 w3 w4 w5 q s * g := by
  simp only [rhsC, ← List.sum_map_mul_right]
  congr 1
  refine List.map_congr_left fun x _ => ?_
  ring

theorem rhsC_sub (w0 w1 w2 w3 w4 w5 : R) (q q2 : St → R) (s : St) :
    rhsC w0 w1 w2 w3 w4 w5 q s - rhsC w0 w1 w2 w3 w4 w5 q2 s
      = rhsC w0 w1 w2 w3 w4 w5 (fun z => q z - q2 z) s := by
  simp only [rhsC]
  induction rterms s with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons, ← ih]; ring

end Linear

noncomputable def thAF : Fuv := (uu + vv) / 2
noncomputable def thBF : Fuv := (uu - vv) / 2
noncomputable def piA0F : Fuv := 1 / 3
noncomputable def piA1F : Fuv := 2 / 3
noncomputable def piB0F : Fuv := 2 / 5
noncomputable def piB1F : Fuv := 3 / 5

theorem thA_eq : thA = algebraMap Fuv L thAF := rfl
theorem thB_eq : thB = algebraMap Fuv L thBF := rfl

theorem uu_eq : uu = thAF + thBF := by rw [thAF, thBF]; ring
theorem vv_eq : vv = thAF - thBF := by rw [thAF, thBF]; ring

theorem thAF_add_one_ne_zero : thAF + 1 ≠ 0 := by
  have h : thAF + 1 = (uu + vv + 2) / 2 := by rw [thAF]; ring
  rw [h]
  exact div_ne_zero uu_add_vv_add_two_ne_zero (by norm_num)

theorem thBF_add_one_ne_zero : thBF + 1 ≠ 0 := by
  have h : thBF + 1 = (uu - vv + 2) / 2 := by rw [thBF]; ring
  rw [h]
  exact div_ne_zero uu_sub_vv_add_two_ne_zero (by norm_num)

theorem thAF_add_thBF_add_two_ne_zero : thAF + thBF + 2 ≠ 0 := by
  rw [← uu_eq]; exact uu_add_two_ne_zero

noncomputable def piA0 : L := 1 / 3
noncomputable def piA1 : L := 2 / 3
noncomputable def piB0 : L := 2 / 5
noncomputable def piB1 : L := 3 / 5

def IsSolution (q : St → L) : Prop :=
  (∀ s ∈ recStates, lhsC thA thB rhoL s * q s
      = rhsC 1 (thA * piA0) (thA * piA1) (thB * piB0) (thB * piB1) rhoL q s) ∧
  (∀ s ∈ bdryStates, q s = bdryC piA0 piA1 piB0 piB1 s)

end Rhone.Algebra.KilledSystem
