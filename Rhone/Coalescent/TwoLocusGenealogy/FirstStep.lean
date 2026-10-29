/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.TwoLocusGenealogy.Coal

/-! # The first-step analysis: `step` is the recursion's right-hand side -/

@[expose] public section

namespace Rhone.Coalescent.TwoLocusGenealogy

open Finset LinearAlgebra.Recursion

variable {n KA KB : ℕ} {σA : Fin n → Fin KA} {σB : Fin n → Fin KB}
variable {F : Type*} [Field F]

theorem sum_prod_pair {ι : Type*} [Fintype ι] (L : Finset (Lin n)) (A B : Lin n → ι → F)
    (X : ι → F) :
    (∑ p ∈ L, ∑ q ∈ L, ∑ i, A p i * B q i * X i)
      = ∑ i, (∑ p ∈ L, A p i) * (∑ q ∈ L, B q i) * X i := by
  have hinner : ∀ p, (∑ q ∈ L, ∑ i, A p i * B q i * X i)
      = ∑ i, ∑ q ∈ L, A p i * B q i * X i := fun _ => Finset.sum_comm
  simp only [hinner]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]

theorem sum_diag_pair {ι : Type*} [Fintype ι] (L : Finset (Lin n)) (A B : Lin n → ι → F)
    (X : ι → F) :
    (∑ p ∈ L, ∑ i, A p i * B p i * X i) = ∑ i, (∑ p ∈ L, A p i * B p i) * X i := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => (Finset.sum_mul _ _ _).symm

theorem sum_prod_pair2 (L : Finset (Lin n)) (A B : Lin n → Fin KA → Fin KB → F)
    (X : Fin KA → Fin KB → F) :
    (∑ p ∈ L, ∑ q ∈ L, ∑ i, ∑ j, A p i j * B q i j * X i j)
      = ∑ i, ∑ j, (∑ p ∈ L, A p i j) * (∑ q ∈ L, B q i j) * X i j := by
  have key := sum_prod_pair (ι := Fin KA × Fin KB) L (fun p ij => A p ij.1 ij.2)
    (fun q ij => B q ij.1 ij.2) (fun ij => X ij.1 ij.2)
  simpa [Fintype.sum_prod_type] using key

theorem sum_diag_pair2 (L : Finset (Lin n)) (A B : Lin n → Fin KA → Fin KB → F)
    (X : Fin KA → Fin KB → F) :
    (∑ p ∈ L, ∑ i, ∑ j, A p i j * B p i j * X i j)
      = ∑ i, ∑ j, (∑ p ∈ L, A p i j * B p i j) * X i j := by
  have key := sum_diag_pair (ι := Fin KA × Fin KB) L (fun p ij => A p ij.1 ij.2)
    (fun q ij => B q ij.1 ij.2) (fun ij => X ij.1 ij.2)
  simpa [Fintype.sum_prod_type] using key

theorem sum_erase_sub {L : Finset (Lin n)} {p : Lin n} (hp : p ∈ L) (H : Lin n → F) :
    ∑ q ∈ L.erase p, H q = (∑ q ∈ L, H q) - H p :=
  eq_sub_of_add_eq' (Finset.add_sum_erase L H hp)

theorem sum_offdiag (L : Finset (Lin n)) (H : Lin n → Lin n → F) :
    (∑ p ∈ L, ∑ q ∈ L.erase p, H p q) = (∑ p ∈ L, ∑ q ∈ L, H p q) - ∑ p ∈ L, H p p := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun p hp => sum_erase_sub hp (H p)

theorem uA_mul_uA (p : Lin n) (i : Fin KA) : uA σA p i * uA σA p i = uA σA p i := by
  simp only [uA]; split_ifs <;> simp

theorem uB_mul_uB (p : Lin n) (j : Fin KB) : uB σB p j * uB σB p j = uB σB p j := by
  simp only [uB]; split_ifs <;> simp

theorem uC_mul_uC (p : Lin n) (i : Fin KA) (j : Fin KB) :
    uC σA σB p i j * uC σA σB p i j = uC σA σB p i j := by
  simp only [uC]; split_ifs <;> simp

theorem uA_mul_uC (p : Lin n) (i : Fin KA) (j : Fin KB) :
    uA σA p i * uC σA σB p i j = 0 := by
  by_cases h : IsA σA i p
  · have hn : ¬ IsC σA σB i j p := fun hc => (Finset.nonempty_iff_ne_empty.1 hc.2.1) h.2.1
    simp [uC, hn]
  · simp [uA, h]

theorem uA_mul_uB (p : Lin n) (i : Fin KA) (j : Fin KB) : uA σA p i * uB σB p j = 0 := by
  by_cases h : IsA σA i p
  · have hn : ¬ IsB σB j p := fun hc => (Finset.nonempty_iff_ne_empty.1 h.1) hc.1
    simp [uB, hn]
  · simp [uA, h]

theorem uB_mul_uC (p : Lin n) (i : Fin KA) (j : Fin KB) :
    uB σB p j * uC σA σB p i j = 0 := by
  by_cases h : IsB σB j p
  · have hn : ¬ IsC σA σB i j p := fun hc => (Finset.nonempty_iff_ne_empty.1 hc.1) h.1
    simp [uC, hn]
  · simp [uB, h]

section BilSums

variable {L : Finset (Lin n)} {ξ : Config KA KB}
variable (hA : ∀ i, ∑ p ∈ L, ((uA σA p i : ℕ) : F) = ((ξ.a i : ℕ) : F))
variable (hB : ∀ j, ∑ p ∈ L, ((uB σB p j : ℕ) : F) = ((ξ.b j : ℕ) : F))
variable (hC : ∀ i j, ∑ p ∈ L, ((uC σA σB p i j : ℕ) : F) = ((ξ.c i j : ℕ) : F))

include hA hB hC

theorem bil_sum_prod (f : Config KA KB → F) :
    (∑ p ∈ L, ∑ q ∈ L, bil σA σB f ξ p q)
      = (∑ i, ((ξ.a i : ℕ) : F) * ((ξ.a i : ℕ) : F) * f (ξ.dropA i))
        + (∑ i, ∑ j, ((ξ.a i : ℕ) : F) * ((ξ.c i j : ℕ) : F) * f (ξ.dropA i))
        + (∑ i, ∑ j, ((ξ.c i j : ℕ) : F) * ((ξ.a i : ℕ) : F) * f (ξ.dropA i))
        + (∑ j, ((ξ.b j : ℕ) : F) * ((ξ.b j : ℕ) : F) * f (ξ.dropB j))
        + (∑ i, ∑ j, ((ξ.b j : ℕ) : F) * ((ξ.c i j : ℕ) : F) * f (ξ.dropB j))
        + (∑ i, ∑ j, ((ξ.c i j : ℕ) : F) * ((ξ.b j : ℕ) : F) * f (ξ.dropB j))
        + (∑ i, ∑ j, ((ξ.c i j : ℕ) : F) * ((ξ.c i j : ℕ) : F) * f (ξ.dropC i j))
        + (∑ i, ∑ j, ((ξ.a i : ℕ) : F) * ((ξ.b j : ℕ) : F) * f (ξ.mergeAB i j))
        + (∑ i, ∑ j, ((ξ.b j : ℕ) : F) * ((ξ.a i : ℕ) : F) * f (ξ.mergeAB i j)) := by
  simp only [bil, Finset.sum_add_distrib, sum_prod_pair, sum_prod_pair2, hA, hB, hC]

theorem bil_sum_diag (f : Config KA KB → F) :
    (∑ p ∈ L, bil σA σB f ξ p p)
      = (∑ i, ((ξ.a i : ℕ) : F) * f (ξ.dropA i))
        + (∑ j, ((ξ.b j : ℕ) : F) * f (ξ.dropB j))
        + (∑ i, ∑ j, ((ξ.c i j : ℕ) : F) * f (ξ.dropC i j)) := by
  have e1 : ∀ i : Fin KA, (∑ p ∈ L, ((uA σA p i : ℕ) : F) * ((uA σA p i : ℕ) : F))
      = ((ξ.a i : ℕ) : F) := by
    intro i
    rw [← hA i]
    exact Finset.sum_congr rfl fun p _ => by rw [← Nat.cast_mul, uA_mul_uA]
  have e2 : ∀ j : Fin KB, (∑ p ∈ L, ((uB σB p j : ℕ) : F) * ((uB σB p j : ℕ) : F))
      = ((ξ.b j : ℕ) : F) := by
    intro j
    rw [← hB j]
    exact Finset.sum_congr rfl fun p _ => by rw [← Nat.cast_mul, uB_mul_uB]
  have e3 : ∀ (i : Fin KA) (j : Fin KB),
      (∑ p ∈ L, ((uC σA σB p i j : ℕ) : F) * ((uC σA σB p i j : ℕ) : F))
        = ((ξ.c i j : ℕ) : F) := by
    intro i j
    rw [← hC i j]
    exact Finset.sum_congr rfl fun p _ => by rw [← Nat.cast_mul, uC_mul_uC]
  have z1 : ∀ (i : Fin KA) (j : Fin KB),
      (∑ p ∈ L, ((uA σA p i : ℕ) : F) * ((uC σA σB p i j : ℕ) : F)) = 0 :=
    fun i j => Finset.sum_eq_zero fun p _ => by rw [← Nat.cast_mul, uA_mul_uC]; simp
  have z2 : ∀ (i : Fin KA) (j : Fin KB),
      (∑ p ∈ L, ((uC σA σB p i j : ℕ) : F) * ((uA σA p i : ℕ) : F)) = 0 :=
    fun i j => Finset.sum_eq_zero fun p _ => by
      rw [← Nat.cast_mul, Nat.mul_comm, uA_mul_uC]; simp
  have z3 : ∀ (i : Fin KA) (j : Fin KB),
      (∑ p ∈ L, ((uB σB p j : ℕ) : F) * ((uC σA σB p i j : ℕ) : F)) = 0 :=
    fun i j => Finset.sum_eq_zero fun p _ => by rw [← Nat.cast_mul, uB_mul_uC]; simp
  have z4 : ∀ (i : Fin KA) (j : Fin KB),
      (∑ p ∈ L, ((uC σA σB p i j : ℕ) : F) * ((uB σB p j : ℕ) : F)) = 0 :=
    fun i j => Finset.sum_eq_zero fun p _ => by
      rw [← Nat.cast_mul, Nat.mul_comm, uB_mul_uC]; simp
  have z5 : ∀ (i : Fin KA) (j : Fin KB),
      (∑ p ∈ L, ((uA σA p i : ℕ) : F) * ((uB σB p j : ℕ) : F)) = 0 :=
    fun i j => Finset.sum_eq_zero fun p _ => by rw [← Nat.cast_mul, uA_mul_uB]; simp
  have z6 : ∀ (i : Fin KA) (j : Fin KB),
      (∑ p ∈ L, ((uB σB p j : ℕ) : F) * ((uA σA p i : ℕ) : F)) = 0 :=
    fun i j => Finset.sum_eq_zero fun p _ => by
      rw [← Nat.cast_mul, Nat.mul_comm, uA_mul_uB]; simp
  simp only [bil, Finset.sum_add_distrib, sum_diag_pair, sum_diag_pair2, e1, e2, e3,
    z1, z2, z3, z4, z5, z6, zero_mul, Finset.sum_const_zero, add_zero]

end BilSums

theorem nat_coalA_cast (a r : ℕ) :
    ((a * (a - 1 + 2 * r) : ℕ) : F) = (a : F) * (a : F) - (a : F) + 2 * ((a : F) * (r : F)) := by
  cases a with
  | zero => simp
  | succ k => simp only [Nat.add_sub_cancel]; push_cast; ring

theorem nat_coalC_cast (c : ℕ) : ((c * (c - 1) : ℕ) : F) = (c : F) * (c : F) - (c : F) := by
  cases c with
  | zero => simp
  | succ k => simp only [Nat.add_sub_cancel]; push_cast; ring

theorem cast_cRow (ξ : Config KA KB) (i : Fin KA) :
    ((ξ.cRow i : ℕ) : F) = ∑ j, ((ξ.c i j : ℕ) : F) := by
  rw [Config.cRow, Nat.cast_sum]

theorem cast_cCol (ξ : Config KA KB) (j : Fin KB) :
    ((ξ.cCol j : ℕ) : F) = ∑ i, ((ξ.c i j : ℕ) : F) := by
  rw [Config.cCol, Nat.cast_sum]

theorem coalA_line (ξ : Config KA KB) (f : Config KA KB → F) :
    (∑ i, ((ξ.a i : ℕ) : F) * ((ξ.a i : ℕ) : F) * f (ξ.dropA i))
      + (∑ i, ∑ j, ((ξ.a i : ℕ) : F) * ((ξ.c i j : ℕ) : F) * f (ξ.dropA i))
      + (∑ i, ∑ j, ((ξ.c i j : ℕ) : F) * ((ξ.a i : ℕ) : F) * f (ξ.dropA i))
      - (∑ i, ((ξ.a i : ℕ) : F) * f (ξ.dropA i))
    = ∑ i, ((ξ.coalA i : ℕ) : F) * f (ξ.dropA i) := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : (∑ j, ((ξ.a i : ℕ) : F) * ((ξ.c i j : ℕ) : F) * f (ξ.dropA i))
      = ((ξ.a i : ℕ) : F) * ((ξ.cRow i : ℕ) : F) * f (ξ.dropA i) := by
    rw [cast_cRow, Finset.mul_sum, Finset.sum_mul]
  have h2 : (∑ j, ((ξ.c i j : ℕ) : F) * ((ξ.a i : ℕ) : F) * f (ξ.dropA i))
      = ((ξ.cRow i : ℕ) : F) * ((ξ.a i : ℕ) : F) * f (ξ.dropA i) := by
    rw [cast_cRow, Finset.sum_mul, Finset.sum_mul]
  rw [h1, h2, Config.coalA, nat_coalA_cast]
  ring

theorem coalB_line (ξ : Config KA KB) (f : Config KA KB → F) :
    (∑ j, ((ξ.b j : ℕ) : F) * ((ξ.b j : ℕ) : F) * f (ξ.dropB j))
      + (∑ i, ∑ j, ((ξ.b j : ℕ) : F) * ((ξ.c i j : ℕ) : F) * f (ξ.dropB j))
      + (∑ i, ∑ j, ((ξ.c i j : ℕ) : F) * ((ξ.b j : ℕ) : F) * f (ξ.dropB j))
      - (∑ j, ((ξ.b j : ℕ) : F) * f (ξ.dropB j))
    = ∑ j, ((ξ.coalB j : ℕ) : F) * f (ξ.dropB j) := by
  have s1 : (∑ i, ∑ j, ((ξ.b j : ℕ) : F) * ((ξ.c i j : ℕ) : F) * f (ξ.dropB j))
      = ∑ j, ((ξ.b j : ℕ) : F) * ((ξ.cCol j : ℕ) : F) * f (ξ.dropB j) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [cast_cCol, Finset.mul_sum, Finset.sum_mul]
  have s2 : (∑ i, ∑ j, ((ξ.c i j : ℕ) : F) * ((ξ.b j : ℕ) : F) * f (ξ.dropB j))
      = ∑ j, ((ξ.cCol j : ℕ) : F) * ((ξ.b j : ℕ) : F) * f (ξ.dropB j) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [cast_cCol, Finset.sum_mul, Finset.sum_mul]
  rw [s1, s2, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Config.coalB, nat_coalA_cast]
  ring

theorem coalC_line (ξ : Config KA KB) (f : Config KA KB → F) :
    (∑ i, ∑ j, ((ξ.c i j : ℕ) : F) * ((ξ.c i j : ℕ) : F) * f (ξ.dropC i j))
      - (∑ i, ∑ j, ((ξ.c i j : ℕ) : F) * f (ξ.dropC i j))
    = ∑ i, ∑ j, ((ξ.coalC i j : ℕ) : F) * f (ξ.dropC i j) := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Config.coalC, nat_coalC_cast]
  ring

theorem coalAB_line (ξ : Config KA KB) (f : Config KA KB → F) :
    (∑ i, ∑ j, ((ξ.a i : ℕ) : F) * ((ξ.b j : ℕ) : F) * f (ξ.mergeAB i j))
      + (∑ i, ∑ j, ((ξ.b j : ℕ) : F) * ((ξ.a i : ℕ) : F) * f (ξ.mergeAB i j))
    = ∑ i, ∑ j, ((ξ.coalAB i j : ℕ) : F) * f (ξ.mergeAB i j) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Config.coalAB]
  push_cast
  ring

section Assemble

variable {L : Finset (Lin n)} {g : Finset (Lin n) → F} {f : Config KA KB → F}
variable {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}
variable (hgf : ∀ M, WF M → Clean σA σB M → g M = f (cfg σA σB M))
variable (hg0 : ∀ M, ¬ Clean σA σB M → g M = 0)

include hgf

theorem mutA_sum (hw : WF L) (hcl : Clean σA σB L) :
    (∑ p ∈ carA L, matchA σA πA p.1 * g (mutAL L p))
      = ∑ i, πA i * ((((cfg σA σB L).a i : ℕ) : F) * f ((cfg σA σB L).dropA i)
          + ∑ j, (((cfg σA σB L).c i j : ℕ) : F) * f ((cfg σA σB L).killA i j)) := by
  have hA : ∀ i, (∑ p ∈ carA L, ((uA σA p i : ℕ) : F)) = (((cfg σA σB L).a i : ℕ) : F) :=
    fun i => sum_uA_carA L i
  have hC : ∀ i j, (∑ p ∈ carA L, ((uC σA σB p i j : ℕ) : F))
      = (((cfg σA σB L).c i j : ℕ) : F) := fun i j => sum_uC_carA L i j
  rw [Finset.sum_congr rfl fun p hp => mutA_term hgf hw hcl hp, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul, hA i]
  congr 2
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => by rw [← Finset.sum_mul, hC i j]

theorem mutB_sum (hw : WF L) (hcl : Clean σA σB L) :
    (∑ p ∈ carB L, matchB σB πB p.2 * g (mutBL L p))
      = ∑ j, πB j * ((((cfg σA σB L).b j : ℕ) : F) * f ((cfg σA σB L).dropB j)
          + ∑ i, (((cfg σA σB L).c i j : ℕ) : F) * f ((cfg σA σB L).killB i j)) := by
  have hB : ∀ j, (∑ p ∈ carB L, ((uB σB p j : ℕ) : F)) = (((cfg σA σB L).b j : ℕ) : F) :=
    fun j => sum_uB_carB L j
  have hC : ∀ i j, (∑ p ∈ carB L, ((uC σA σB p i j : ℕ) : F))
      = (((cfg σA σB L).c i j : ℕ) : F) := fun i j => sum_uC_carB L i j
  rw [Finset.sum_congr rfl fun p hp => mutB_term hgf hw hcl hp, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul, hB j]
  congr 2
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => by rw [← Finset.sum_mul, hC i j]

theorem rec_sum (hw : WF L) (hcl : Clean σA σB L) :
    (∑ p ∈ carC L, g (recL L p))
      = ∑ i, ∑ j, (((cfg σA σB L).c i j : ℕ) : F) * f ((cfg σA σB L).split i j) := by
  have hC : ∀ i j, (∑ p ∈ carC L, ((uC σA σB p i j : ℕ) : F))
      = (((cfg σA σB L).c i j : ℕ) : F) := fun i j => sum_uC_carC L i j
  rw [Finset.sum_congr rfl fun p hp => rec_term hgf hw hcl hp, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => by rw [← Finset.sum_mul, hC i j]

include hg0

theorem coal_sum (hw : WF L) (hcl : Clean σA σB L) :
    (∑ p ∈ L, ∑ q ∈ L.erase p, g (coalL L p q))
      = (∑ i, (((cfg σA σB L).coalA i : ℕ) : F) * f ((cfg σA σB L).dropA i))
        + (∑ j, (((cfg σA σB L).coalB j : ℕ) : F) * f ((cfg σA σB L).dropB j))
        + (∑ i, ∑ j, (((cfg σA σB L).coalC i j : ℕ) : F) * f ((cfg σA σB L).dropC i j))
        + (∑ i, ∑ j, (((cfg σA σB L).coalAB i j : ℕ) : F)
            * f ((cfg σA σB L).mergeAB i j)) := by
  have hA : ∀ i, (∑ p ∈ L, ((uA σA p i : ℕ) : F)) = (((cfg σA σB L).a i : ℕ) : F) :=
    fun i => (cast_cfgA L i).symm
  have hB : ∀ j, (∑ p ∈ L, ((uB σB p j : ℕ) : F)) = (((cfg σA σB L).b j : ℕ) : F) :=
    fun j => (cast_cfgB L j).symm
  have hC : ∀ i j, (∑ p ∈ L, ((uC σA σB p i j : ℕ) : F))
      = (((cfg σA σB L).c i j : ℕ) : F) := fun i j => (cast_cfgC L i j).symm
  have hterm : (∑ p ∈ L, ∑ q ∈ L.erase p, g (coalL L p q))
      = ∑ p ∈ L, ∑ q ∈ L.erase p, bil σA σB f (cfg σA σB L) p q :=
    Finset.sum_congr rfl fun p hp =>
      Finset.sum_congr rfl fun q hq => coal_term hgf hg0 hw hcl hp hq
  rw [hterm, sum_offdiag, bil_sum_prod hA hB hC f, bil_sum_diag hA hB hC f,
    ← coalA_line (cfg σA σB L) f, ← coalB_line (cfg σA σB L) f,
    ← coalC_line (cfg σA σB L) f, ← coalAB_line (cfg σA σB L) f]
  ring

theorem step_eq_rhs (hw : WF L) (hcl : Clean σA σB L) :
    step σA σB θA θB ρ πA πB g L = LinearAlgebra.Recursion.rhs θA θB ρ πA πB f (cfg σA σB L) := by
  rw [step, LinearAlgebra.Recursion.rhs, coal_sum hgf hg0 hw hcl, mutA_sum hgf hw hcl,
    mutB_sum hgf hw hcl, rec_sum hgf hw hcl]

end Assemble

end Rhone.Coalescent.TwoLocusGenealogy
