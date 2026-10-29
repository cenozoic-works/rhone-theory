/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.Recursion.Finite
public import Rhone.LinearAlgebra.Recursion.Exist

/-! # General allele counts: definitions for allele lumping and for the Cramer form -/

@[expose] public section

namespace Rhone.LinearAlgebra.AlleleLumping

open Finset Recursion

variable {KA KB KA' KB' : ℕ}

def pushV {K K' : ℕ} (f : Fin K → Fin K') (v : Fin K → ℕ) : Fin K' → ℕ :=
  fun p => ∑ i with f i = p, v i

def pushM (fA : Fin KA → Fin KA') (fB : Fin KB → Fin KB') (m : Fin KA → Fin KB → ℕ) :
    Fin KA' → Fin KB' → ℕ :=
  fun p r => ∑ i with fA i = p, ∑ j with fB j = r, m i j

def push (fA : Fin KA → Fin KA') (fB : Fin KB → Fin KB') (ξ : Config KA KB) : Config KA' KB' :=
  ⟨pushV fA ξ.a, pushV fB ξ.b, pushM fA fB ξ.c⟩

def pushPi {F : Type*} [AddCommMonoid F] {K K' : ℕ} (f : Fin K → Fin K') (π : Fin K → F) :
    Fin K' → F :=
  fun p => ∑ i with f i = p, π i

def mult (ξ : Config KA KB) : ℕ :=
  Nat.multinomial univ ξ.a * Nat.multinomial univ ξ.b
    * Nat.multinomial univ (fun x : Fin KA × Fin KB => ξ.c x.1 x.2)

theorem sum_pushV {K K' : ℕ} (f : Fin K → Fin K') (v : Fin K → ℕ) :
    ∑ p, pushV f v p = ∑ i, v i :=
  Finset.sum_fiberwise univ f v

@[simp] theorem sumA_push (fA : Fin KA → Fin KA') (fB : Fin KB → Fin KB') (ξ : Config KA KB) :
    (push fA fB ξ).sumA = ξ.sumA :=
  sum_pushV fA ξ.a

@[simp] theorem sumB_push (fA : Fin KA → Fin KA') (fB : Fin KB → Fin KB') (ξ : Config KA KB) :
    (push fA fB ξ).sumB = ξ.sumB :=
  sum_pushV fB ξ.b

theorem cRow_push (fA : Fin KA → Fin KA') (fB : Fin KB → Fin KB') (ξ : Config KA KB)
    (p : Fin KA') : (push fA fB ξ).cRow p = ∑ i with fA i = p, ξ.cRow i := by
  simp only [Config.cRow, push, pushM]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_fiberwise univ fB (ξ.c i)

theorem cCol_push (fA : Fin KA → Fin KA') (fB : Fin KB → Fin KB') (ξ : Config KA KB)
    (r : Fin KB') : (push fA fB ξ).cCol r = ∑ j with fB j = r, ξ.cCol j := by
  simp only [Config.cCol, push, pushM]
  rw [Finset.sum_fiberwise univ fA (fun i => ∑ j with fB j = r, ξ.c i j), Finset.sum_comm]

@[simp] theorem t_push (fA : Fin KA → Fin KA') (fB : Fin KB → Fin KB') (ξ : Config KA KB) :
    (push fA fB ξ).t = ξ.t := by
  rw [Config.t_eq_sum_cRow, Config.t_eq_sum_cRow]
  simp only [cRow_push]
  exact Finset.sum_fiberwise univ fA ξ.cRow

@[simp] theorem nA_push (fA : Fin KA → Fin KA') (fB : Fin KB → Fin KB') (ξ : Config KA KB) :
    (push fA fB ξ).nA = ξ.nA := by
  simp [Config.nA]

@[simp] theorem nB_push (fA : Fin KA → Fin KA') (fB : Fin KB → Fin KB') (ξ : Config KA KB) :
    (push fA fB ξ).nB = ξ.nB := by
  simp [Config.nB]

@[simp] theorem n_push (fA : Fin KA → Fin KA') (fB : Fin KB → Fin KB') (ξ : Config KA KB) :
    (push fA fB ξ).n = ξ.n := by
  simp [Config.n]

noncomputable def fibre (fA : Fin KA → Fin KA') (fB : Fin KB → Fin KB') (η : Config KA' KB') :
    Finset (Config KA KB) :=
  open Classical in
  (Config.finite_le (η.nA + η.nB)).toFinset.filter fun ξ => push fA fB ξ = η

theorem mem_fibre {fA : Fin KA → Fin KA'} {fB : Fin KB → Fin KB'} {η : Config KA' KB'}
    {ξ : Config KA KB} : ξ ∈ fibre fA fB η ↔ push fA fB ξ = η := by
  classical
  simp only [fibre, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq,
    and_iff_right_iff_imp]
  rintro rfl
  simp

variable {F : Type*} [Field F]

abbrev Lev (KA KB N : ℕ) : Type := ↥{ξ : Config KA KB | ξ.nA + ξ.nB = N}

noncomputable instance instDecidableEqLev (N : ℕ) : DecidableEq (Lev KA KB N) :=
  Classical.decEq _

noncomputable def Tmat (θA θB ρ : F) (πA : Fin KA → F) (πB : Fin KB → F) (N : ℕ) :
    Matrix (Lev KA KB N) (Lev KA KB N) F :=
  LinearMap.toMatrix' (blockOp θA θB ρ πA πB N)

def below (N : ℕ) (q : Config KA KB → F) : Config KA KB → F :=
  fun η => if η.nA + η.nB < N then q η else 0

noncomputable def src (θA θB ρ : F) (πA : Fin KA → F) (πB : Fin KB → F) (q : Config KA KB → F)
    (N : ℕ) : Lev KA KB N → F :=
  fun ξ => if 2 ≤ (ξ : Config KA KB).n
    then rhs θA θB ρ πA πB (below N q) (ξ : Config KA KB)
    else Config.bdryVal πA πB (ξ : Config KA KB)

end Rhone.LinearAlgebra.AlleleLumping
