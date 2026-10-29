/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.Denominator.Insert

/-! # Commuting the recursion past an inserted A-slot -/

@[expose] public section

namespace Rhone.Probability.Denominator

open Finset LinearAlgebra.Recursion

variable {KA KB : ℕ} {F : Type*} [CommRing F]
variable (θA θB ρ : F) (πA : Fin KA → F) (πB : Fin KB → F)

def sumAddA (f : Config KA KB → F) (ξ : Config KA KB) : F := ∑ i, f (addA ξ i)

def sumUp (f : Config KA KB → F) (j : Fin KB) (ξ : Config KA KB) : F := ∑ i, f (up ξ i j)

theorem sum_dropA_addA (f : Config KA KB → F) (ξ : Config KA KB) (u v : Fin KA → F)
    (hu : ∀ k : Fin KA, ξ.a k = 0 → u k = 0) :
    (∑ i, ∑ k, (if i = k then v k else u k) * f ((addA ξ i).dropA k))
      = (∑ k, u k * sumAddA f (ξ.dropA k)) + ∑ k, (v k - u k) * f ξ := by
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hoff : ∀ i ∈ Finset.univ.erase k,
      (if i = k then v k else u k) * f ((addA ξ i).dropA k) = u k * f (addA (ξ.dropA k) i) := by
    intro i hi
    have hik : i ≠ k := (Finset.mem_erase.mp hi).1
    rw [ite_eq_right hik, dropA_addA_of_ne ξ i k (Ne.symm hik)]
  have hlast : u k * f (addA (ξ.dropA k) k) = u k * f ξ := by
    by_cases ha : ξ.a k = 0
    · rw [hu k ha]; ring
    · rw [show addA (ξ.dropA k) k = ξ from Config.ext (incf_decf_self ha) rfl rfl]
  have expand : (∑ i, (if i = k then v k else u k) * f ((addA ξ i).dropA k))
      = v k * f ξ + ∑ i ∈ Finset.univ.erase k, u k * f (addA (ξ.dropA k) i) := by
    rw [← Finset.add_sum_erase _
      (fun i => (if i = k then v k else u k) * f ((addA ξ i).dropA k)) (Finset.mem_univ k),
      Finset.sum_congr rfl hoff]
    simp [dropA_addA_self]
  have expand2 : u k * sumAddA f (ξ.dropA k)
      = u k * f ξ + ∑ i ∈ Finset.univ.erase k, u k * f (addA (ξ.dropA k) i) := by
    rw [sumAddA, ← Finset.add_sum_erase _ (fun i => f (addA (ξ.dropA k) i)) (Finset.mem_univ k),
      mul_add, hlast, Finset.mul_sum]
  rw [expand, expand2]; ring

theorem sum_mergeAB_addA (f : Config KA KB → F) (ξ : Config KA KB)
    (u v : Fin KA → Fin KB → F) (hu : ∀ (k : Fin KA) (l : Fin KB), ξ.a k = 0 → u k l = 0) :
    (∑ i, ∑ k, ∑ l, (if i = k then v k l else u k l) * f ((addA ξ i).mergeAB k l))
      = (∑ k, ∑ l, u k l * sumAddA f (ξ.mergeAB k l))
        + ∑ k, ∑ l, (v k l - u k l) * f (up ξ k l) := by
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hoff : ∀ i ∈ Finset.univ.erase k,
      (if i = k then v k l else u k l) * f ((addA ξ i).mergeAB k l)
        = u k l * f (addA (ξ.mergeAB k l) i) := by
    intro i hi
    have hik : i ≠ k := (Finset.mem_erase.mp hi).1
    rw [ite_eq_right hik, mergeAB_addA_of_ne ξ i k l (Ne.symm hik)]
  have hlast : u k l * f (addA (ξ.mergeAB k l) k) = u k l * f (up ξ k l) := by
    by_cases ha : ξ.a k = 0
    · rw [hu k l ha]; ring
    · rw [show addA (ξ.mergeAB k l) k = up ξ k l from
        Config.ext (incf_decf_self ha) rfl rfl]
  have expand : (∑ i, (if i = k then v k l else u k l) * f ((addA ξ i).mergeAB k l))
      = v k l * f (up ξ k l) + ∑ i ∈ Finset.univ.erase k, u k l * f (addA (ξ.mergeAB k l) i) := by
    rw [← Finset.add_sum_erase _
      (fun i => (if i = k then v k l else u k l) * f ((addA ξ i).mergeAB k l))
      (Finset.mem_univ k), Finset.sum_congr rfl hoff]
    simp [mergeAB_addA_self]
  have expand2 : u k l * sumAddA f (ξ.mergeAB k l)
      = u k l * f (up ξ k l)
        + ∑ i ∈ Finset.univ.erase k, u k l * f (addA (ξ.mergeAB k l) i) := by
    rw [sumAddA, ← Finset.add_sum_erase _ (fun i => f (addA (ξ.mergeAB k l) i))
      (Finset.mem_univ k), mul_add, hlast, Finset.mul_sum]
  rw [expand, expand2]; ring

theorem sum_addA_const {ι : Type*} [Fintype ι] (f : Config KA KB → F) (w : ι → F)
    (T : ι → Config KA KB) :
    (∑ i : Fin KA, ∑ x : ι, w x * f (addA (T x) i)) = ∑ x : ι, w x * sumAddA f (T x) := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => by rw [sumAddA, Finset.mul_sum]

theorem coalA_addA (ξ : Config KA KB) (i k : Fin KA) :
    (addA ξ i).coalA k
      = if i = k then (ξ.a k + 1) * (ξ.a k + 2 * ξ.cRow k) else ξ.coalA k := by
  by_cases h : i = k
  · subst h
    simp [Config.coalA, incf_self]
  · rw [ite_eq_right h]
    simp only [Config.coalA, a_addA, cRow_addA, incf_of_ne _ (Ne.symm h)]

theorem a_addA_apply (ξ : Config KA KB) (i k : Fin KA) :
    (addA ξ i).a k = if i = k then ξ.a k + 1 else ξ.a k := by
  by_cases h : i = k
  · subst h; simp [incf_self]
  · simp [incf_of_ne _ (Ne.symm h), h]

theorem coalAB_addA (ξ : Config KA KB) (i k : Fin KA) (l : Fin KB) :
    (addA ξ i).coalAB k l
      = if i = k then 2 * ((ξ.a k + 1) * ξ.b l) else ξ.coalAB k l := by
  simp only [Config.coalAB, a_addA_apply, b_addA]
  split_ifs <;> rfl

@[simp] theorem coalB_addA (ξ : Config KA KB) (i : Fin KA) (l : Fin KB) :
    (addA ξ i).coalB l = ξ.coalB l := rfl

@[simp] theorem coalC_addA (ξ : Config KA KB) (i k : Fin KA) (l : Fin KB) :
    (addA ξ i).coalC k l = ξ.coalC k l := rfl

theorem sum_pi_add (π : Fin KA → F) (g h : Fin KA → F) :
    (∑ k, π k * (g k + h k)) = (∑ k, π k * g k) + ∑ k, π k * h k := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem sum_pi_addB (π : Fin KB → F) (g h : Fin KB → F) :
    (∑ l, π l * (g l + h l)) = (∑ l, π l * g l) + ∑ l, π l * h l := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem sum_addA_const2 (f : Config KA KB -> F) (w : Fin KA -> Fin KB -> F)
    (T : Fin KA -> Fin KB -> Config KA KB) :
    (∑ i : Fin KA, ∑ k, ∑ l, w k l * f (addA (T k l) i))
      = ∑ k, ∑ l, w k l * sumAddA f (T k l) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => by rw [sumAddA, Finset.mul_sum]

theorem sum_rhs_addA (f : Config KA KB -> F) (ξ : Config KA KB) :
    (∑ i, rhs θA θB ρ πA πB f (addA ξ i))
      = rhs θA θB ρ πA πB (sumAddA f) ξ
        + (((2 * ξ.nA : ℕ) : F) + θA * ∑ k, πA k) * f ξ
        + 2 * ∑ l, ((ξ.b l : ℕ) : F) * sumUp f l ξ := by
  have hnA : (∑ k, (2 * ξ.a k + 2 * ξ.cRow k)) = 2 * ξ.nA := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [Config.nA, Config.sumA, Config.t_eq_sum_cRow]
    ring
  have hterm : ∀ k : Fin KA,
      (((ξ.a k + 1) * (ξ.a k + 2 * ξ.cRow k) : ℕ) : F) - ((ξ.coalA k : ℕ) : F)
        = ((2 * ξ.a k + 2 * ξ.cRow k : ℕ) : F) := by
    intro k
    have hn : ξ.coalA k + (2 * ξ.a k + 2 * ξ.cRow k)
        = (ξ.a k + 1) * (ξ.a k + 2 * ξ.cRow k) := by
      simp only [Config.coalA]
      rcases Nat.eq_zero_or_pos (ξ.a k) with h | h
      · rw [h]; ring
      · obtain ⟨p, hp⟩ : ∃ p, ξ.a k = p + 1 := ⟨ξ.a k - 1, by omega⟩
        rw [hp]; simp only [Nat.add_sub_cancel]; ring
    have hcast : ((ξ.coalA k : ℕ) : F) + ((2 * ξ.a k + 2 * ξ.cRow k : ℕ) : F)
        = (((ξ.a k + 1) * (ξ.a k + 2 * ξ.cRow k) : ℕ) : F) := by
      rw [← Nat.cast_add, hn]
    linear_combination hcast.symm
  have G1 : (∑ i, ∑ k, (((addA ξ i).coalA k : ℕ) : F) * f ((addA ξ i).dropA k))
      = (∑ k, ((ξ.coalA k : ℕ) : F) * sumAddA f (ξ.dropA k))
        + ((2 * ξ.nA : ℕ) : F) * f ξ := by
    have hco : ∀ i k : Fin KA, (((addA ξ i).coalA k : ℕ) : F)
        = if i = k then (((ξ.a k + 1) * (ξ.a k + 2 * ξ.cRow k) : ℕ) : F)
          else ((ξ.coalA k : ℕ) : F) := by
      intro i k; rw [coalA_addA]; split_ifs <;> rfl
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
      Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) => by rw [hco i k]]
    rw [sum_dropA_addA f ξ (fun k => ((ξ.coalA k : ℕ) : F))
      (fun k => (((ξ.a k + 1) * (ξ.a k + 2 * ξ.cRow k) : ℕ) : F))
      (fun k hk => by rw [ξ.coalA_eq_zero_of hk]; simp)]
    have hcorr : (∑ k, ((((ξ.a k + 1) * (ξ.a k + 2 * ξ.cRow k) : ℕ) : F)
        - ((ξ.coalA k : ℕ) : F))) = ((2 * ξ.nA : ℕ) : F) := by
      rw [← hnA, Nat.cast_sum]
      exact Finset.sum_congr rfl fun k _ => hterm k
    rw [← Finset.sum_mul, hcorr]
  have G2 : (∑ i, ∑ l, (((addA ξ i).coalB l : ℕ) : F) * f ((addA ξ i).dropB l))
      = ∑ l, ((ξ.coalB l : ℕ) : F) * sumAddA f (ξ.dropB l) :=
    sum_addA_const f (fun l => ((ξ.coalB l : ℕ) : F)) (fun l => ξ.dropB l)
  have G3 : (∑ i, ∑ k, ∑ l, (((addA ξ i).coalC k l : ℕ) : F)
        * f ((addA ξ i).dropC k l))
      = ∑ k, ∑ l, ((ξ.coalC k l : ℕ) : F) * sumAddA f (ξ.dropC k l) :=
    sum_addA_const2 f (fun k l => ((ξ.coalC k l : ℕ) : F)) (fun k l => ξ.dropC k l)
  have G4 : (∑ i, ∑ k, ∑ l, (((addA ξ i).coalAB k l : ℕ) : F)
        * f ((addA ξ i).mergeAB k l))
      = (∑ k, ∑ l, ((ξ.coalAB k l : ℕ) : F) * sumAddA f (ξ.mergeAB k l))
        + 2 * ∑ l, ((ξ.b l : ℕ) : F) * sumUp f l ξ := by
    have hco : ∀ (i k : Fin KA) (l : Fin KB), (((addA ξ i).coalAB k l : ℕ) : F)
        = if i = k then ((2 * ((ξ.a k + 1) * ξ.b l) : ℕ) : F)
          else ((ξ.coalAB k l : ℕ) : F) := by
      intro i k l; rw [coalAB_addA]; split_ifs <;> rfl
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
      Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) =>
        Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) => by rw [hco i k l]]
    rw [sum_mergeAB_addA f ξ (fun k l => ((ξ.coalAB k l : ℕ) : F))
      (fun k l => ((2 * ((ξ.a k + 1) * ξ.b l) : ℕ) : F))
      (fun k l hk => by rw [ξ.coalAB_eq_zero_left l hk]; simp)]
    have hdiff : ∀ (k : Fin KA) (l : Fin KB),
        ((2 * ((ξ.a k + 1) * ξ.b l) : ℕ) : F) - ((ξ.coalAB k l : ℕ) : F)
          = 2 * ((ξ.b l : ℕ) : F) := by
      intro k l
      have hn : ξ.coalAB k l + 2 * ξ.b l = 2 * ((ξ.a k + 1) * ξ.b l) := by
        simp only [Config.coalAB]; ring
      have hcast : ((ξ.coalAB k l : ℕ) : F) + ((2 * ξ.b l : ℕ) : F)
          = ((2 * ((ξ.a k + 1) * ξ.b l) : ℕ) : F) := by rw [← Nat.cast_add, hn]
      push_cast at hcast ⊢
      linear_combination hcast.symm
    have hsecond : (∑ k, ∑ l, (((2 * ((ξ.a k + 1) * ξ.b l) : ℕ) : F)
          - ((ξ.coalAB k l : ℕ) : F)) * f (up ξ k l))
        = 2 * ∑ l, ((ξ.b l : ℕ) : F) * sumUp f l ξ := by
      rw [Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) =>
        Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) => by rw [hdiff k l]]
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [sumUp, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hsecond]
  have G5 : (∑ i, θA * ∑ k, πA k * ((((addA ξ i).a k : ℕ) : F)
        * f ((addA ξ i).dropA k)
        + ∑ l, (((addA ξ i).c k l : ℕ) : F) * f ((addA ξ i).killA k l)))
      = θA * ∑ k, πA k * (((ξ.a k : ℕ) : F) * sumAddA f (ξ.dropA k)
          + ∑ l, ((ξ.c k l : ℕ) : F) * sumAddA f (ξ.killA k l))
        + θA * (∑ k, πA k) * f ξ := by
    rw [← Finset.mul_sum]
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
      sum_pi_add πA (fun k => (((addA ξ i).a k : ℕ) : F) * f ((addA ξ i).dropA k))
        (fun k => ∑ l, (((addA ξ i).c k l : ℕ) : F) * f ((addA ξ i).killA k l))]
    rw [Finset.sum_add_distrib]
    have P1 : (∑ i, ∑ k, πA k * ((((addA ξ i).a k : ℕ) : F)
          * f ((addA ξ i).dropA k)))
        = (∑ k, πA k * (((ξ.a k : ℕ) : F) * sumAddA f (ξ.dropA k)))
          + (∑ k, πA k) * f ξ := by
      have hco : ∀ i k : Fin KA,
          πA k * ((((addA ξ i).a k : ℕ) : F) * f ((addA ξ i).dropA k))
          = (if i = k then πA k * (((ξ.a k + 1 : ℕ)) : F) else πA k * ((ξ.a k : ℕ) : F))
            * f ((addA ξ i).dropA k) := by
        intro i k
        rw [a_addA_apply]
        split_ifs <;> ring
      rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
        Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) => hco i k]
      rw [sum_dropA_addA f ξ (fun k => πA k * ((ξ.a k : ℕ) : F))
        (fun k => πA k * (((ξ.a k + 1 : ℕ)) : F))
        (fun k hk => by rw [hk]; simp)]
      have hcorr : (∑ k, (πA k * (((ξ.a k + 1 : ℕ)) : F) - πA k * ((ξ.a k : ℕ) : F)))
          = ∑ k, πA k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        push_cast
        ring
      rw [← Finset.sum_mul, hcorr]
      exact congrArg (· + (∑ k, πA k) * f ξ)
        (Finset.sum_congr rfl fun k _ => by rw [mul_assoc])
    have P2 : (∑ i, ∑ k, πA k * ∑ l, (((addA ξ i).c k l : ℕ) : F)
          * f ((addA ξ i).killA k l))
        = ∑ k, πA k * ∑ l, ((ξ.c k l : ℕ) : F) * sumAddA f (ξ.killA k l) := by
      have hstep : ∀ (i k : Fin KA), πA k * ∑ l, (((addA ξ i).c k l : ℕ) : F)
            * f ((addA ξ i).killA k l)
          = ∑ l, (πA k * ((ξ.c k l : ℕ) : F)) * f (addA (ξ.killA k l) i) := by
        intro i k
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by rw [c_addA, killA_addA]; ring
      rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
        Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) => hstep i k]
      rw [sum_addA_const2 f (fun k l => πA k * ((ξ.c k l : ℕ) : F))
        (fun k l => ξ.killA k l)]
      exact Finset.sum_congr rfl fun k _ => by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by ring
    rw [P1, P2, sum_pi_add πA (fun k => ((ξ.a k : ℕ) : F) * sumAddA f (ξ.dropA k))
      (fun k => ∑ l, ((ξ.c k l : ℕ) : F) * sumAddA f (ξ.killA k l))]
    ring
  have G6 : (∑ i, θB * ∑ l, πB l * ((((addA ξ i).b l : ℕ) : F)
        * f ((addA ξ i).dropB l)
        + ∑ k, (((addA ξ i).c k l : ℕ) : F) * f ((addA ξ i).killB k l)))
      = θB * ∑ l, πB l * (((ξ.b l : ℕ) : F) * sumAddA f (ξ.dropB l)
          + ∑ k, ((ξ.c k l : ℕ) : F) * sumAddA f (ξ.killB k l)) := by
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
      sum_pi_addB πB (fun l => (((addA ξ i).b l : ℕ) : F) * f ((addA ξ i).dropB l))
        (fun l => ∑ k, (((addA ξ i).c k l : ℕ) : F) * f ((addA ξ i).killB k l))]
    rw [Finset.sum_add_distrib,
      sum_pi_addB πB (fun l => ((ξ.b l : ℕ) : F) * sumAddA f (ξ.dropB l))
        (fun l => ∑ k, ((ξ.c k l : ℕ) : F) * sumAddA f (ξ.killB k l))]
    congr 1
    · have hstep : ∀ (i : Fin KA) (l : Fin KB),
          πB l * ((((addA ξ i).b l : ℕ) : F) * f ((addA ξ i).dropB l))
            = (πB l * ((ξ.b l : ℕ) : F)) * f (addA (ξ.dropB l) i) := fun i l => by
        rw [b_addA, dropB_addA]; ring
      rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
        Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) => hstep i l]
      rw [sum_addA_const f (fun l => πB l * ((ξ.b l : ℕ) : F)) (fun l => ξ.dropB l)]
      exact Finset.sum_congr rfl fun l _ => by rw [mul_assoc]
    · have hstep : ∀ (i : Fin KA) (l : Fin KB),
          πB l * ∑ k, (((addA ξ i).c k l : ℕ) : F) * f ((addA ξ i).killB k l)
            = ∑ k, (πB l * ((ξ.c k l : ℕ) : F)) * f (addA (ξ.killB k l) i) := fun i l => by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by rw [c_addA, killB_addA]; ring
      rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
        Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) => hstep i l]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.mul_sum, Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [sumAddA, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
  have G7 : (∑ i, ρ * ∑ k, ∑ l, (((addA ξ i).c k l : ℕ) : F)
        * f ((addA ξ i).split k l))
      = ρ * ∑ k, ∑ l, ((ξ.c k l : ℕ) : F) * sumAddA f (ξ.split k l) := by
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
      Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) =>
        Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) => by rw [c_addA, split_addA]]
    exact sum_addA_const2 f (fun k l => ((ξ.c k l : ℕ) : F)) (fun k l => ξ.split k l)
  simp only [rhs]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    G1, G2, G3, G4, G5, G6, G7]
  ring

end Rhone.Probability.Denominator
