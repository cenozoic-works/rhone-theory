/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.Denominator.Commute

/-! # Commuting the recursion past an upgraded B-slot -/

@[expose] public section

namespace Rhone.Probability.Denominator

open Finset LinearAlgebra.Recursion

variable {KA KB : ℕ} {F : Type*} [CommRing F]
variable (θA θB ρ : F) (πA : Fin KA → F) (πB : Fin KB → F)

theorem incC_decC_self {m : Fin KA → Fin KB → ℕ} {i : Fin KA} {j : Fin KB} (h : m i j ≠ 0) :
    Config.incC (Config.decC m i j) i j = m := by
  funext x y
  simp only [incC_apply, decC_apply]
  by_cases h1 : x = i <;> by_cases h2 : y = j <;> simp_all
  omega

theorem up_dropC_self {ξ : Config KA KB} {i : Fin KA} {j : Fin KB} (h : ξ.c i j ≠ 0) :
    up (ξ.dropC i j) i j = ξ.dropB j :=
  Config.ext rfl rfl (by simp [up, Config.dropC, Config.dropB, incC_decC_self h])

theorem up_killA_self {ξ : Config KA KB} {i : Fin KA} {j : Fin KB} (h : ξ.c i j ≠ 0) :
    up (ξ.killA i j) i j = ξ :=
  Config.ext rfl (by simp [up, Config.killA]) (by simp [up, Config.killA, incC_decC_self h])

theorem up_killB_self {ξ : Config KA KB} {i : Fin KA} {j : Fin KB} (h : ξ.c i j ≠ 0) :
    up (ξ.killB i j) i j = addA (ξ.dropB j) i :=
  Config.ext rfl rfl (by simp [up, Config.killB, addA, Config.dropB, incC_decC_self h])

theorem up_split_self {ξ : Config KA KB} {i : Fin KA} {j : Fin KB} (h : ξ.c i j ≠ 0) :
    up (ξ.split i j) i j = addA ξ i :=
  Config.ext rfl (by simp [up, Config.split, addA])
    (by simp [up, Config.split, addA, incC_decC_self h])

theorem up_dropA_self (ξ : Config KA KB) (k : Fin KA) (j : Fin KB) :
    up (ξ.dropA k) k j = ξ.mergeAB k j := rfl

section Coeff

variable (ξ : Config KA KB) (i k : Fin KA) (j l : Fin KB)

theorem cRow_up_self : (up ξ i j).cRow i = ξ.cRow i + 1 := by
  have := cRow_up ξ i j i
  simpa using this

theorem cRow_up_of_ne (h : k ≠ i) : (up ξ i j).cRow k = ξ.cRow k := by
  have := cRow_up ξ i j k
  simpa [h] using this

theorem cCol_up_self : (up ξ i j).cCol j = ξ.cCol j + 1 := by
  have := cCol_up ξ i j j
  simpa using this

theorem cCol_up_of_ne (h : l ≠ j) : (up ξ i j).cCol l = ξ.cCol l := by
  have := cCol_up ξ i j l
  simpa [h] using this

theorem b_up_self (hb : ξ.b j ≠ 0) : (up ξ i j).b j + 1 = ξ.b j := by
  simp only [b_up, decf_self]
  omega

theorem b_up_of_ne (h : l ≠ j) : (up ξ i j).b l = ξ.b l := by
  simp [decf_of_ne _ h]

theorem c_up_self : (up ξ i j).c i j = ξ.c i j + 1 := by
  simp [incC_apply]

theorem c_up_of_ne (h : ¬(k = i ∧ l = j)) : (up ξ i j).c k l = ξ.c k l := by
  simp only [c_up, incC_apply]
  by_cases hk : k = i <;> by_cases hl : l = j <;> simp_all

theorem coalA_up_self : (up ξ i j).coalA i = ξ.coalA i + 2 * ξ.a i := by
  simp only [Config.coalA, a_up, cRow_up_self]
  generalize ξ.a i - 1 = d
  ring

theorem coalA_up_of_ne (h : k ≠ i) : (up ξ i j).coalA k = ξ.coalA k := by
  simp only [Config.coalA, a_up, cRow_up_of_ne ξ i k j h]

theorem coalB_up_self (hb : ξ.b j ≠ 0) : (up ξ i j).coalB j + 2 * ξ.cCol j = ξ.coalB j := by
  simp only [Config.coalB, cCol_up_self]
  obtain ⟨p, hp⟩ : ∃ p, ξ.b j = p + 1 := ⟨ξ.b j - 1, by omega⟩
  have hbj : (up ξ i j).b j = p := by simp only [b_up, decf_self, hp]; omega
  rw [hbj, hp]
  rcases Nat.eq_zero_or_pos p with h0 | h0
  · subst h0; simp
  · obtain ⟨s, hs⟩ : ∃ s, p = s + 1 := ⟨p - 1, by omega⟩
    subst hs
    simp only [Nat.add_sub_cancel]
    ring

theorem coalB_up_of_ne (h : l ≠ j) : (up ξ i j).coalB l = ξ.coalB l := by
  simp only [Config.coalB, b_up_of_ne ξ i j l h, cCol_up_of_ne ξ i j l h]

theorem coalC_up_self : (up ξ i j).coalC i j = ξ.coalC i j + 2 * ξ.c i j := by
  simp only [Config.coalC, c_up_self]
  rcases Nat.eq_zero_or_pos (ξ.c i j) with h0 | h0
  · rw [h0]
  · obtain ⟨s, hs⟩ : ∃ s, ξ.c i j = s + 1 := ⟨ξ.c i j - 1, by omega⟩
    rw [hs]
    simp only [Nat.add_sub_cancel]
    ring

theorem coalC_up_of_ne (h : ¬(k = i ∧ l = j)) : (up ξ i j).coalC k l = ξ.coalC k l := by
  simp only [Config.coalC, c_up_of_ne ξ i k j l h]

theorem coalAB_up_self (hb : ξ.b j ≠ 0) :
    (up ξ i j).coalAB k j + 2 * ξ.a k = ξ.coalAB k j := by
  simp only [Config.coalAB, a_up]
  obtain ⟨p, hp⟩ : ∃ p, ξ.b j = p + 1 := ⟨ξ.b j - 1, by omega⟩
  have hbj : (up ξ i j).b j = p := by simp only [b_up, decf_self, hp]; omega
  rw [hbj, hp]
  ring

theorem coalAB_up_of_ne (h : l ≠ j) : (up ξ i j).coalAB k l = ξ.coalAB k l := by
  simp only [Config.coalAB, a_up, b_up_of_ne ξ i j l h]

end Coeff

section Diag

variable (f : Config KA KB → F) (ξ : Config KA KB) (i : Fin KA) (j : Fin KB)

theorem dropC_diag :
    (((ξ.coalC i j + 2 * ξ.c i j : ℕ)) : F) * f (ξ.dropB j)
      = ((ξ.coalC i j : ℕ) : F) * f (up (ξ.dropC i j) i j)
        + 2 * ((ξ.c i j : ℕ) : F) * f (ξ.dropB j) := by
  rcases Nat.eq_zero_or_pos (ξ.c i j) with h0 | h0
  · rw [ξ.coalC_eq_zero_of h0, h0]; push_cast; ring
  · rw [up_dropC_self (show ξ.c i j ≠ 0 by omega)]; push_cast; ring

theorem killA_diag :
    (((ξ.c i j + 1 : ℕ)) : F) * f ξ
      = ((ξ.c i j : ℕ) : F) * f (up (ξ.killA i j) i j) + f ξ := by
  rcases Nat.eq_zero_or_pos (ξ.c i j) with h0 | h0
  · rw [h0]; push_cast; ring
  · rw [up_killA_self (show ξ.c i j ≠ 0 by omega)]; push_cast; ring

theorem killB_diag :
    (((ξ.c i j + 1 : ℕ)) : F) * f (addA (ξ.dropB j) i)
      = ((ξ.c i j : ℕ) : F) * f (up (ξ.killB i j) i j) + f (addA (ξ.dropB j) i) := by
  rcases Nat.eq_zero_or_pos (ξ.c i j) with h0 | h0
  · rw [h0]; push_cast; ring
  · rw [up_killB_self (show ξ.c i j ≠ 0 by omega)]; push_cast; ring

theorem split_diag :
    (((ξ.c i j + 1 : ℕ)) : F) * f (addA ξ i)
      = ((ξ.c i j : ℕ) : F) * f (up (ξ.split i j) i j) + f (addA ξ i) := by
  rcases Nat.eq_zero_or_pos (ξ.c i j) with h0 | h0
  · rw [h0]; push_cast; ring
  · rw [up_split_self (show ξ.c i j ≠ 0 by omega)]; push_cast; ring

end Diag

theorem sum_up_const {ι : Type*} [Fintype ι] (f : Config KA KB → F) (j : Fin KB)
    (w : ι → F) (T : ι → Config KA KB) :
    (∑ _i : Fin KA, ∑ x : ι, w x * f (up (T x) _i j)) = ∑ x, w x * sumUp f j (T x) := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => by rw [sumUp, Finset.mul_sum]

theorem sum_up_const2 (f : Config KA KB → F) (j : Fin KB) (w : Fin KA → Fin KB → F)
    (T : Fin KA → Fin KB → Config KA KB) :
    (∑ _i : Fin KA, ∑ k, ∑ l, w k l * f (up (T k l) _i j))
      = ∑ k, ∑ l, w k l * sumUp f j (T k l) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => by rw [sumUp, Finset.mul_sum]

theorem sum_up_const2' (f : Config KA KB → F) (j : Fin KB) (w : Fin KB → Fin KA → F)
    (T : Fin KB → Fin KA → Config KA KB) :
    (∑ _i : Fin KA, ∑ l : Fin KB, ∑ k : Fin KA, w l k * f (up (T l k) _i j))
      = ∑ l, ∑ k, w l k * sumUp f j (T l k) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => by rw [sumUp, Finset.mul_sum]

theorem sum_rhs_up (f : Config KA KB → F) (ξ : Config KA KB) (j : Fin KB) (hb : ξ.b j ≠ 0) :
    (∑ i, rhs θA θB ρ πA πB f (up ξ i j))
      = rhs θA θB ρ πA πB (sumUp f j) ξ
        + 2 * (∑ k, ((ξ.a k : ℕ) : F) * f (ξ.mergeAB k j))
        - 2 * (∑ k, ((ξ.a k : ℕ) : F) * sumUp f j (ξ.mergeAB k j))
        - 2 * ((ξ.cCol j : ℕ) : F) * sumUp f j (ξ.dropB j)
        + 2 * ((ξ.cCol j : ℕ) : F) * f (ξ.dropB j)
        + θA * (∑ k, πA k) * f ξ
        + θB * πB j * sumAddA f (ξ.dropB j)
        - θB * πB j * sumUp f j (ξ.dropB j)
        + ρ * sumAddA f ξ := by
  have U1 : (∑ i, ∑ k, (((up ξ i j).coalA k : ℕ) : F) * f ((up ξ i j).dropA k))
      = (∑ k, ((ξ.coalA k : ℕ) : F) * sumUp f j (ξ.dropA k))
        + 2 * ∑ k, ((ξ.a k : ℕ) : F) * f (ξ.mergeAB k j) := by
    have step : ∀ (i k : Fin KA), (((up ξ i j).coalA k : ℕ) : F) * f ((up ξ i j).dropA k)
        = ((ξ.coalA k : ℕ) : F) * f (up (ξ.dropA k) i j)
          + (if k = i then 2 * ((ξ.a k : ℕ) : F) * f (ξ.mergeAB k j) else 0) := by
      intro i k
      rw [dropA_up]
      by_cases hk : k = i
      · subst hk
        rw [ite_eq_left rfl, coalA_up_self, up_dropA_self]
        push_cast
        ring
      · rw [ite_eq_right hk, coalA_up_of_ne ξ i k j hk]
        ring
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
      Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) => step i k]
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => Finset.sum_add_distrib,
      Finset.sum_add_distrib,
      sum_up_const f j (fun k => ((ξ.coalA k : ℕ) : F)) (fun k => ξ.dropA k)]
    congr 1
    simp [Finset.mul_sum, mul_assoc]
  have U2 : (∑ i, ∑ l, (((up ξ i j).coalB l : ℕ) : F) * f ((up ξ i j).dropB l))
      = (∑ l, ((ξ.coalB l : ℕ) : F) * sumUp f j (ξ.dropB l))
        - 2 * ((ξ.cCol j : ℕ) : F) * sumUp f j (ξ.dropB j) := by
    have step : ∀ (i : Fin KA) (l : Fin KB),
        (((up ξ i j).coalB l : ℕ) : F) * f ((up ξ i j).dropB l)
        = ((ξ.coalB l : ℕ) : F) * f (up (ξ.dropB l) i j)
          - (if l = j then 2 * ((ξ.cCol j : ℕ) : F) * f (up (ξ.dropB j) i j) else 0) := by
      intro i l
      rw [dropB_up]
      by_cases hl : l = j
      · subst hl
        rw [ite_eq_left rfl]
        have hc := congrArg (Nat.cast : ℕ → F) (coalB_up_self ξ i l hb)
        push_cast at hc
        linear_combination f (up (ξ.dropB l) i l) * hc
      · rw [ite_eq_right hl, coalB_up_of_ne ξ i j l hl]
        ring
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
      Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) => step i l]
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => Finset.sum_sub_distrib _ _,
      Finset.sum_sub_distrib,
      sum_up_const f j (fun l => ((ξ.coalB l : ℕ) : F)) (fun l => ξ.dropB l)]
    congr 1
    simp [sumUp, Finset.mul_sum, mul_assoc]
  have U3 : (∑ i, ∑ k, ∑ l, (((up ξ i j).coalC k l : ℕ) : F)
        * f ((up ξ i j).dropC k l))
      = (∑ k, ∑ l, ((ξ.coalC k l : ℕ) : F) * sumUp f j (ξ.dropC k l))
        + 2 * ((ξ.cCol j : ℕ) : F) * f (ξ.dropB j) := by
    have step : ∀ (i k : Fin KA) (l : Fin KB),
        (((up ξ i j).coalC k l : ℕ) : F) * f ((up ξ i j).dropC k l)
        = ((ξ.coalC k l : ℕ) : F) * f (up (ξ.dropC k l) i j)
          + (if k = i then (if l = j then 2 * ((ξ.c i j : ℕ) : F) * f (ξ.dropB j) else 0)
             else 0) := by
      intro i k l
      by_cases hk : k = i
      · subst hk
        by_cases hl : l = j
        · subst hl
          rw [ite_eq_left rfl, ite_eq_left rfl, coalC_up_self, dropC_up_self]
          exact dropC_diag f ξ k l
        · rw [ite_eq_left rfl, ite_eq_right hl, coalC_up_of_ne ξ k k j l (by simp [hl]),
            dropC_up_of_ne ξ k k j l (by simp [hl])]
          ring
      · rw [ite_eq_right hk, coalC_up_of_ne ξ i k j l (by simp [hk]),
          dropC_up_of_ne ξ i k j l (by simp [hk])]
        ring
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
      Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) =>
        Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) => step i k l]
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
      Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) => Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => Finset.sum_add_distrib,
      Finset.sum_add_distrib,
      sum_up_const2 f j (fun k l => ((ξ.coalC k l : ℕ) : F)) (fun k l => ξ.dropC k l)]
    congr 1
    have hin : (∑ i, ∑ k, ∑ l, (if k = i then
          (if l = j then 2 * ((ξ.c i j : ℕ) : F) * f (ξ.dropB j) else 0) else 0))
        = ∑ i, 2 * ((ξ.c i j : ℕ) : F) * f (ξ.dropB j) := by
      exact Finset.sum_congr rfl fun i _ => by simp
    rw [hin, Config.cCol, Nat.cast_sum, Finset.mul_sum, Finset.sum_mul]
  have U4 : (∑ i, ∑ k, ∑ l, (((up ξ i j).coalAB k l : ℕ) : F)
        * f ((up ξ i j).mergeAB k l))
      = (∑ k, ∑ l, ((ξ.coalAB k l : ℕ) : F) * sumUp f j (ξ.mergeAB k l))
        - 2 * ∑ k, ((ξ.a k : ℕ) : F) * sumUp f j (ξ.mergeAB k j) := by
    have step : ∀ (i k : Fin KA) (l : Fin KB),
        (((up ξ i j).coalAB k l : ℕ) : F) * f ((up ξ i j).mergeAB k l)
        = ((ξ.coalAB k l : ℕ) : F) * f (up (ξ.mergeAB k l) i j)
          - (if l = j then 2 * ((ξ.a k : ℕ) : F) * f (up (ξ.mergeAB k j) i j) else 0) := by
      intro i k l
      rw [mergeAB_up]
      by_cases hl : l = j
      · subst hl
        rw [ite_eq_left rfl]
        have hc := congrArg (Nat.cast : ℕ → F) (coalAB_up_self ξ i k l hb)
        push_cast at hc
        linear_combination f (up (ξ.mergeAB k l) i l) * hc
      · rw [ite_eq_right hl, coalAB_up_of_ne ξ i k j l hl]
        ring
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
      Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) =>
        Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) => step i k l]
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
      Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) => Finset.sum_sub_distrib _ _]
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => Finset.sum_sub_distrib _ _,
      Finset.sum_sub_distrib,
      sum_up_const2 f j (fun k l => ((ξ.coalAB k l : ℕ) : F)) (fun k l => ξ.mergeAB k l)]
    congr 1
    have hin : (∑ i, ∑ k, ∑ l, (if l = j then
          2 * ((ξ.a k : ℕ) : F) * f (up (ξ.mergeAB k j) i j) else 0))
        = ∑ i, ∑ k, 2 * ((ξ.a k : ℕ) : F) * f (up (ξ.mergeAB k j) i j) := by
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by simp
    rw [hin, Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [sumUp, Finset.mul_sum, mul_assoc]
  have U5 : (∑ i, θA * ∑ k, πA k * ((((up ξ i j).a k : ℕ) : F)
        * f ((up ξ i j).dropA k)
        + ∑ l, (((up ξ i j).c k l : ℕ) : F) * f ((up ξ i j).killA k l)))
      = θA * ∑ k, πA k * (((ξ.a k : ℕ) : F) * sumUp f j (ξ.dropA k)
          + ∑ l, ((ξ.c k l : ℕ) : F) * sumUp f j (ξ.killA k l))
        + θA * (∑ k, πA k) * f ξ := by
    rw [← Finset.mul_sum]
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
      sum_pi_add πA (fun k => (((up ξ i j).a k : ℕ) : F) * f ((up ξ i j).dropA k))
        (fun k => ∑ l, (((up ξ i j).c k l : ℕ) : F) * f ((up ξ i j).killA k l))]
    rw [Finset.sum_add_distrib]
    have P1 : (∑ i, ∑ k, πA k * ((((up ξ i j).a k : ℕ) : F)
          * f ((up ξ i j).dropA k)))
        = ∑ k, πA k * (((ξ.a k : ℕ) : F) * sumUp f j (ξ.dropA k)) := by
      have hstep : ∀ (i k : Fin KA),
          πA k * ((((up ξ i j).a k : ℕ) : F) * f ((up ξ i j).dropA k))
            = (πA k * ((ξ.a k : ℕ) : F)) * f (up (ξ.dropA k) i j) := by
        intro i k
        rw [a_up, dropA_up]
        ring
      rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
        Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) => hstep i k]
      rw [sum_up_const f j (fun k => πA k * ((ξ.a k : ℕ) : F)) (fun k => ξ.dropA k)]
      exact Finset.sum_congr rfl fun k _ => by rw [mul_assoc]
    have P2 : (∑ i, ∑ k, πA k * ∑ l, (((up ξ i j).c k l : ℕ) : F)
          * f ((up ξ i j).killA k l))
        = (∑ k, πA k * ∑ l, ((ξ.c k l : ℕ) : F) * sumUp f j (ξ.killA k l))
          + (∑ k, πA k) * f ξ := by
      have hterm : ∀ (i k : Fin KA) (l : Fin KB),
          (((up ξ i j).c k l : ℕ) : F) * f ((up ξ i j).killA k l)
            = ((ξ.c k l : ℕ) : F) * f (up (ξ.killA k l) i j)
              + (if k = i then (if l = j then f ξ else 0) else 0) := by
        intro i k l
        by_cases hk : k = i
        · subst hk
          by_cases hl : l = j
          · subst hl
            rw [ite_eq_left rfl, ite_eq_left rfl, c_up_self, killA_up_self ξ k l hb]
            exact killA_diag f ξ k l
          · rw [ite_eq_left rfl, ite_eq_right hl, c_up_of_ne ξ k k j l (by simp [hl]),
              killA_up_of_ne ξ k k j l hb (by simp [hl])]
            ring
        · rw [ite_eq_right hk, c_up_of_ne ξ i k j l (by simp [hk]),
            killA_up_of_ne ξ i k j l hb (by simp [hk])]
          ring
      have hinner : ∀ (i k : Fin KA),
          πA k * (∑ l, (((up ξ i j).c k l : ℕ) : F) * f ((up ξ i j).killA k l))
            = (∑ l, (πA k * ((ξ.c k l : ℕ) : F)) * f (up (ξ.killA k l) i j))
              + (if k = i then πA k * f ξ else 0) := by
        intro i k
        rw [Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) => hterm i k l,
          Finset.sum_add_distrib, mul_add, Finset.mul_sum]
        congr 1
        · exact Finset.sum_congr rfl fun l _ => by ring
        · by_cases hk : k = i <;> simp [hk]
      rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
        Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) => hinner i k]
      rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => Finset.sum_add_distrib,
        Finset.sum_add_distrib,
        sum_up_const2 f j (fun k l => πA k * ((ξ.c k l : ℕ) : F)) (fun k l => ξ.killA k l)]
      congr 1
      · exact Finset.sum_congr rfl fun k _ => by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun l _ => by ring
      · rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => by simp
    rw [P1, P2, sum_pi_add πA (fun k => ((ξ.a k : ℕ) : F) * sumUp f j (ξ.dropA k))
      (fun k => ∑ l, ((ξ.c k l : ℕ) : F) * sumUp f j (ξ.killA k l))]
    ring
  have U6 : (∑ i, θB * ∑ l, πB l * ((((up ξ i j).b l : ℕ) : F)
        * f ((up ξ i j).dropB l)
        + ∑ k, (((up ξ i j).c k l : ℕ) : F) * f ((up ξ i j).killB k l)))
      = θB * ∑ l, πB l * (((ξ.b l : ℕ) : F) * sumUp f j (ξ.dropB l)
          + ∑ k, ((ξ.c k l : ℕ) : F) * sumUp f j (ξ.killB k l))
        - θB * πB j * sumUp f j (ξ.dropB j)
        + θB * πB j * sumAddA f (ξ.dropB j) := by
    rw [← Finset.mul_sum]
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
      sum_pi_addB πB (fun l => (((up ξ i j).b l : ℕ) : F) * f ((up ξ i j).dropB l))
        (fun l => ∑ k, (((up ξ i j).c k l : ℕ) : F) * f ((up ξ i j).killB k l))]
    rw [Finset.sum_add_distrib]
    have P1 : (∑ i, ∑ l, πB l * ((((up ξ i j).b l : ℕ) : F)
          * f ((up ξ i j).dropB l)))
        = (∑ l, πB l * (((ξ.b l : ℕ) : F) * sumUp f j (ξ.dropB l)))
          - πB j * sumUp f j (ξ.dropB j) := by
      have hstep : ∀ (i : Fin KA) (l : Fin KB),
          πB l * ((((up ξ i j).b l : ℕ) : F) * f ((up ξ i j).dropB l))
            = (πB l * ((ξ.b l : ℕ) : F)) * f (up (ξ.dropB l) i j)
              - (if l = j then πB j * f (up (ξ.dropB j) i j) else 0) := by
        intro i l
        rw [dropB_up]
        by_cases hl : l = j
        · subst hl
          rw [ite_eq_left rfl]
          have hc := congrArg (Nat.cast : ℕ → F) (b_up_self ξ i l hb)
          push_cast at hc
          linear_combination (πB l * f (up (ξ.dropB l) i l)) * hc
        · rw [ite_eq_right hl, b_up_of_ne ξ i j l hl]
          ring
      rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
        Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) => hstep i l]
      rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => Finset.sum_sub_distrib _ _,
        Finset.sum_sub_distrib,
        sum_up_const f j (fun l => πB l * ((ξ.b l : ℕ) : F)) (fun l => ξ.dropB l)]
      congr 1
      · exact Finset.sum_congr rfl fun l _ => by rw [mul_assoc]
      · simp [sumUp, Finset.mul_sum]
    have P2 : (∑ i, ∑ l, πB l * ∑ k, (((up ξ i j).c k l : ℕ) : F)
          * f ((up ξ i j).killB k l))
        = (∑ l, πB l * ∑ k, ((ξ.c k l : ℕ) : F) * sumUp f j (ξ.killB k l))
          + πB j * sumAddA f (ξ.dropB j) := by
      have hterm : ∀ (i k : Fin KA) (l : Fin KB),
          (((up ξ i j).c k l : ℕ) : F) * f ((up ξ i j).killB k l)
            = ((ξ.c k l : ℕ) : F) * f (up (ξ.killB k l) i j)
              + (if k = i then (if l = j then f (addA (ξ.dropB j) i) else 0) else 0) := by
        intro i k l
        by_cases hk : k = i
        · subst hk
          by_cases hl : l = j
          · subst hl
            rw [ite_eq_left rfl, ite_eq_left rfl, c_up_self, killB_up_self ξ k l]
            exact killB_diag f ξ k l
          · rw [ite_eq_left rfl, ite_eq_right hl, c_up_of_ne ξ k k j l (by simp [hl]),
              killB_up_of_ne ξ k k j l (by simp [hl])]
            ring
        · rw [ite_eq_right hk, c_up_of_ne ξ i k j l (by simp [hk]),
            killB_up_of_ne ξ i k j l (by simp [hk])]
          ring
      have hinner : ∀ (i : Fin KA) (l : Fin KB),
          πB l * (∑ k, (((up ξ i j).c k l : ℕ) : F) * f ((up ξ i j).killB k l))
            = (∑ k, (πB l * ((ξ.c k l : ℕ) : F)) * f (up (ξ.killB k l) i j))
              + (if l = j then πB l * f (addA (ξ.dropB j) i) else 0) := by
        intro i l
        rw [Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) => hterm i k l,
          Finset.sum_add_distrib, mul_add, Finset.mul_sum]
        congr 1
        · exact Finset.sum_congr rfl fun k _ => by ring
        · by_cases hl : l = j <;> simp [hl]
      rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
        Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) => hinner i l]
      rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => Finset.sum_add_distrib,
        Finset.sum_add_distrib,
        sum_up_const2' f j (fun l k => πB l * ((ξ.c k l : ℕ) : F))
          (fun l k => ξ.killB k l)]
      congr 1
      · exact Finset.sum_congr rfl fun l _ => by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      · simp [sumAddA, Finset.mul_sum]
    rw [P1, P2, sum_pi_addB πB (fun l => ((ξ.b l : ℕ) : F) * sumUp f j (ξ.dropB l))
      (fun l => ∑ k, ((ξ.c k l : ℕ) : F) * sumUp f j (ξ.killB k l))]
    ring
  have U7 : (∑ i, ρ * ∑ k, ∑ l, (((up ξ i j).c k l : ℕ) : F)
        * f ((up ξ i j).split k l))
      = ρ * (∑ k, ∑ l, ((ξ.c k l : ℕ) : F) * sumUp f j (ξ.split k l))
        + ρ * sumAddA f ξ := by
    rw [← Finset.mul_sum]
    have hterm : ∀ (i k : Fin KA) (l : Fin KB),
        (((up ξ i j).c k l : ℕ) : F) * f ((up ξ i j).split k l)
          = ((ξ.c k l : ℕ) : F) * f (up (ξ.split k l) i j)
            + (if k = i then (if l = j then f (addA ξ i) else 0) else 0) := by
      intro i k l
      by_cases hk : k = i
      · subst hk
        by_cases hl : l = j
        · subst hl
          rw [ite_eq_left rfl, ite_eq_left rfl, c_up_self, split_up_self ξ k l hb]
          exact split_diag f ξ k l
        · rw [ite_eq_left rfl, ite_eq_right hl, c_up_of_ne ξ k k j l (by simp [hl]),
            split_up_of_ne ξ k k j l hb (by simp [hl])]
          ring
      · rw [ite_eq_right hk, c_up_of_ne ξ i k j l (by simp [hk]),
          split_up_of_ne ξ i k j l hb (by simp [hk])]
        ring
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
      Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) =>
        Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) => hterm i k l]
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
      Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) => Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => Finset.sum_add_distrib,
      Finset.sum_add_distrib,
      sum_up_const2 f j (fun k l => ((ξ.c k l : ℕ) : F)) (fun k l => ξ.split k l)]
    rw [← mul_add]
    congr 1
    simp [sumAddA]
  simp only [rhs]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    U1, U2, U3, U4, U5, U6, U7]
  ring

end Rhone.Probability.Denominator
