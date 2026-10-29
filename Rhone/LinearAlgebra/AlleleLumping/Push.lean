/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.AlleleLumping.Defs

/-! # Coarsening and multiplicity under the increment of one count -/

@[expose] public section

namespace Rhone.LinearAlgebra.AlleleLumping

open Finset Recursion Recursion.Config

variable {KA KB KA' KB' : ℕ}

section Vec

variable {ι : Type*} [DecidableEq ι]

theorem decf_incf (v : ι → ℕ) (i : ι) : decf (incf v i) i = v := by
  funext k
  by_cases hk : k = i
  · subst hk; rw [decf_self, incf_self]; omega
  · rw [decf_of_ne _ hk, incf_of_ne _ hk]

theorem incf_decf {v : ι → ℕ} {i : ι} (h : v i ≠ 0) : incf (decf v i) i = v := by
  funext k
  by_cases hk : k = i
  · subst hk; rw [incf_self, decf_self]; omega
  · rw [incf_of_ne _ hk, decf_of_ne _ hk]

theorem incf_apply (v : ι → ℕ) (i k : ι) : incf v i k = v k + if k = i then 1 else 0 := by
  by_cases hk : k = i
  · subst hk; simp [incf_self]
  · simp [incf_of_ne _ hk, hk]

theorem multinomial_incf [Fintype ι] (v : ι → ℕ) (i : ι) :
    Nat.multinomial univ (incf v i) * (v i + 1)
      = ((∑ k, v k) + 1) * Nat.multinomial univ v := by
  have e1 := Finset.mul_prod_erase univ (fun k => (incf v i k).factorial) (mem_univ i)
  have e2 := Finset.mul_prod_erase univ (fun k => (v k).factorial) (mem_univ i)
  have e3 : ∏ k ∈ univ.erase i, (incf v i k).factorial = ∏ k ∈ univ.erase i, (v k).factorial :=
    Finset.prod_congr rfl fun k hk => by rw [incf_of_ne _ (Finset.ne_of_mem_erase hk)]
  beta_reduce at e1 e2
  rw [e3, incf_self, Nat.factorial_succ] at e1
  have h1 := Nat.multinomial_spec univ (incf v i)
  have h2 := Nat.multinomial_spec univ v
  rw [sum_incf, Nat.factorial_succ, ← h2, ← e1, ← e2] at h1
  have hpos : 0 < (v i).factorial * ∏ k ∈ univ.erase i, (v k).factorial :=
    Nat.mul_pos (Nat.factorial_pos _) (Finset.prod_pos fun k _ => Nat.factorial_pos _)
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  calc _ = ((v i + 1) * (v i).factorial * ∏ k ∈ univ.erase i, (v k).factorial)
          * Nat.multinomial univ (incf v i) := by ring
    _ = _ := h1
    _ = _ := by ring

end Vec

theorem pushV_incf {K K' : ℕ} (f : Fin K → Fin K') (v : Fin K → ℕ) (i : Fin K) :
    pushV f (incf v i) = incf (pushV f v) (f i) := by
  funext p
  rw [incf_apply]
  simp only [pushV, incf_apply, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact if_congr eq_comm rfl rfl

theorem pushV_decf {K K' : ℕ} (f : Fin K → Fin K') {v : Fin K → ℕ} {i : Fin K} (h : v i ≠ 0) :
    pushV f (decf v i) = decf (pushV f v) (f i) := by
  conv_rhs => rw [← incf_decf h, pushV_incf, decf_incf]

theorem le_pushV {K K' : ℕ} (f : Fin K → Fin K') (v : Fin K → ℕ) (i : Fin K) :
    v i ≤ pushV f v (f i) :=
  Finset.single_le_sum (f := v) (fun _ _ => Nat.zero_le _) (by simp)

theorem incC_apply (m : Fin KA → Fin KB → ℕ) (i : Fin KA) (j : Fin KB) (i' : Fin KA)
    (j' : Fin KB) : incC m i j i' j' = m i' j' + if i' = i ∧ j' = j then 1 else 0 := by
  rw [incC_eq_add, Pi.add_apply, Pi.add_apply, eM_apply, add_comm]
  by_cases h1 : i' = i <;> by_cases h2 : j' = j <;> simp [h1, h2]

theorem decC_incC (m : Fin KA → Fin KB → ℕ) (i : Fin KA) (j : Fin KB) :
    decC (incC m i j) i j = m := by
  rw [incC_eq_add, decC_eM_add]

theorem incC_decC {m : Fin KA → Fin KB → ℕ} {i : Fin KA} {j : Fin KB} (h : m i j ≠ 0) :
    incC (decC m i j) i j = m := by
  funext i'
  by_cases hi : i' = i
  · subst hi
    simp only [incC, decC, Function.update_self]
    exact incf_decf h
  · simp [incC, decC, Function.update_of_ne hi]

theorem pushM_incC (fA : Fin KA → Fin KA') (fB : Fin KB → Fin KB') (m : Fin KA → Fin KB → ℕ)
    (i : Fin KA) (j : Fin KB) :
    pushM fA fB (incC m i j) = incC (pushM fA fB m) (fA i) (fB j) := by
  funext p r
  rw [incC_apply]
  simp only [pushM, incC_apply, Finset.sum_add_distrib]
  congr 1
  have inner : ∀ i' : Fin KA, (∑ j' with fB j' = r, if i' = i ∧ j' = j then 1 else 0)
      = if i' = i then (if r = fB j then 1 else 0) else 0 := by
    intro i'
    by_cases hi : i' = i
    · simp only [hi, true_and, ite_true]
      rw [Finset.sum_ite_eq']
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact if_congr eq_comm rfl rfl
    · simp [hi]
  simp only [inner]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hp : fA i = p
  · subst hp
    by_cases hr : r = fB j <;> simp [hr]
  · have hp' : ¬ p = fA i := fun h => hp h.symm
    simp [hp, hp']

theorem pushM_decC (fA : Fin KA → Fin KA') (fB : Fin KB → Fin KB') {m : Fin KA → Fin KB → ℕ}
    {i : Fin KA} {j : Fin KB} (h : m i j ≠ 0) :
    pushM fA fB (decC m i j) = decC (pushM fA fB m) (fA i) (fB j) := by
  conv_rhs => rw [← incC_decC h, pushM_incC, decC_incC]

theorem le_pushM (fA : Fin KA → Fin KA') (fB : Fin KB → Fin KB') (m : Fin KA → Fin KB → ℕ)
    (i : Fin KA) (j : Fin KB) : m i j ≤ pushM fA fB m (fA i) (fB j) := by
  have h1 : m i j ≤ ∑ j' with fB j' = fB j, m i j' :=
    Finset.single_le_sum (f := m i) (fun _ _ => Nat.zero_le _) (by simp)
  have h2 : (∑ j' with fB j' = fB j, m i j') ≤ pushM fA fB m (fA i) (fB j) :=
    Finset.single_le_sum (f := fun i' => ∑ j' with fB j' = fB j, m i' j')
      (fun _ _ => Nat.zero_le _) (by simp)
  exact le_trans h1 h2

def addA (ξ : Config KA KB) (i : Fin KA) : Config KA KB := ⟨incf ξ.a i, ξ.b, ξ.c⟩

def addB (ξ : Config KA KB) (j : Fin KB) : Config KA KB := ⟨ξ.a, incf ξ.b j, ξ.c⟩

def addC (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) : Config KA KB :=
  ⟨ξ.a, ξ.b, incC ξ.c i j⟩

section Moves

variable (ξ : Config KA KB) (i : Fin KA) (j : Fin KB)

theorem dropA_addA : (addA ξ i).dropA i = ξ := by
  simp only [addA, dropA, decf_incf]

theorem dropB_addB : (addB ξ j).dropB j = ξ := by
  simp only [addB, dropB, decf_incf]

theorem dropC_addC : (addC ξ i j).dropC i j = ξ := by
  simp only [addC, dropC, decC_incC]

variable {ξ i j}

theorem addA_dropA (h : ξ.a i ≠ 0) : addA (ξ.dropA i) i = ξ := by
  simp only [addA, dropA, incf_decf h]

theorem addB_dropB (h : ξ.b j ≠ 0) : addB (ξ.dropB j) j = ξ := by
  simp only [addB, dropB, incf_decf h]

theorem addC_dropC (h : ξ.c i j ≠ 0) : addC (ξ.dropC i j) i j = ξ := by
  simp only [addC, dropC, incC_decC h]

end Moves

section Push

variable (fA : Fin KA → Fin KA') (fB : Fin KB → Fin KB') (ξ : Config KA KB) (i : Fin KA)
  (j : Fin KB)

theorem push_addA : push fA fB (addA ξ i) = addA (push fA fB ξ) (fA i) := by
  simp only [push, addA, pushV_incf]

theorem push_addB : push fA fB (addB ξ j) = addB (push fA fB ξ) (fB j) := by
  simp only [push, addB, pushV_incf]

theorem push_addC : push fA fB (addC ξ i j) = addC (push fA fB ξ) (fA i) (fB j) := by
  simp only [push, addC, pushM_incC]

variable {ξ i j}

theorem push_dropA (h : ξ.a i ≠ 0) : push fA fB (ξ.dropA i) = (push fA fB ξ).dropA (fA i) := by
  simp only [push, dropA, pushV_decf fA h]

theorem push_dropB (h : ξ.b j ≠ 0) : push fA fB (ξ.dropB j) = (push fA fB ξ).dropB (fB j) := by
  simp only [push, dropB, pushV_decf fB h]

theorem push_dropC (h : ξ.c i j ≠ 0) :
    push fA fB (ξ.dropC i j) = (push fA fB ξ).dropC (fA i) (fB j) := by
  simp only [push, dropC, pushM_decC fA fB h]

end Push

theorem mult_addA (ξ : Config KA KB) (i : Fin KA) :
    mult (addA ξ i) * (ξ.a i + 1) = (ξ.sumA + 1) * mult ξ := by
  have h := multinomial_incf ξ.a i
  simp only [mult, addA, sumA]
  calc Nat.multinomial univ (incf ξ.a i) * Nat.multinomial univ ξ.b
          * Nat.multinomial univ (fun x : Fin KA × Fin KB => ξ.c x.1 x.2) * (ξ.a i + 1)
      = Nat.multinomial univ (incf ξ.a i) * (ξ.a i + 1) * (Nat.multinomial univ ξ.b
          * Nat.multinomial univ (fun x : Fin KA × Fin KB => ξ.c x.1 x.2)) := by ring
    _ = _ := by rw [h]; ring

theorem mult_addB (ξ : Config KA KB) (j : Fin KB) :
    mult (addB ξ j) * (ξ.b j + 1) = (ξ.sumB + 1) * mult ξ := by
  have h := multinomial_incf ξ.b j
  simp only [mult, addB, sumB]
  calc Nat.multinomial univ ξ.a * Nat.multinomial univ (incf ξ.b j)
          * Nat.multinomial univ (fun x : Fin KA × Fin KB => ξ.c x.1 x.2) * (ξ.b j + 1)
      = Nat.multinomial univ (incf ξ.b j) * (ξ.b j + 1) * (Nat.multinomial univ ξ.a
          * Nat.multinomial univ (fun x : Fin KA × Fin KB => ξ.c x.1 x.2)) := by ring
    _ = _ := by rw [h]; ring

theorem mult_addC (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) :
    mult (addC ξ i j) * (ξ.c i j + 1) = (ξ.t + 1) * mult ξ := by
  have hinc : (fun x : Fin KA × Fin KB => incC ξ.c i j x.1 x.2)
      = incf (fun x : Fin KA × Fin KB => ξ.c x.1 x.2) (i, j) := by
    funext x
    obtain ⟨i', j'⟩ := x
    rw [incC_apply, incf_apply]
    simp only [Prod.mk.injEq]
  have ht : ∑ x : Fin KA × Fin KB, ξ.c x.1 x.2 = ξ.t := by
    rw [Fintype.sum_prod_type]; rfl
  have h := multinomial_incf (fun x : Fin KA × Fin KB => ξ.c x.1 x.2) (i, j)
  rw [ht] at h
  simp only [mult, addC, hinc]
  calc Nat.multinomial univ ξ.a * Nat.multinomial univ ξ.b
          * Nat.multinomial univ (incf (fun x : Fin KA × Fin KB => ξ.c x.1 x.2) (i, j))
          * (ξ.c i j + 1)
      = Nat.multinomial univ (incf (fun x : Fin KA × Fin KB => ξ.c x.1 x.2) (i, j))
          * (ξ.c i j + 1) * (Nat.multinomial univ ξ.a * Nat.multinomial univ ξ.b) := by ring
    _ = _ := by rw [h]; ring

theorem mult_zero : mult (0 : Config KA KB) = 1 := by
  have h : ∀ {ι : Type} [Fintype ι], Nat.multinomial (univ : Finset ι) (fun _ => 0) = 1 := by
    intro ι _
    simp [Nat.multinomial]
  have ha : (0 : Config KA KB).a = fun _ => 0 := rfl
  have hb : (0 : Config KA KB).b = fun _ => 0 := rfl
  have hc : (fun x : Fin KA × Fin KB => (0 : Config KA KB).c x.1 x.2) = fun _ => 0 := rfl
  rw [mult, ha, hb, hc, h, h, h]

theorem mult_pos (ξ : Config KA KB) : 0 < mult ξ := by
  have h : ∀ {ι : Type} [Fintype ι] (v : ι → ℕ), 0 < Nat.multinomial (univ : Finset ι) v := by
    intro ι _ v
    rcases Nat.eq_zero_or_pos (Nat.multinomial univ v) with h0 | h0
    · have := Nat.multinomial_spec univ v
      rw [h0, mul_zero] at this
      exact absurd this.symm (Nat.factorial_ne_zero _)
    · exact h0
  exact Nat.mul_pos (Nat.mul_pos (h _) (h _)) (h _)

end Rhone.LinearAlgebra.AlleleLumping
