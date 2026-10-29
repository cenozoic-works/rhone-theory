/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.AlleleLumping.Push

/-! # The lumped sum and its behaviour under the moves of the recursion -/

@[expose] public section

namespace Rhone.LinearAlgebra.AlleleLumping

open Finset Recursion Recursion.Config

variable {KA KB KA' KB' : ℕ} {F : Type*} [Field F]
variable (fA : Fin KA → Fin KA') (fB : Fin KB → Fin KB')

noncomputable def lumpSum (h : Config KA KB → F) (η : Config KA' KB') : F :=
  ∑ ξ ∈ fibre fA fB η, (mult ξ : F) * h ξ

theorem lumpSum_add (f g : Config KA KB → F) (η : Config KA' KB') :
    lumpSum fA fB (fun ξ => f ξ + g ξ) η = lumpSum fA fB f η + lumpSum fA fB g η := by
  simp only [lumpSum, mul_add, Finset.sum_add_distrib]

theorem lumpSum_const_mul (c : F) (f : Config KA KB → F) (η : Config KA' KB') :
    lumpSum fA fB (fun ξ => c * f ξ) η = c * lumpSum fA fB f η := by
  simp only [lumpSum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun ξ _ => by ring

theorem lumpSum_sum {κ : Type*} (s : Finset κ) (f : κ → Config KA KB → F)
    (η : Config KA' KB') :
    lumpSum fA fB (fun ξ => ∑ k ∈ s, f k ξ) η = ∑ k ∈ s, lumpSum fA fB (f k) η := by
  simp only [lumpSum, Finset.mul_sum]
  exact Finset.sum_comm

variable {fA fB} in
theorem lumpSum_congr {f g : Config KA KB → F} {η : Config KA' KB'}
    (h : ∀ ξ, push fA fB ξ = η → f ξ = g ξ) : lumpSum fA fB f η = lumpSum fA fB g η :=
  Finset.sum_congr rfl fun ξ hξ => by rw [h ξ (mem_fibre.mp hξ)]

theorem sum_lumpSum_weight {κ : Type*} (s : Finset κ) (w : κ → Config KA KB → F)
    (g : Config KA KB → F) (η : Config KA' KB') (W : F)
    (hW : ∀ ζ, push fA fB ζ = η → ∑ k ∈ s, w k ζ = W) :
    ∑ k ∈ s, lumpSum fA fB (fun ζ => w k ζ * g ζ) η = W * lumpSum fA fB g η := by
  simp only [lumpSum]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ζ hζ => ?_
  rw [← hW ζ (mem_fibre.mp hζ), Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem sum_lumpSum_weight₂ {κ κ' : Type*} (s : Finset κ) (t : Finset κ')
    (w : κ → κ' → Config KA KB → F) (g : Config KA KB → F) (η : Config KA' KB') (W : F)
    (hW : ∀ ζ, push fA fB ζ = η → ∑ k ∈ s, ∑ l ∈ t, w k l ζ = W) :
    ∑ k ∈ s, ∑ l ∈ t, lumpSum fA fB (fun ζ => w k l ζ * g ζ) η = W * lumpSum fA fB g η := by
  have h := sum_lumpSum_weight fA fB (s ×ˢ t) (fun x => w x.1 x.2) g η W
    (fun ζ hζ => (Finset.sum_product' s t (fun k l => w k l ζ)).trans (hW ζ hζ))
  rw [← h]
  exact (Finset.sum_product' s t
    (fun k l => lumpSum fA fB (fun ζ => w k l ζ * g ζ) η)).symm

theorem sum_fib {K K' : ℕ} (f : Fin K → Fin K') (h : Fin K → Fin K' → F) :
    ∑ i, h i (f i) = ∑ p, ∑ i with f i = p, h i p := by
  rw [← Finset.sum_fiberwise univ f (fun i => h i (f i))]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun i hi => ?_
  rw [(Finset.mem_filter.mp hi).2]

theorem sum_pushPi {K K' : ℕ} (f : Fin K → Fin K') (π : Fin K → F) (Z : Fin K' → F) :
    ∑ i, π i * Z (f i) = ∑ p, pushPi f π p * Z p := by
  rw [sum_fib f (fun i p => π i * Z p)]
  exact Finset.sum_congr rfl fun p _ => by rw [pushPi, Finset.sum_mul]

theorem sum_fib_lumpSum {K K' : ℕ} (f : Fin K → Fin K') (c : Fin K' → Prop) [DecidablePred c]
    (C : Fin K' → F) (w : Fin K → Config KA KB → F) (g : Config KA KB → F)
    (ηf : Fin K' → Config KA' KB') (W : Fin K' → F)
    (hW : ∀ p ζ, push fA fB ζ = ηf p → ∑ i with f i = p, w i ζ = W p) :
    ∑ i, (if c (f i) then 0
        else C (f i) * lumpSum fA fB (fun ζ => w i ζ * g ζ) (ηf (f i)))
      = ∑ p, if c p then 0 else C p * W p * lumpSum fA fB g (ηf p) := by
  rw [sum_fib f (fun i p => if c p then 0
    else C p * lumpSum fA fB (fun ζ => w i ζ * g ζ) (ηf p))]
  refine Finset.sum_congr rfl fun p _ => ?_
  split_ifs with h
  · exact Finset.sum_const_zero
  · rw [← Finset.mul_sum, sum_lumpSum_weight fA fB _ w g (ηf p) (W p) (hW p), mul_assoc]

theorem sum_fib_lumpSum₂ (c : Fin KA' → Fin KB' → Prop) [∀ p r, Decidable (c p r)]
    (C : Fin KA' → Fin KB' → F) (w : Fin KA → Fin KB → Config KA KB → F)
    (g : Config KA KB → F) (ηf : Fin KA' → Fin KB' → Config KA' KB') (W : Fin KA' → Fin KB' → F)
    (hW : ∀ p r ζ, push fA fB ζ = ηf p r →
      ∑ i with fA i = p, ∑ j with fB j = r, w i j ζ = W p r) :
    ∑ i, ∑ j, (if c (fA i) (fB j) then 0
        else C (fA i) (fB j) * lumpSum fA fB (fun ζ => w i j ζ * g ζ) (ηf (fA i) (fB j)))
      = ∑ p, ∑ r, if c p r then 0 else C p r * W p r * lumpSum fA fB g (ηf p r) := by
  rw [sum_fib fA (fun i p => ∑ j, if c p (fB j) then 0
    else C p (fB j) * lumpSum fA fB (fun ζ => w i j ζ * g ζ) (ηf p (fB j)))]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hj : ∀ i, (∑ j, if c p (fB j) then 0
        else C p (fB j) * lumpSum fA fB (fun ζ => w i j ζ * g ζ) (ηf p (fB j)))
      = ∑ r, ∑ j with fB j = r, if c p r then 0
        else C p r * lumpSum fA fB (fun ζ => w i j ζ * g ζ) (ηf p r) := fun i =>
    sum_fib fB (fun j r => if c p r then 0
      else C p r * lumpSum fA fB (fun ζ => w i j ζ * g ζ) (ηf p r))
  simp only [hj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  split_ifs with h
  · simp
  · simp only [← Finset.mul_sum]
    rw [sum_lumpSum_weight₂ fA fB _ _ w g (ηf p r) (W p r) (hW p r), mul_assoc]

theorem lumpSum_inc_gen (inc dec : Config KA KB → Config KA KB) (cnt : Config KA KB → ℕ)
    (η η' : Config KA' KB') (S : ℕ)
    (h1 : ∀ ξ, push fA fB ξ = η → push fA fB (inc ξ) = η')
    (h2 : ∀ ξ, dec (inc ξ) = ξ)
    (h3 : ∀ ζ, cnt ζ ≠ 0 → inc (dec ζ) = ζ)
    (h4 : ∀ ζ, cnt ζ ≠ 0 → push fA fB ζ = η' → push fA fB (dec ζ) = η)
    (h5 : ∀ ξ, push fA fB ξ = η → mult (inc ξ) * cnt (inc ξ) = S * mult ξ)
    (g : Config KA KB → F) :
    (S : F) * lumpSum fA fB (fun ξ => g (inc ξ)) η
      = lumpSum fA fB (fun ζ => (cnt ζ : F) * g ζ) η' := by
  simp only [lumpSum, Finset.mul_sum]
  have hval : ∀ ξ ∈ fibre fA fB η, (S : F) * ((mult ξ : F) * g (inc ξ))
      = (mult (inc ξ) : F) * ((cnt (inc ξ) : F) * g (inc ξ)) := by
    intro ξ hξ
    have hc : (mult (inc ξ) : F) * (cnt (inc ξ) : F) = (S : F) * (mult ξ : F) := by
      exact_mod_cast congrArg (Nat.cast (R := F)) (h5 ξ (mem_fibre.mp hξ))
    rw [← mul_assoc, ← mul_assoc, hc]
  refine Finset.sum_bij_ne_zero (fun ξ _ _ => inc ξ) ?_ ?_ ?_ ?_
  · intro ξ hξ _
    exact mem_fibre.mpr (h1 ξ (mem_fibre.mp hξ))
  · intro ξ₁ _ _ ξ₂ _ _ h
    rw [← h2 ξ₁, h, h2]
  · intro ζ hζ hne
    have hc : cnt ζ ≠ 0 := by
      intro h0
      apply hne
      simp [h0]
    have hmem : dec ζ ∈ fibre fA fB η := mem_fibre.mpr (h4 ζ hc (mem_fibre.mp hζ))
    refine ⟨dec ζ, hmem, ?_, h3 ζ hc⟩
    rw [hval _ hmem, h3 ζ hc]
    exact hne
  · intro ξ hξ _
    exact hval ξ hξ

variable (g : Config KA KB → F) (η : Config KA' KB')

theorem lumpSum_addA (i : Fin KA) :
    ((η.sumA + 1 : ℕ) : F) * lumpSum fA fB (fun ξ => g (addA ξ i)) η
      = lumpSum fA fB (fun ζ => (ζ.a i : F) * g ζ) (addA η (fA i)) := by
  refine lumpSum_inc_gen fA fB (fun ξ => addA ξ i) (fun ξ => ξ.dropA i) (fun ζ => ζ.a i)
    η (addA η (fA i)) (η.sumA + 1) ?_ (fun ξ => dropA_addA ξ i) (fun ζ h => addA_dropA h)
    ?_ ?_ g
  · intro ξ hξ
    rw [push_addA, hξ]
  · intro ζ hc hζ
    rw [push_dropA fA fB hc, hζ, dropA_addA]
  · intro ξ hξ
    change mult (addA ξ i) * incf ξ.a i i = (η.sumA + 1) * mult ξ
    rw [incf_self, ← hξ, sumA_push]
    exact mult_addA ξ i

theorem lumpSum_addB (j : Fin KB) :
    ((η.sumB + 1 : ℕ) : F) * lumpSum fA fB (fun ξ => g (addB ξ j)) η
      = lumpSum fA fB (fun ζ => (ζ.b j : F) * g ζ) (addB η (fB j)) := by
  refine lumpSum_inc_gen fA fB (fun ξ => addB ξ j) (fun ξ => ξ.dropB j) (fun ζ => ζ.b j)
    η (addB η (fB j)) (η.sumB + 1) ?_ (fun ξ => dropB_addB ξ j) (fun ζ h => addB_dropB h)
    ?_ ?_ g
  · intro ξ hξ
    rw [push_addB, hξ]
  · intro ζ hc hζ
    rw [push_dropB fA fB hc, hζ, dropB_addB]
  · intro ξ hξ
    change mult (addB ξ j) * incf ξ.b j j = (η.sumB + 1) * mult ξ
    rw [incf_self, ← hξ, sumB_push]
    exact mult_addB ξ j

theorem lumpSum_addC (i : Fin KA) (j : Fin KB) :
    ((η.t + 1 : ℕ) : F) * lumpSum fA fB (fun ξ => g (addC ξ i j)) η
      = lumpSum fA fB (fun ζ => (ζ.c i j : F) * g ζ) (addC η (fA i) (fB j)) := by
  refine lumpSum_inc_gen fA fB (fun ξ => addC ξ i j) (fun ξ => ξ.dropC i j) (fun ζ => ζ.c i j)
    η (addC η (fA i) (fB j)) (η.t + 1) ?_ (fun ξ => dropC_addC ξ i j)
    (fun ζ h => addC_dropC h) ?_ ?_ g
  · intro ξ hξ
    rw [push_addC, hξ]
  · intro ζ hc hζ
    rw [push_dropC fA fB hc, hζ, dropC_addC]
  · intro ξ hξ
    change mult (addC ξ i j) * incC ξ.c i j i j = (η.t + 1) * mult ξ
    rw [incC_self, incf_self, ← hξ, t_push]
    exact mult_addC ξ i j

theorem lumpSum_dropA (i : Fin KA) :
    lumpSum fA fB (fun ξ => (ξ.a i : F) * g (ξ.dropA i)) η
      = if η.a (fA i) = 0 then 0 else (η.sumA : F) * lumpSum fA fB g (η.dropA (fA i)) := by
  split_ifs with h0
  · refine Finset.sum_eq_zero fun ξ hξ => ?_
    have hle : ξ.a i ≤ (push fA fB ξ).a (fA i) := le_pushV fA ξ.a i
    rw [mem_fibre.mp hξ] at hle
    have hz : ξ.a i = 0 := by omega
    simp [hz]
  · have h := lumpSum_addA fA fB (fun ξ => g (ξ.dropA i)) (η.dropA (fA i)) i
    simp only [dropA_addA] at h
    rw [addA_dropA h0, Config.sumA_dropA η (fA i) h0] at h
    exact h.symm

theorem lumpSum_dropB (j : Fin KB) :
    lumpSum fA fB (fun ξ => (ξ.b j : F) * g (ξ.dropB j)) η
      = if η.b (fB j) = 0 then 0 else (η.sumB : F) * lumpSum fA fB g (η.dropB (fB j)) := by
  split_ifs with h0
  · refine Finset.sum_eq_zero fun ξ hξ => ?_
    have hle : ξ.b j ≤ (push fA fB ξ).b (fB j) := le_pushV fB ξ.b j
    rw [mem_fibre.mp hξ] at hle
    have hz : ξ.b j = 0 := by omega
    simp [hz]
  · have h := lumpSum_addB fA fB (fun ξ => g (ξ.dropB j)) (η.dropB (fB j)) j
    simp only [dropB_addB] at h
    rw [addB_dropB h0, Config.sumB_dropB η (fB j) h0] at h
    exact h.symm

theorem lumpSum_dropC (i : Fin KA) (j : Fin KB) :
    lumpSum fA fB (fun ξ => (ξ.c i j : F) * g (ξ.dropC i j)) η
      = if η.c (fA i) (fB j) = 0 then 0
        else (η.t : F) * lumpSum fA fB g (η.dropC (fA i) (fB j)) := by
  split_ifs with h0
  · refine Finset.sum_eq_zero fun ξ hξ => ?_
    have hle : ξ.c i j ≤ (push fA fB ξ).c (fA i) (fB j) := le_pushM fA fB ξ.c i j
    rw [mem_fibre.mp hξ] at hle
    have hz : ξ.c i j = 0 := by omega
    simp [hz]
  · have h := lumpSum_addC fA fB (fun ξ => g (ξ.dropC i j)) (η.dropC (fA i) (fB j)) i j
    simp only [dropC_addC] at h
    rw [addC_dropC h0, Config.t_dropC η (fA i) (fB j) h0] at h
    exact h.symm

variable [CharZero F]

theorem lumpSum_addA_inv (i : Fin KA) :
    lumpSum fA fB (fun ξ => g (addA ξ i)) η
      = ((η.sumA + 1 : ℕ) : F)⁻¹
        * lumpSum fA fB (fun ζ => (ζ.a i : F) * g ζ) (addA η (fA i)) := by
  rw [← lumpSum_addA, inv_mul_cancel_left₀ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _))]

theorem lumpSum_addB_inv (j : Fin KB) :
    lumpSum fA fB (fun ξ => g (addB ξ j)) η
      = ((η.sumB + 1 : ℕ) : F)⁻¹
        * lumpSum fA fB (fun ζ => (ζ.b j : F) * g ζ) (addB η (fB j)) := by
  rw [← lumpSum_addB, inv_mul_cancel_left₀ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _))]

theorem lumpSum_addC_inv (i : Fin KA) (j : Fin KB) :
    lumpSum fA fB (fun ξ => g (addC ξ i j)) η
      = ((η.t + 1 : ℕ) : F)⁻¹
        * lumpSum fA fB (fun ζ => (ζ.c i j : F) * g ζ) (addC η (fA i) (fB j)) := by
  rw [← lumpSum_addC, inv_mul_cancel_left₀ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _))]

end Rhone.LinearAlgebra.AlleleLumping
