/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.AlleleLumping.Lump

/-! # The lumped sum of the right-hand side of the recursion -/

@[expose] public section

namespace Rhone.LinearAlgebra.AlleleLumping

open Finset Recursion Recursion.Config

variable {KA KB KA' KB' : ℕ} {F : Type*} [Field F]

noncomputable def urhs (θA θB ρ : F) (πA : Fin KA → F) (πB : Fin KB → F)
    (P : Config KA KB → F) (η : Config KA KB) : F :=
  (∑ p, if η.a p = 0 then 0 else
      (η.sumA : F) * ((η.a p - 1 + 2 * η.cRow p : ℕ) : F) * P (η.dropA p))
    + (∑ r, if η.b r = 0 then 0 else
      (η.sumB : F) * ((η.b r - 1 + 2 * η.cCol r : ℕ) : F) * P (η.dropB r))
    + (∑ p, ∑ r, if η.c p r = 0 then 0 else
      (η.t : F) * ((η.c p r - 1 : ℕ) : F) * P (η.dropC p r))
    + (∑ p, ∑ r, if η.a p = 0 ∨ η.b r = 0 then 0 else
      (2 * (η.sumA : F) * (η.sumB : F) * ((η.t + 1 : ℕ) : F)⁻¹)
        * ((η.c p r + 1 : ℕ) : F) * P (η.mergeAB p r))
    + θA * ∑ p, πA p * ((if η.a p = 0 then 0 else (η.sumA : F) * P (η.dropA p))
        + ∑ r, if η.c p r = 0 then 0 else
          ((η.t : F) * ((η.sumB + 1 : ℕ) : F)⁻¹) * ((η.b r + 1 : ℕ) : F) * P (η.killA p r))
    + θB * ∑ r, πB r * ((if η.b r = 0 then 0 else (η.sumB : F) * P (η.dropB r))
        + ∑ p, if η.c p r = 0 then 0 else
          ((η.t : F) * ((η.sumA + 1 : ℕ) : F)⁻¹) * ((η.a p + 1 : ℕ) : F) * P (η.killB p r))
    + ρ * ∑ p, ∑ r, if η.c p r = 0 then 0 else
        ((η.t : F) * ((η.sumA + 1 : ℕ) : F)⁻¹ * ((η.sumB + 1 : ℕ) : F)⁻¹)
          * (((η.a p + 1 : ℕ) : F) * ((η.b r + 1 : ℕ) : F)) * P (η.split p r)

variable (fA : Fin KA → Fin KA') (fB : Fin KB → Fin KB')
variable (q : Config KA KB → F) (η : Config KA' KB')

theorem lumpSum_coalA :
    lumpSum fA fB (fun ξ => ∑ i, ((ξ.coalA i : ℕ) : F) * q (ξ.dropA i)) η
      = ∑ p, if η.a p = 0 then 0 else
          (η.sumA : F) * ((η.a p - 1 + 2 * η.cRow p : ℕ) : F)
            * lumpSum fA fB q (η.dropA p) := by
  rw [lumpSum_sum]
  have hterm : ∀ i, lumpSum fA fB (fun ξ => ((ξ.coalA i : ℕ) : F) * q (ξ.dropA i)) η
      = if η.a (fA i) = 0 then 0 else (η.sumA : F) *
          lumpSum fA fB (fun ζ => ((ζ.a i + 2 * ζ.cRow i : ℕ) : F) * q ζ)
            (η.dropA (fA i)) := by
    intro i
    rw [← lumpSum_dropA fA fB (fun ζ => ((ζ.a i + 2 * ζ.cRow i : ℕ) : F) * q ζ) η i]
    refine lumpSum_congr fun ξ _ => ?_
    have h1 : (ξ.dropA i).a i = ξ.a i - 1 := decf_self _ _
    have h2 : (ξ.dropA i).cRow i = ξ.cRow i := rfl
    rw [h1, h2, coalA, Nat.cast_mul, mul_assoc]
  simp only [hterm]
  refine sum_fib_lumpSum fA fB fA (fun p => η.a p = 0) (fun _ => (η.sumA : F))
    (fun i ζ => ((ζ.a i + 2 * ζ.cRow i : ℕ) : F)) q (fun p => η.dropA p)
    (fun p => ((η.a p - 1 + 2 * η.cRow p : ℕ) : F)) (fun p ζ hζ => ?_)
  have ha : ∑ i with fA i = p, ζ.a i = (push fA fB ζ).a p := rfl
  rw [← Nat.cast_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← cRow_push fA fB ζ p, ha, hζ]
  congr 1
  change decf η.a p p + 2 * η.cRow p = _
  rw [decf_self]

theorem lumpSum_coalB :
    lumpSum fA fB (fun ξ => ∑ j, ((ξ.coalB j : ℕ) : F) * q (ξ.dropB j)) η
      = ∑ r, if η.b r = 0 then 0 else
          (η.sumB : F) * ((η.b r - 1 + 2 * η.cCol r : ℕ) : F)
            * lumpSum fA fB q (η.dropB r) := by
  rw [lumpSum_sum]
  have hterm : ∀ j, lumpSum fA fB (fun ξ => ((ξ.coalB j : ℕ) : F) * q (ξ.dropB j)) η
      = if η.b (fB j) = 0 then 0 else (η.sumB : F) *
          lumpSum fA fB (fun ζ => ((ζ.b j + 2 * ζ.cCol j : ℕ) : F) * q ζ)
            (η.dropB (fB j)) := by
    intro j
    rw [← lumpSum_dropB fA fB (fun ζ => ((ζ.b j + 2 * ζ.cCol j : ℕ) : F) * q ζ) η j]
    refine lumpSum_congr fun ξ _ => ?_
    have h1 : (ξ.dropB j).b j = ξ.b j - 1 := decf_self _ _
    have h2 : (ξ.dropB j).cCol j = ξ.cCol j := rfl
    rw [h1, h2, coalB, Nat.cast_mul, mul_assoc]
  simp only [hterm]
  refine sum_fib_lumpSum fA fB fB (fun r => η.b r = 0) (fun _ => (η.sumB : F))
    (fun j ζ => ((ζ.b j + 2 * ζ.cCol j : ℕ) : F)) q (fun r => η.dropB r)
    (fun r => ((η.b r - 1 + 2 * η.cCol r : ℕ) : F)) (fun r ζ hζ => ?_)
  have hb : ∑ j with fB j = r, ζ.b j = (push fA fB ζ).b r := rfl
  rw [← Nat.cast_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← cCol_push fA fB ζ r, hb, hζ]
  congr 1
  change decf η.b r r + 2 * η.cCol r = _
  rw [decf_self]

theorem lumpSum_coalC :
    lumpSum fA fB (fun ξ => ∑ i, ∑ j, ((ξ.coalC i j : ℕ) : F) * q (ξ.dropC i j)) η
      = ∑ p, ∑ r, if η.c p r = 0 then 0 else
          (η.t : F) * ((η.c p r - 1 : ℕ) : F) * lumpSum fA fB q (η.dropC p r) := by
  simp only [lumpSum_sum]
  have hterm : ∀ i j, lumpSum fA fB (fun ξ => ((ξ.coalC i j : ℕ) : F) * q (ξ.dropC i j)) η
      = if η.c (fA i) (fB j) = 0 then 0 else (η.t : F) *
          lumpSum fA fB (fun ζ => (ζ.c i j : F) * q ζ) (η.dropC (fA i) (fB j)) := by
    intro i j
    rw [← lumpSum_dropC fA fB (fun ζ => (ζ.c i j : F) * q ζ) η i j]
    refine lumpSum_congr fun ξ _ => ?_
    have h1 : (ξ.dropC i j).c i j = ξ.c i j - 1 := by
      change decC ξ.c i j i j = _
      rw [decC_self, decf_self]
    rw [h1, coalC, Nat.cast_mul, mul_assoc]
  simp only [hterm]
  refine sum_fib_lumpSum₂ fA fB (fun p r => η.c p r = 0) (fun _ _ => (η.t : F))
    (fun i j ζ => (ζ.c i j : F)) q (fun p r => η.dropC p r)
    (fun p r => ((η.c p r - 1 : ℕ) : F)) (fun p r ζ hζ => ?_)
  have hc : ∑ i with fA i = p, ∑ j with fB j = r, ζ.c i j = (push fA fB ζ).c p r := rfl
  simp only [← Nat.cast_sum]
  rw [hc, hζ]
  congr 1
  change decC η.c p r p r = _
  rw [decC_self, decf_self]

variable [CharZero F]

theorem lumpSum_coalAB :
    lumpSum fA fB (fun ξ => ∑ i, ∑ j, ((ξ.coalAB i j : ℕ) : F) * q (ξ.mergeAB i j)) η
      = ∑ p, ∑ r, if η.a p = 0 ∨ η.b r = 0 then 0 else
          (2 * (η.sumA : F) * (η.sumB : F) * ((η.t + 1 : ℕ) : F)⁻¹)
            * ((η.c p r + 1 : ℕ) : F) * lumpSum fA fB q (η.mergeAB p r) := by
  simp only [lumpSum_sum]
  have hterm : ∀ i j, lumpSum fA fB (fun ξ => ((ξ.coalAB i j : ℕ) : F) * q (ξ.mergeAB i j)) η
      = if η.a (fA i) = 0 ∨ η.b (fB j) = 0 then 0 else
          (2 * (η.sumA : F) * (η.sumB : F) * ((η.t + 1 : ℕ) : F)⁻¹)
            * lumpSum fA fB (fun ζ => (ζ.c i j : F) * q ζ) (η.mergeAB (fA i) (fB j)) := by
    intro i j
    have e1 : lumpSum fA fB (fun ξ => ((ξ.coalAB i j : ℕ) : F) * q (ξ.mergeAB i j)) η
        = 2 * lumpSum fA fB (fun ξ => (ξ.a i : F) * ((ξ.b j : F) * q (ξ.mergeAB i j))) η := by
      rw [← lumpSum_const_mul]
      refine lumpSum_congr fun ξ _ => ?_
      rw [coalAB]
      push_cast
      ring
    have s1 : lumpSum fA fB (fun ξ => (ξ.a i : F) * ((ξ.b j : F) * q (ξ.mergeAB i j))) η
        = if η.a (fA i) = 0 then 0 else (η.sumA : F) *
            lumpSum fA fB (fun ζ => (ζ.b j : F) * q (addC (ζ.dropB j) i j))
              (η.dropA (fA i)) :=
      lumpSum_dropA fA fB (fun ζ => (ζ.b j : F) * q (addC (ζ.dropB j) i j)) η i
    have s2 : lumpSum fA fB (fun ζ => (ζ.b j : F) * q (addC (ζ.dropB j) i j))
          (η.dropA (fA i))
        = if η.b (fB j) = 0 then 0 else (η.sumB : F) *
            lumpSum fA fB (fun ζ => q (addC ζ i j)) ((η.dropA (fA i)).dropB (fB j)) :=
      lumpSum_dropB fA fB (fun ζ => q (addC ζ i j)) (η.dropA (fA i)) j
    have s3 : lumpSum fA fB (fun ζ => q (addC ζ i j)) ((η.dropA (fA i)).dropB (fB j))
        = ((η.t + 1 : ℕ) : F)⁻¹
          * lumpSum fA fB (fun ζ => (ζ.c i j : F) * q ζ) (η.mergeAB (fA i) (fB j)) :=
      lumpSum_addC_inv fA fB q ((η.dropA (fA i)).dropB (fB j)) i j
    rw [e1, s1, s2, s3]
    by_cases ha : η.a (fA i) = 0
    · simp [ha]
    by_cases hb : η.b (fB j) = 0
    · simp [hb]
    rw [ite_eq_right ha, ite_eq_right hb, ite_eq_right (not_or.mpr ⟨ha, hb⟩)]
    ring
  simp only [hterm]
  refine sum_fib_lumpSum₂ fA fB (fun p r => η.a p = 0 ∨ η.b r = 0)
    (fun _ _ => 2 * (η.sumA : F) * (η.sumB : F) * ((η.t + 1 : ℕ) : F)⁻¹)
    (fun i j ζ => (ζ.c i j : F)) q (fun p r => η.mergeAB p r)
    (fun p r => ((η.c p r + 1 : ℕ) : F)) (fun p r ζ hζ => ?_)
  have hc : ∑ i with fA i = p, ∑ j with fB j = r, ζ.c i j = (push fA fB ζ).c p r := rfl
  simp only [← Nat.cast_sum]
  rw [hc, hζ]
  congr 1
  change incC η.c p r p r = _
  rw [incC_self, incf_self]

theorem lumpSum_killA (πA : Fin KA → F) :
    lumpSum fA fB (fun ξ => ∑ i, πA i * (((ξ.a i : ℕ) : F) * q (ξ.dropA i)
        + ∑ j, ((ξ.c i j : ℕ) : F) * q (ξ.killA i j))) η
      = ∑ p, pushPi fA πA p
          * ((if η.a p = 0 then 0 else (η.sumA : F) * lumpSum fA fB q (η.dropA p))
            + ∑ r, if η.c p r = 0 then 0 else
              ((η.t : F) * ((η.sumB + 1 : ℕ) : F)⁻¹) * ((η.b r + 1 : ℕ) : F)
                * lumpSum fA fB q (η.killA p r)) := by
  simp only [lumpSum_sum, lumpSum_const_mul, lumpSum_add]
  have hterm : ∀ i j, lumpSum fA fB (fun ξ => (ξ.c i j : F) * q (ξ.killA i j)) η
      = if η.c (fA i) (fB j) = 0 then 0 else
          ((η.t : F) * ((η.sumB + 1 : ℕ) : F)⁻¹)
            * lumpSum fA fB (fun ζ => (ζ.b j : F) * q ζ) (η.killA (fA i) (fB j)) := by
    intro i j
    have s1 : lumpSum fA fB (fun ξ => (ξ.c i j : F) * q (ξ.killA i j)) η
        = if η.c (fA i) (fB j) = 0 then 0 else (η.t : F) *
            lumpSum fA fB (fun ζ => q (addB ζ j)) (η.dropC (fA i) (fB j)) :=
      lumpSum_dropC fA fB (fun ζ => q (addB ζ j)) η i j
    have s2 : lumpSum fA fB (fun ζ => q (addB ζ j)) (η.dropC (fA i) (fB j))
        = ((η.sumB + 1 : ℕ) : F)⁻¹
          * lumpSum fA fB (fun ζ => (ζ.b j : F) * q ζ) (η.killA (fA i) (fB j)) :=
      lumpSum_addB_inv fA fB q (η.dropC (fA i) (fB j)) j
    rw [s1, s2]
    split_ifs
    · rfl
    · ring
  have hdrop : ∀ i, lumpSum fA fB (fun ξ => (ξ.a i : F) * q (ξ.dropA i)) η
      = if η.a (fA i) = 0 then 0 else (η.sumA : F) * lumpSum fA fB q (η.dropA (fA i)) :=
    fun i => lumpSum_dropA fA fB q η i
  simp only [hterm, hdrop]
  have hinner : ∀ p, (∑ j, if η.c p (fB j) = 0 then 0 else
        ((η.t : F) * ((η.sumB + 1 : ℕ) : F)⁻¹)
          * lumpSum fA fB (fun ζ => (ζ.b j : F) * q ζ) (η.killA p (fB j)))
      = ∑ r, if η.c p r = 0 then 0 else
          ((η.t : F) * ((η.sumB + 1 : ℕ) : F)⁻¹) * ((η.b r + 1 : ℕ) : F)
            * lumpSum fA fB q (η.killA p r) := by
    intro p
    refine sum_fib_lumpSum fA fB fB (fun r => η.c p r = 0)
      (fun _ => (η.t : F) * ((η.sumB + 1 : ℕ) : F)⁻¹) (fun j ζ => (ζ.b j : F)) q
      (fun r => η.killA p r) (fun r => ((η.b r + 1 : ℕ) : F)) (fun r ζ hζ => ?_)
    have hb : ∑ j with fB j = r, ζ.b j = (push fA fB ζ).b r := rfl
    rw [← Nat.cast_sum, hb, hζ]
    congr 1
    change incf η.b r r = _
    rw [incf_self]
  simp only [hinner]
  exact sum_pushPi fA πA (fun p =>
    (if η.a p = 0 then 0 else (η.sumA : F) * lumpSum fA fB q (η.dropA p))
      + ∑ r, if η.c p r = 0 then 0 else
        ((η.t : F) * ((η.sumB + 1 : ℕ) : F)⁻¹) * ((η.b r + 1 : ℕ) : F)
          * lumpSum fA fB q (η.killA p r))

theorem lumpSum_killB (πB : Fin KB → F) :
    lumpSum fA fB (fun ξ => ∑ j, πB j * (((ξ.b j : ℕ) : F) * q (ξ.dropB j)
        + ∑ i, ((ξ.c i j : ℕ) : F) * q (ξ.killB i j))) η
      = ∑ r, pushPi fB πB r
          * ((if η.b r = 0 then 0 else (η.sumB : F) * lumpSum fA fB q (η.dropB r))
            + ∑ p, if η.c p r = 0 then 0 else
              ((η.t : F) * ((η.sumA + 1 : ℕ) : F)⁻¹) * ((η.a p + 1 : ℕ) : F)
                * lumpSum fA fB q (η.killB p r)) := by
  simp only [lumpSum_sum, lumpSum_const_mul, lumpSum_add]
  have hterm : ∀ i j, lumpSum fA fB (fun ξ => (ξ.c i j : F) * q (ξ.killB i j)) η
      = if η.c (fA i) (fB j) = 0 then 0 else
          ((η.t : F) * ((η.sumA + 1 : ℕ) : F)⁻¹)
            * lumpSum fA fB (fun ζ => (ζ.a i : F) * q ζ) (η.killB (fA i) (fB j)) := by
    intro i j
    have s1 : lumpSum fA fB (fun ξ => (ξ.c i j : F) * q (ξ.killB i j)) η
        = if η.c (fA i) (fB j) = 0 then 0 else (η.t : F) *
            lumpSum fA fB (fun ζ => q (addA ζ i)) (η.dropC (fA i) (fB j)) :=
      lumpSum_dropC fA fB (fun ζ => q (addA ζ i)) η i j
    have s2 : lumpSum fA fB (fun ζ => q (addA ζ i)) (η.dropC (fA i) (fB j))
        = ((η.sumA + 1 : ℕ) : F)⁻¹
          * lumpSum fA fB (fun ζ => (ζ.a i : F) * q ζ) (η.killB (fA i) (fB j)) :=
      lumpSum_addA_inv fA fB q (η.dropC (fA i) (fB j)) i
    rw [s1, s2]
    split_ifs
    · rfl
    · ring
  have hdrop : ∀ j, lumpSum fA fB (fun ξ => (ξ.b j : F) * q (ξ.dropB j)) η
      = if η.b (fB j) = 0 then 0 else (η.sumB : F) * lumpSum fA fB q (η.dropB (fB j)) :=
    fun j => lumpSum_dropB fA fB q η j
  simp only [hterm, hdrop]
  have hinner : ∀ r, (∑ i, if η.c (fA i) r = 0 then 0 else
        ((η.t : F) * ((η.sumA + 1 : ℕ) : F)⁻¹)
          * lumpSum fA fB (fun ζ => (ζ.a i : F) * q ζ) (η.killB (fA i) r))
      = ∑ p, if η.c p r = 0 then 0 else
          ((η.t : F) * ((η.sumA + 1 : ℕ) : F)⁻¹) * ((η.a p + 1 : ℕ) : F)
            * lumpSum fA fB q (η.killB p r) := by
    intro r
    refine sum_fib_lumpSum fA fB fA (fun p => η.c p r = 0)
      (fun _ => (η.t : F) * ((η.sumA + 1 : ℕ) : F)⁻¹) (fun i ζ => (ζ.a i : F)) q
      (fun p => η.killB p r) (fun p => ((η.a p + 1 : ℕ) : F)) (fun p ζ hζ => ?_)
    have ha : ∑ i with fA i = p, ζ.a i = (push fA fB ζ).a p := rfl
    rw [← Nat.cast_sum, ha, hζ]
    congr 1
    change incf η.a p p = _
    rw [incf_self]
  simp only [hinner]
  exact sum_pushPi fB πB (fun r =>
    (if η.b r = 0 then 0 else (η.sumB : F) * lumpSum fA fB q (η.dropB r))
      + ∑ p, if η.c p r = 0 then 0 else
        ((η.t : F) * ((η.sumA + 1 : ℕ) : F)⁻¹) * ((η.a p + 1 : ℕ) : F)
          * lumpSum fA fB q (η.killB p r))

theorem lumpSum_split :
    lumpSum fA fB (fun ξ => ∑ i, ∑ j, ((ξ.c i j : ℕ) : F) * q (ξ.split i j)) η
      = ∑ p, ∑ r, if η.c p r = 0 then 0 else
          ((η.t : F) * ((η.sumA + 1 : ℕ) : F)⁻¹ * ((η.sumB + 1 : ℕ) : F)⁻¹)
            * (((η.a p + 1 : ℕ) : F) * ((η.b r + 1 : ℕ) : F))
            * lumpSum fA fB q (η.split p r) := by
  simp only [lumpSum_sum]
  have hterm : ∀ i j, lumpSum fA fB (fun ξ => (ξ.c i j : F) * q (ξ.split i j)) η
      = if η.c (fA i) (fB j) = 0 then 0 else
          ((η.t : F) * ((η.sumA + 1 : ℕ) : F)⁻¹ * ((η.sumB + 1 : ℕ) : F)⁻¹)
            * lumpSum fA fB (fun ζ => ((ζ.a i : F) * (ζ.b j : F)) * q ζ)
              (η.split (fA i) (fB j)) := by
    intro i j
    have s1 : lumpSum fA fB (fun ξ => (ξ.c i j : F) * q (ξ.split i j)) η
        = if η.c (fA i) (fB j) = 0 then 0 else (η.t : F) *
            lumpSum fA fB (fun ζ => q (addA (addB ζ j) i)) (η.dropC (fA i) (fB j)) :=
      lumpSum_dropC fA fB (fun ζ => q (addA (addB ζ j) i)) η i j
    have s2 : lumpSum fA fB (fun ζ => q (addA (addB ζ j) i)) (η.dropC (fA i) (fB j))
        = ((η.sumB + 1 : ℕ) : F)⁻¹
          * lumpSum fA fB (fun ζ => (ζ.b j : F) * q (addA ζ i))
            (addB (η.dropC (fA i) (fB j)) (fB j)) :=
      lumpSum_addB_inv fA fB (fun ζ => q (addA ζ i)) (η.dropC (fA i) (fB j)) j
    have s3 : lumpSum fA fB (fun ζ => (ζ.b j : F) * q (addA ζ i))
          (addB (η.dropC (fA i) (fB j)) (fB j))
        = ((η.sumA + 1 : ℕ) : F)⁻¹
          * lumpSum fA fB (fun ζ => (ζ.a i : F) * ((ζ.b j : F) * q ζ))
            (η.split (fA i) (fB j)) :=
      lumpSum_addA_inv fA fB (fun ζ => (ζ.b j : F) * q ζ)
        (addB (η.dropC (fA i) (fB j)) (fB j)) i
    have s4 : lumpSum fA fB (fun ζ => (ζ.a i : F) * ((ζ.b j : F) * q ζ))
          (η.split (fA i) (fB j))
        = lumpSum fA fB (fun ζ => ((ζ.a i : F) * (ζ.b j : F)) * q ζ)
          (η.split (fA i) (fB j)) :=
      lumpSum_congr fun ζ _ => (mul_assoc _ _ _).symm
    rw [s1, s2, s3, s4]
    split_ifs
    · rfl
    · ring
  simp only [hterm]
  refine sum_fib_lumpSum₂ fA fB (fun p r => η.c p r = 0)
    (fun _ _ => (η.t : F) * ((η.sumA + 1 : ℕ) : F)⁻¹ * ((η.sumB + 1 : ℕ) : F)⁻¹)
    (fun i j ζ => (ζ.a i : F) * (ζ.b j : F)) q (fun p r => η.split p r)
    (fun p r => ((η.a p + 1 : ℕ) : F) * ((η.b r + 1 : ℕ) : F)) (fun p r ζ hζ => ?_)
  have ha : ∑ i with fA i = p, ζ.a i = (push fA fB ζ).a p := rfl
  have hb : ∑ j with fB j = r, ζ.b j = (push fA fB ζ).b r := rfl
  rw [← Finset.sum_mul_sum, ← Nat.cast_sum, ← Nat.cast_sum, ha, hb, hζ]
  congr 2
  · change incf η.a p p = _
    rw [incf_self]
  · change incf η.b r r = _
    rw [incf_self]

theorem lumpSum_rhs (θA θB ρ : F) (πA : Fin KA → F) (πB : Fin KB → F) :
    lumpSum fA fB (rhs θA θB ρ πA πB q) η
      = urhs θA θB ρ (pushPi fA πA) (pushPi fB πB) (lumpSum fA fB q) η := by
  change lumpSum fA fB (fun ξ => rhs θA θB ρ πA πB q ξ) η = _
  simp only [rhs]
  rw [lumpSum_add, lumpSum_add, lumpSum_add, lumpSum_add, lumpSum_add, lumpSum_add,
    lumpSum_const_mul, lumpSum_const_mul, lumpSum_const_mul,
    lumpSum_coalA, lumpSum_coalB, lumpSum_coalC, lumpSum_coalAB, lumpSum_killA, lumpSum_killB,
    lumpSum_split]
  rfl

end Rhone.LinearAlgebra.AlleleLumping
