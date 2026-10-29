/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.RecombinationExpansion.Source

/-! # The `t = 0` residual recursion for the `σ` coefficients -/

@[expose] public section

namespace Rhone.Probability.RecombinationExpansion

open LinearAlgebra.Recursion LinearAlgebra.Recursion.Config

variable {KA KB : ℕ} {F : Type*} [Field F]
variable {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}

theorem cRow_le_t (ξ : Config KA KB) (i : Fin KA) : ξ.cRow i ≤ ξ.t := by
  rw [ξ.t_eq_sum_cRow]
  exact Finset.single_le_sum (f := fun i' => ξ.cRow i') (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ i)

theorem cCol_le_t (ξ : Config KA KB) (j : Fin KB) : ξ.cCol j ≤ ξ.t := by
  rw [ξ.t_eq_sum_cCol]
  exact Finset.single_le_sum (f := fun j' => ξ.cCol j') (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ j)

theorem c_le_t (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) : ξ.c i j ≤ ξ.t :=
  le_trans (ξ.le_cRow i j) (cRow_le_t ξ i)

private theorem nat_mul_pred_eq_zero {x : ℕ} (h : x ≤ 1) : x * (x - 1) = 0 := by
  interval_cases x <;> rfl

theorem twoQ1_eq_zero_of_t_le_one (ξ : Config KA KB) (h : ξ.t ≤ 1) :
    twoQ1 θA θB πA πB ξ = 0 := by
  have h1 : ((ξ.t * (ξ.t - 1) : ℕ) : F) = 0 := by
    rw [nat_mul_pred_eq_zero h]; simp
  have h2 : (∑ i, ((ξ.cRow i * (ξ.cRow i - 1) : ℕ) : F) * qOne θA πA (decf ξ.mA i)) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [nat_mul_pred_eq_zero (le_trans (cRow_le_t ξ i) h)]
    simp
  have h3 : (∑ j, ((ξ.cCol j * (ξ.cCol j - 1) : ℕ) : F) * qOne θB πB (decf ξ.mB j)) = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [nat_mul_pred_eq_zero (le_trans (cCol_le_t ξ j) h)]
    simp
  have h4 : (∑ i, ∑ j, ((ξ.c i j * (ξ.c i j - 1) : ℕ) : F)
      * (qOne θA πA (decf ξ.mA i) * qOne θB πB (decf ξ.mB j))) = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    rw [show ξ.c i j * (ξ.c i j - 1) = 0 from
      nat_mul_pred_eq_zero (le_trans (c_le_t ξ i j) h)]
    simp
  rw [twoQ1, h1, h2, h3, h4]
  ring

theorem L0_eq_zero_of_vanishing (f : Config KA KB → F) (ξ : Config KA KB) (ht : ξ.t = 0)
    (h0 : f ξ = 0) (hA : ∀ i, f (ξ.dropA i) = 0) (hB : ∀ j, f (ξ.dropB j) = 0)
    (hAB : ∀ i j, f (ξ.mergeAB i j) = 0) : Analysis.RecombinationExpansion.L0 θA θB πA πB f ξ = 0 :=
        by
  have hc : ξ.c = fun _ _ => 0 := ξ.c_eq_zero_of_t ht
  have e1 : (∑ i, ((ξ.coalA i : ℕ) : F) * f (ξ.dropA i)) = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [hA i, mul_zero]
  have e2 : (∑ j, ((ξ.coalB j : ℕ) : F) * f (ξ.dropB j)) = 0 :=
    Finset.sum_eq_zero fun j _ => by rw [hB j, mul_zero]
  have e3 : (∑ i, ∑ j, ((ξ.coalC i j : ℕ) : F) * f (ξ.dropC i j)) = 0 :=
    Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by
      rw [ξ.coalC_eq_zero_of (by simp [hc])]; simp
  have e4 : (∑ i, ∑ j, ((ξ.coalAB i j : ℕ) : F) * f (ξ.mergeAB i j)) = 0 :=
    Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by rw [hAB i j, mul_zero]
  have e5 : (∑ i, πA i * (((ξ.a i : ℕ) : F) * f (ξ.dropA i)
      + ∑ j, ((ξ.c i j : ℕ) : F) * f (ξ.killA i j))) = 0 :=
    Finset.sum_eq_zero fun i _ => by
      rw [hA i, mul_zero, zero_add,
        Finset.sum_eq_zero fun j _ => by rw [show ξ.c i j = 0 by simp [hc]]; simp, mul_zero]
  have e6 : (∑ j, πB j * (((ξ.b j : ℕ) : F) * f (ξ.dropB j)
      + ∑ i, ((ξ.c i j : ℕ) : F) * f (ξ.killB i j))) = 0 :=
    Finset.sum_eq_zero fun j _ => by
      rw [hB j, mul_zero, zero_add,
        Finset.sum_eq_zero fun i _ => by rw [show ξ.c i j = 0 by simp [hc]]; simp, mul_zero]
  rw [Analysis.RecombinationExpansion.L0, Analysis.RecombinationExpansion.Lop, rhs, e1, e2, e3, e4,
      e5, e6, h0]
  ring

theorem L0_twoQ1_eq_zero (ξ : Config KA KB) (ht : ξ.t = 0) :
    Analysis.RecombinationExpansion.L0 θA θB πA πB (twoQ1 θA θB πA πB) ξ = 0 := by
  refine L0_eq_zero_of_vanishing _ ξ ht (twoQ1_eq_zero_of_t_le_one ξ (by omega))
    (fun i => twoQ1_eq_zero_of_t_le_one _ (by rw [ξ.t_dropA i]; omega))
    (fun j => twoQ1_eq_zero_of_t_le_one _ (by rw [ξ.t_dropB j]; omega))
    (fun i j => twoQ1_eq_zero_of_t_le_one _ ?_)
  rw [ξ.t_mergeAB i j, ht]

theorem sigma_rec_eq {σ Ref : Config KA KB → F} (ξ : Config KA KB) (S : F)
    (hRef : ∀ i j, ξ.c i j ≠ 0 → Ref (ξ.split i j) = Ref ξ)
    (hk1 : Analysis.RecombinationExpansion.L1 (fun η => Ref η + σ η) ξ = S) :
    ((ξ.t : ℕ) : F) * σ ξ
      = (∑ i, ∑ j, ((ξ.c i j : ℕ) : F) * σ (ξ.split i j)) + S := by
  rw [Analysis.RecombinationExpansion.L1_add, Analysis.RecombinationExpansion.L1_of_sector_const ξ
      hRef, zero_add] at hk1
  rw [Analysis.RecombinationExpansion.L1] at hk1
  linear_combination hk1

theorem rhs_of_t_eq_zero (q : Config KA KB → F) (ξ : Config KA KB) (ht : ξ.t = 0) :
    rhs θA θB 0 πA πB q ξ
      = (∑ i, (((ξ.a i * (ξ.a i - 1) : ℕ) : F) + θA * πA i * ((ξ.a i : ℕ) : F))
          * q (ξ.dropA i))
        + (∑ j, (((ξ.b j * (ξ.b j - 1) : ℕ) : F) + θB * πB j * ((ξ.b j : ℕ) : F))
            * q (ξ.dropB j))
        + (∑ i, ∑ j, ((ξ.coalAB i j : ℕ) : F) * q (ξ.mergeAB i j)) := by
  have hc : ξ.c = fun _ _ => 0 := ξ.c_eq_zero_of_t ht
  have e1 : ∀ i : Fin KA, ξ.coalA i = ξ.a i * (ξ.a i - 1) := by
    intro i; simp [Config.coalA, Config.cRow, hc]
  have e2 : ∀ j : Fin KB, ξ.coalB j = ξ.b j * (ξ.b j - 1) := by
    intro j; simp [Config.coalB, Config.cCol, hc]
  have e3 : (∑ i, ∑ j, ((ξ.coalC i j : ℕ) : F) * q (ξ.dropC i j)) = 0 :=
    Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by
      rw [ξ.coalC_eq_zero_of (by simp [hc])]; simp
  have e5 : (∑ i, πA i * (((ξ.a i : ℕ) : F) * q (ξ.dropA i)
      + ∑ j, ((ξ.c i j : ℕ) : F) * q (ξ.killA i j)))
      = ∑ i, πA i * ((ξ.a i : ℕ) : F) * q (ξ.dropA i) :=
    Finset.sum_congr rfl fun i _ => by
      rw [Finset.sum_eq_zero fun j _ => by rw [show ξ.c i j = 0 by simp [hc]]; simp, add_zero]
      ring
  have e6 : (∑ j, πB j * (((ξ.b j : ℕ) : F) * q (ξ.dropB j)
      + ∑ i, ((ξ.c i j : ℕ) : F) * q (ξ.killB i j)))
      = ∑ j, πB j * ((ξ.b j : ℕ) : F) * q (ξ.dropB j) :=
    Finset.sum_congr rfl fun j _ => by
      rw [Finset.sum_eq_zero fun i _ => by rw [show ξ.c i j = 0 by simp [hc]]; simp, add_zero]
      ring
  have mA : (∑ i, ((ξ.coalA i : ℕ) : F) * q (ξ.dropA i))
      + θA * (∑ i, πA i * ((ξ.a i : ℕ) : F) * q (ξ.dropA i))
      = ∑ i, (((ξ.a i * (ξ.a i - 1) : ℕ) : F) + θA * πA i * ((ξ.a i : ℕ) : F))
          * q (ξ.dropA i) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [e1 i]
    ring
  have mB : (∑ j, ((ξ.coalB j : ℕ) : F) * q (ξ.dropB j))
      + θB * (∑ j, πB j * ((ξ.b j : ℕ) : F) * q (ξ.dropB j))
      = ∑ j, (((ξ.b j * (ξ.b j - 1) : ℕ) : F) + θB * πB j * ((ξ.b j : ℕ) : F))
          * q (ξ.dropB j) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [e2 j]
    ring
  rw [rhs, e3, e5, e6, ← mA, ← mB]
  ring

theorem residual_t_zero {q2 σ : Config KA KB → F} (ξ : Config KA KB) (ht : ξ.t = 0)
    (hL0 : Analysis.RecombinationExpansion.L0 θA θB πA πB q2 ξ = 0)
    (hsplit : ∀ i j, ξ.a i ≠ 0 → ξ.b j ≠ 0 →
      q2 (ξ.mergeAB i j) = q2 ξ + σ (ξ.mergeAB i j)) :
    (((ξ.nA * (ξ.nA - 1) : ℕ) : F) + θA * ((ξ.nA : ℕ) : F)
        + ((ξ.nB * (ξ.nB - 1) : ℕ) : F) + θB * ((ξ.nB : ℕ) : F)) * q2 ξ
      = (∑ i, (((ξ.a i * (ξ.a i - 1) : ℕ) : F) + θA * πA i * ((ξ.a i : ℕ) : F))
          * q2 (ξ.dropA i))
        + (∑ j, (((ξ.b j * (ξ.b j - 1) : ℕ) : F) + θB * πB j * ((ξ.b j : ℕ) : F))
            * q2 (ξ.dropB j))
        + (∑ i, ∑ j, ((ξ.coalAB i j : ℕ) : F) * σ (ξ.mergeAB i j)) := by
  have hmerge : (∑ i, ∑ j, ((ξ.coalAB i j : ℕ) : F) * q2 (ξ.mergeAB i j))
      = 2 * ((ξ.sumA * ξ.sumB : ℕ) : F) * q2 ξ
        + ∑ i, ∑ j, ((ξ.coalAB i j : ℕ) : F) * σ (ξ.mergeAB i j) := by
    have hstep : ∀ i : Fin KA, ∀ j : Fin KB,
        ((ξ.coalAB i j : ℕ) : F) * q2 (ξ.mergeAB i j)
          = ((ξ.coalAB i j : ℕ) : F) * q2 ξ
            + ((ξ.coalAB i j : ℕ) : F) * σ (ξ.mergeAB i j) := by
      intro i j
      by_cases ha : ξ.a i = 0
      · rw [ξ.coalAB_eq_zero_left j ha]; simp
      by_cases hb : ξ.b j = 0
      · rw [ξ.coalAB_eq_zero_right i hb]; simp
      · rw [hsplit i j ha hb]; ring
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hstep i j]
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib, Finset.sum_add_distrib]
    congr 1
    simp only [← Finset.sum_mul]
    rw [Analysis.RecombinationExpansion.cast_sum_coalAB ξ]
  have hbk : ((ξ.n * (ξ.n - 1) : ℕ) : F)
      = ((ξ.nA * (ξ.nA - 1) : ℕ) : F) + ((ξ.nB * (ξ.nB - 1) : ℕ) : F)
        + 2 * ((ξ.sumA * ξ.sumB : ℕ) : F) := by
    have h := ξ.bookkeeping_diag
    rw [ht] at h
    have h' : ((ξ.n * (ξ.n - 1) + 0 * (0 - 1) : ℕ) : F)
        = ((ξ.nA * (ξ.nA - 1) + ξ.nB * (ξ.nB - 1) + 2 * (ξ.sumA * ξ.sumB) : ℕ) : F) := by
      rw [h]
    push_cast at h'
    push_cast
    linear_combination h'
  have hd : diag θA θB 0 ξ
      = ((ξ.n * (ξ.n - 1) : ℕ) : F) + θA * ((ξ.nA : ℕ) : F) + θB * ((ξ.nB : ℕ) : F) := by
    rw [diag, ht]
    simp
  rw [Analysis.RecombinationExpansion.L0, Analysis.RecombinationExpansion.Lop, hd, rhs_of_t_eq_zero
      q2 ξ ht, hmerge] at hL0
  linear_combination hL0 - q2 ξ * hbk

end Rhone.Probability.RecombinationExpansion
