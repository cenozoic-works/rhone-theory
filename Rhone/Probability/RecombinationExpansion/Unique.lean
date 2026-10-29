/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.RecombinationExpansion.Transport

/-! # Uniqueness of the power-series solution -/

@[expose] public section

namespace Rhone.Probability.RecombinationExpansion

open LinearAlgebra.Recursion LinearAlgebra.Recursion.Config Analysis.RecombinationExpansion

variable {KA KB : ℕ} {F : Type*} [Field F] [CharZero F]
variable {θA θB : F} {πA : Fin KA → F} {πB : Fin KB → F}

theorem eq_zero_of_L1_eq_zero (d : Config KA KB → F)
    (h0 : ∀ ξ : Config KA KB, ξ.t = 0 → d ξ = 0)
    (hb : ∀ ξ : Config KA KB, ξ.n ≤ 1 → d ξ = 0)
    (hL : ∀ ξ : Config KA KB, 2 ≤ ξ.n → L1 d ξ = 0) :
    ∀ ξ : Config KA KB, d ξ = 0 := by
  have main : ∀ m : ℕ, ∀ ξ : Config KA KB, ξ.t = m → d ξ = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro ξ hξ
      rcases Nat.eq_zero_or_pos m with hm | hm
      · exact h0 ξ (by omega)
      rcases Nat.lt_or_ge ξ.n 2 with hn | hn
      · exact hb ξ (by omega)
      have hsum : ∑ i, ∑ j, ((ξ.c i j : ℕ) : F) * d (ξ.split i j) = 0 := by
        refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
        by_cases hc : ξ.c i j = 0
        · rw [hc]
          simp
        · have hlt : (ξ.split i j).t < m := by
            have hts := L1_level ξ i j hc
            omega
          rw [ih (ξ.split i j).t hlt (ξ.split i j) rfl, mul_zero]
      have h := hL ξ (by omega)
      rw [L1, hsum, sub_zero] at h
      have ht : ((ξ.t : ℕ) : F) ≠ 0 := by
        rw [hξ]
        exact Nat.cast_ne_zero.mpr (by omega)
      exact (mul_eq_zero.mp h).resolve_left ht
  exact fun ξ => main ξ.t ξ rfl

theorem eq_of_LTrans_eq (Q Q' : Config KA KB → PowerSeries F)
    (h0 : ∀ ξ : Config KA KB, ξ.t = 0 → Q ξ = Q' ξ)
    (hb : ∀ ξ : Config KA KB, ξ.n ≤ 1 → Q ξ = Q' ξ)
    (heq : ∀ ξ : Config KA KB, 2 ≤ ξ.n →
      LTrans θA θB πA πB Q ξ = LTrans θA θB πA πB Q' ξ) :
    Q = Q' := by
  have key : ∀ k : ℕ, ∀ ξ : Config KA KB,
      PowerSeries.coeff k (Q ξ) - PowerSeries.coeff k (Q' ξ) = 0 := by
    intro k
    induction k with
    | zero =>
      refine eq_zero_of_L1_eq_zero
        (fun η => PowerSeries.coeff 0 (Q η) - PowerSeries.coeff 0 (Q' η))
        (fun ξ hξ => by rw [h0 ξ hξ, sub_self]) (fun ξ hξ => by rw [hb ξ hξ, sub_self]) ?_
      intro ξ hn
      have h := congrArg (PowerSeries.coeff 0) (heq ξ hn)
      rw [coeff_zero_LTrans, coeff_zero_LTrans] at h
      rw [L1_sub (fun η => PowerSeries.coeff 0 (Q η))
        (fun η => PowerSeries.coeff 0 (Q' η)) ξ, h, sub_self]
    | succ k ih =>
      refine eq_zero_of_L1_eq_zero
        (fun η => PowerSeries.coeff (k + 1) (Q η) - PowerSeries.coeff (k + 1) (Q' η))
        (fun ξ hξ => by rw [h0 ξ hξ, sub_self]) (fun ξ hξ => by rw [hb ξ hξ, sub_self]) ?_
      intro ξ hn
      have h := congrArg (PowerSeries.coeff (k + 1)) (heq ξ hn)
      rw [coeff_succ_LTrans, coeff_succ_LTrans] at h
      have hfun : (fun η : Config KA KB => PowerSeries.coeff k (Q η))
          = fun η : Config KA KB => PowerSeries.coeff k (Q' η) := by
        funext η
        have hk := ih η
        linear_combination hk
      rw [hfun] at h
      rw [L1_sub (fun η => PowerSeries.coeff (k + 1) (Q η))
        (fun η => PowerSeries.coeff (k + 1) (Q' η)) ξ]
      linear_combination h
  funext ξ
  refine PowerSeries.ext fun k => ?_
  linear_combination key k ξ

end Rhone.Probability.RecombinationExpansion
