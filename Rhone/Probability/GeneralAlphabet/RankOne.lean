/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.GeneralAlphabet.Basic

/-! # The rank-one theorem at a general alphabet -/

@[expose] public section

universe u v

namespace Rhone.Probability.GeneralAlphabet

open Finset LinearAlgebra.Recursion Denominator LinearAlgebra.Multilinear Multilinear
open SlotDeletion

variable {KA KB : ℕ}

theorem two_mul_mul_le (a b t : ℕ) : 2 * (a * b) ≤ (a + b + t) * (a + b + t - 1) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  have h : a' + 1 + (b' + 1) + t - 1 = a' + b' + t + 1 := by omega
  rw [h]
  nlinarith

section Defn

variable {F : Type*} [CommRing F] {SA : Type u} [Fintype SA] [DecidableEq SA]

def defc (q : Config KA KB → F) (πA : Fin KA → F) (u₁ : SA) (x y x' y' : Fin KA → F)
    {SB : Type v} [Fintype SB] [DecidableEq SB]
    (M : Finset (SA × SB)) (w : SB → Fin KB → F) : F :=
  mean πA (x' * y') * Q q M (sPair u₁ x y) w - mean πA (x * y) * Q q M (sPair u₁ x' y') w

end Defn

section Rec

variable {SA : Type u} {SB : Type v}
variable [Fintype SA] [DecidableEq SA] [Fintype SB] [DecidableEq SB]
variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}
variable (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
variable {q : Config KA KB → F} (hq : IsSolution θA θB ρ πA πB q)
variable {u₁ : SA} {x y x' y' : Fin KA → F}
include hθA hθB hρ hq

theorem defc_of_B_one (hπB : ∑ j, πB j = 1)
    (hzero : ∀ {SB' : Type v} [Fintype SB'] [DecidableEq SB'] (M' : Finset (SA × SB'))
      (w' : SB' → Fin KB → F), Fintype.card SB' < Fintype.card SB → IsMatching M' →
      defc q πA u₁ x y x' y' M' w' = 0)
    {M : Finset (SA × SB)} (hM : IsMatching M) (v : SB) (w : SB → Fin KB → F) (hw : w v = 1) :
    defc q πA u₁ x y x' y' M w = 0 := by
  have hlt : Fintype.card {t : SB // t ≠ v} < Fintype.card SB := by
    have h := card_sub_ne (SA := SB) v
    omega
  by_cases hfree : v ∈ freeB M
  · have h1 := Q_restrB hθA hθB hρ hq hπB hfree (sPair u₁ x y) w hw
    have h2 := Q_restrB hθA hθB hρ hq hπB hfree (sPair u₁ x' y') w hw
    have h3 := hzero (restrB v M) (fun t => w (t : SB)) hlt (isMatching_restrB hM)
    simp only [defc] at h3 ⊢
    rw [h1, h2]
    exact h3
  · obtain ⟨u, hu⟩ := mem_domB.mp (by simpa [freeB, Finset.mem_sdiff] using hfree)
    have hfree' : v ∈ freeB (M.erase (u, v)) := snd_freeB_erase hM hu
    have e1 := Q_eraseB hθA hθB hρ hq hπB hM hu (sPair u₁ x y) w hw
    have e2 := Q_eraseB hθA hθB hρ hq hπB hM hu (sPair u₁ x' y') w hw
    have h1 := Q_restrB hθA hθB hρ hq hπB hfree' (sPair u₁ x y) w hw
    have h2 := Q_restrB hθA hθB hρ hq hπB hfree' (sPair u₁ x' y') w hw
    have h3 := hzero (restrB v (M.erase (u, v))) (fun t => w (t : SB)) hlt
      (isMatching_restrB (isMatching_erase hM _))
    simp only [defc] at h3 ⊢
    rw [e1, e2, h1, h2]
    exact h3

theorem defc_rec (hπA : ∑ i, πA i = 1) (hπB : ∑ j, πB j = 1)
    (hcard : Fintype.card SA = 2) {u₂ : SA} (hne : u₁ ≠ u₂)
    (hx : mean πA x = 0) (hy : mean πA y = 0) (hx' : mean πA x' = 0) (hy' : mean πA y' = 0)
    (hzero : ∀ {SB' : Type v} [Fintype SB'] [DecidableEq SB'] (M' : Finset (SA × SB'))
      (w' : SB' → Fin KB → F), Fintype.card SB' < Fintype.card SB → IsMatching M' →
      defc q πA u₁ x y x' y' M' w' = 0)
    {M : Finset (SA × SB)} (hM : IsMatching M) (w : SB → Fin KB → F) :
    dgQ θA θB ρ (Fintype.card SA) (Fintype.card SB) M.card * defc q πA u₁ x y x' y' M w
      = 2 * (∑ k ∈ freeA M, ∑ l ∈ freeB M,
            defc q πA u₁ x y x' y' (insert (k, l) M) w)
        + ρ * (∑ p ∈ M, defc q πA u₁ x y x' y' (M.erase p) w) := by
  have hL := dgQ_mul_Q_eq_rhsQ hθA hθB hρ hq M hπA hπB hM (sPair u₁ x y) w
  have hL' := dgQ_mul_Q_eq_rhsQ hθA hθB hρ hq M hπA hπB hM (sPair u₁ x' y') w
  have key : dgQ θA θB ρ (Fintype.card SA) (Fintype.card SB) M.card
        * defc q πA u₁ x y x' y' M w
      = mean πA (x' * y') * rhsQ θA θB ρ πA πB q M (sPair u₁ x y) w
        - mean πA (x * y) * rhsQ θA θB ρ πA πB q M (sPair u₁ x' y') w := by
    simp only [defc]
    rw [← hL, ← hL']
    ring
  have hA1 : mean πA (x' * y')
        * (∑ k ∈ freeA M, ∑ m ∈ (freeA M).erase k, Q q M (hadA k m (sPair u₁ x y)) w)
      = mean πA (x * y)
        * (∑ k ∈ freeA M, ∑ m ∈ (freeA M).erase k, Q q M (hadA k m (sPair u₁ x' y')) w) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hkm : k ≠ m := Ne.symm (Finset.mem_erase.mp hm).1
    rw [Q_hadA_sPair hθA hθB hρ hq hπA hcard hne hM x y hkm w,
      Q_hadA_sPair hθA hθB hρ hq hπA hcard hne hM x' y' hkm w]
    ring
  have hA2 : mean πA (x' * y')
        * (∑ k ∈ freeA M, ∑ p ∈ M, Q q M (hadA p.1 k (sPair u₁ x y)) w)
      = mean πA (x * y)
        * (∑ k ∈ freeA M, ∑ p ∈ M, Q q M (hadA p.1 k (sPair u₁ x' y')) w) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hkm : p.1 ≠ k := fst_ne_of_mem_freeA hk hp
    rw [Q_hadA_sPair hθA hθB hρ hq hπA hcard hne hM x y hkm w,
      Q_hadA_sPair hθA hθB hρ hq hπA hcard hne hM x' y' hkm w]
    ring
  have hA5 : mean πA (x' * y')
        * (∑ p ∈ M, ∑ p' ∈ M.erase p,
            Q q M (hadA p.1 p'.1 (sPair u₁ x y)) (hadB p.2 p'.2 w))
      = mean πA (x * y)
        * (∑ p ∈ M, ∑ p' ∈ M.erase p,
            Q q M (hadA p.1 p'.1 (sPair u₁ x' y')) (hadB p.2 p'.2 w)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p' hp' => ?_
    have hkm : p.1 ≠ p'.1 := fun hcc =>
      (Finset.mem_erase.mp hp').1 (hM.fst p hp p' (Finset.mem_erase.mp hp').2 hcc).symm
    rw [Q_hadA_sPair hθA hθB hρ hq hπA hcard hne hM x y hkm (hadB p.2 p'.2 w),
      Q_hadA_sPair hθA hθB hρ hq hπA hcard hne hM x' y' hkm (hadB p.2 p'.2 w)]
    ring
  have hA3 : mean πA (x' * y')
        * (∑ l ∈ freeB M, ∑ n ∈ (freeB M).erase l, Q q M (sPair u₁ x y) (hadB l n w))
      = mean πA (x * y)
        * (∑ l ∈ freeB M, ∑ n ∈ (freeB M).erase l, Q q M (sPair u₁ x' y') (hadB l n w)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    have h0 := defc_of_B_one hθA hθB hρ hq hπB hzero hM n (hadB l n w)
      (by rw [hadB, Function.update_self])
    simp only [defc] at h0
    linear_combination h0
  have hA4 : mean πA (x' * y')
        * (∑ l ∈ freeB M, ∑ p ∈ M, Q q M (sPair u₁ x y) (hadB p.2 l w))
      = mean πA (x * y)
        * (∑ l ∈ freeB M, ∑ p ∈ M, Q q M (sPair u₁ x' y') (hadB p.2 l w)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    have h0 := defc_of_B_one hθA hθB hρ hq hπB hzero hM l (hadB p.2 l w)
      (by rw [hadB, Function.update_self])
    simp only [defc] at h0
    linear_combination h0
  have hA7 : mean πA (x' * y')
        * (∑ u : SA, mean πA (sPair u₁ x y u) * Q q M (Function.update (sPair u₁ x y) u 1) w)
      = mean πA (x * y)
        * (∑ u : SA,
            mean πA (sPair u₁ x' y' u) * Q q M (Function.update (sPair u₁ x' y') u 1) w) := by
    have z1 : (∑ u : SA,
        mean πA (sPair u₁ x y u) * Q q M (Function.update (sPair u₁ x y) u 1) w) = 0 :=
      Finset.sum_eq_zero fun u _ => by rw [mean_sPair hx hy u, zero_mul]
    have z2 : (∑ u : SA,
        mean πA (sPair u₁ x' y' u) * Q q M (Function.update (sPair u₁ x' y') u 1) w) = 0 :=
      Finset.sum_eq_zero fun u _ => by rw [mean_sPair hx' hy' u, zero_mul]
    rw [z1, z2, mul_zero, mul_zero]
  have hA8 : mean πA (x' * y')
        * (∑ v : SB, mean πB (w v) * Q q M (sPair u₁ x y) (Function.update w v 1))
      = mean πA (x * y)
        * (∑ v : SB, mean πB (w v) * Q q M (sPair u₁ x' y') (Function.update w v 1)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    have h0 := defc_of_B_one hθA hθB hρ hq hπB hzero hM v (Function.update w v 1)
      (by rw [Function.update_self])
    simp only [defc] at h0
    linear_combination mean πB (w v) * h0
  have h6 : (∑ k ∈ freeA M, ∑ l ∈ freeB M, defc q πA u₁ x y x' y' (insert (k, l) M) w)
      = mean πA (x' * y')
          * (∑ k ∈ freeA M, ∑ l ∈ freeB M, Q q (insert (k, l) M) (sPair u₁ x y) w)
        - mean πA (x * y)
          * (∑ k ∈ freeA M, ∑ l ∈ freeB M, Q q (insert (k, l) M) (sPair u₁ x' y') w) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun l _ => rfl
  have h9 : (∑ p ∈ M, defc q πA u₁ x y x' y' (M.erase p) w)
      = mean πA (x' * y') * (∑ p ∈ M, Q q (M.erase p) (sPair u₁ x y) w)
        - mean πA (x * y) * (∑ p ∈ M, Q q (M.erase p) (sPair u₁ x' y') w) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun p _ => rfl
  rw [key]
  simp only [rhsQ]
  linear_combination hA1 + 2 * hA2 + hA3 + 2 * hA4 + hA5 + θA * hA7 + θB * hA8
    - 2 * h6 - ρ * h9

end Rec

section Dominance

variable {SA : Type u} {SB : Type v}
variable [Fintype SA] [DecidableEq SA] [Fintype SB] [DecidableEq SB]
variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}
variable (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
variable {q : Config KA KB → F} (hq : IsSolution θA θB ρ πA πB q)
variable {u₁ : SA} {x y x' y' : Fin KA → F}
include hθA hθB hρ hq

theorem defc_eq_zero_step (hπA : ∑ i, πA i = 1) (hπB : ∑ j, πB j = 1)
    (hcard : Fintype.card SA = 2) {u₂ : SA} (hne : u₁ ≠ u₂)
    (hx : mean πA x = 0) (hy : mean πA y = 0) (hx' : mean πA x' = 0) (hy' : mean πA y' = 0)
    (hzero : ∀ {SB' : Type v} [Fintype SB'] [DecidableEq SB'] (M' : Finset (SA × SB'))
      (w' : SB' → Fin KB → F), Fintype.card SB' < Fintype.card SB → IsMatching M' →
      defc q πA u₁ x y x' y' M' w' = 0)
    (M : Finset (SA × SB)) (hM : IsMatching M) (w : SB → Fin KB → F) :
    defc q πA u₁ x y x' y' M w = 0 := by
  classical
  obtain ⟨N, hNmem, hNmax⟩ := Finset.exists_max_image
    ((univ : Finset (Finset (SA × SB))).filter fun N => IsMatching N)
    (fun N => |defc q πA u₁ x y x' y' N w|) ⟨M, by simp [hM]⟩
  have hNM : IsMatching N := by simpa using hNmem
  set D : F := |defc q πA u₁ x y x' y' N w| with hD
  have hle : ∀ N' : Finset (SA × SB), IsMatching N' →
      |defc q πA u₁ x y x' y' N' w| ≤ D := fun N' hN' => hNmax N' (by simp [hN'])
  have hDnn : (0 : F) ≤ D := abs_nonneg _
  have hrec := defc_rec hθA hθB hρ hq hπA hπB hcard hne hx hy hx' hy' hzero hNM w
  have hb1 : |∑ k ∈ freeA N, ∑ l ∈ freeB N, defc q πA u₁ x y x' y' (insert (k, l) N) w|
      ≤ (((freeA N).card * (freeB N).card : ℕ) : F) * D := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hin : ∀ k ∈ freeA N,
        |∑ l ∈ freeB N, defc q πA u₁ x y x' y' (insert (k, l) N) w|
          ≤ (((freeB N).card : ℕ) : F) * D := by
      intro k hk
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have hsum : (∑ l ∈ freeB N, |defc q πA u₁ x y x' y' (insert (k, l) N) w|)
          ≤ ∑ _l ∈ freeB N, D :=
        Finset.sum_le_sum fun l hl => hle _ (isMatching_insert hNM hk hl)
      rw [Finset.sum_const, nsmul_eq_mul] at hsum
      exact hsum
    refine le_trans (Finset.sum_le_sum hin) (le_of_eq ?_)
    rw [Finset.sum_const, nsmul_eq_mul]
    push_cast
    ring
  have hb2 : |∑ p ∈ N, defc q πA u₁ x y x' y' (N.erase p) w| ≤ ((N.card : ℕ) : F) * D := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hsum : (∑ p ∈ N, |defc q πA u₁ x y x' y' (N.erase p) w|) ≤ ∑ _p ∈ N, D :=
      Finset.sum_le_sum fun p _ => hle _ (isMatching_erase hNM p)
    rw [Finset.sum_const, nsmul_eq_mul] at hsum
    exact hsum
  have hdgnn : (0 : F) ≤ dgQ θA θB ρ (Fintype.card SA) (Fintype.card SB) N.card := by
    rw [dgQ]
    have h1 : (0 : F) ≤ (((Fintype.card SA + Fintype.card SB - N.card)
        * (Fintype.card SA + Fintype.card SB - N.card - 1) : ℕ) : F) := Nat.cast_nonneg _
    have h2 : (0 : F) ≤ θA * ((Fintype.card SA : ℕ) : F) :=
      mul_nonneg hθA.le (Nat.cast_nonneg _)
    have h3 : (0 : F) ≤ θB * ((Fintype.card SB : ℕ) : F) :=
      mul_nonneg hθB.le (Nat.cast_nonneg _)
    have h4 : (0 : F) ≤ ρ * ((N.card : ℕ) : F) := mul_nonneg hρ (Nat.cast_nonneg _)
    linarith
  have habs : |dgQ θA θB ρ (Fintype.card SA) (Fintype.card SB) N.card
      * defc q πA u₁ x y x' y' N w|
      = dgQ θA θB ρ (Fintype.card SA) (Fintype.card SB) N.card * D := by
    rw [abs_mul, abs_of_nonneg hdgnn]
  have hkey : dgQ θA θB ρ (Fintype.card SA) (Fintype.card SB) N.card * D
      ≤ (2 * (((freeA N).card * (freeB N).card : ℕ) : F) + ρ * ((N.card : ℕ) : F)) * D := by
    calc dgQ θA θB ρ (Fintype.card SA) (Fintype.card SB) N.card * D
        = |dgQ θA θB ρ (Fintype.card SA) (Fintype.card SB) N.card
            * defc q πA u₁ x y x' y' N w| := habs.symm
      _ = |2 * (∑ k ∈ freeA N, ∑ l ∈ freeB N,
              defc q πA u₁ x y x' y' (insert (k, l) N) w)
            + ρ * (∑ p ∈ N, defc q πA u₁ x y x' y' (N.erase p) w)| := by rw [hrec]
      _ ≤ |2 * (∑ k ∈ freeA N, ∑ l ∈ freeB N,
              defc q πA u₁ x y x' y' (insert (k, l) N) w)|
            + |ρ * (∑ p ∈ N, defc q πA u₁ x y x' y' (N.erase p) w)| := abs_add_le _ _
      _ = 2 * |∑ k ∈ freeA N, ∑ l ∈ freeB N,
              defc q πA u₁ x y x' y' (insert (k, l) N) w|
            + ρ * |∑ p ∈ N, defc q πA u₁ x y x' y' (N.erase p) w| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : F) ≤ 2),
            abs_of_nonneg hρ]
      _ ≤ 2 * ((((freeA N).card * (freeB N).card : ℕ) : F) * D)
            + ρ * (((N.card : ℕ) : F) * D) :=
          add_le_add (mul_le_mul_of_nonneg_left hb1 (by norm_num))
            (mul_le_mul_of_nonneg_left hb2 hρ)
      _ = (2 * (((freeA N).card * (freeB N).card : ℕ) : F) + ρ * ((N.card : ℕ) : F)) * D := by
          ring
  have hnat : 2 * ((freeA N).card * (freeB N).card)
      ≤ (Fintype.card SA + Fintype.card SB - N.card)
        * (Fintype.card SA + Fintype.card SB - N.card - 1) := by
    have h1 := card_freeA hNM
    have h2 := card_freeB hNM
    have h3 := two_mul_mul_le (freeA N).card (freeB N).card N.card
    have heq : (freeA N).card + (freeB N).card + N.card
        = Fintype.card SA + Fintype.card SB - N.card := by omega
    rwa [heq] at h3
  have hcast : (2 : F) * (((freeA N).card * (freeB N).card : ℕ) : F)
      ≤ (((Fintype.card SA + Fintype.card SB - N.card)
        * (Fintype.card SA + Fintype.card SB - N.card - 1) : ℕ) : F) := by
    have h := (Nat.cast_le (α := F)).mpr hnat
    push_cast at h ⊢
    linarith
  have hposcoef : 0 < dgQ θA θB ρ (Fintype.card SA) (Fintype.card SB) N.card
      - (2 * (((freeA N).card * (freeB N).card : ℕ) : F) + ρ * ((N.card : ℕ) : F)) := by
    rw [dgQ]
    have hA2 : (0 : F) < θA * ((Fintype.card SA : ℕ) : F) := by
      rw [hcard]
      exact mul_pos hθA (by norm_num)
    have hB0 : (0 : F) ≤ θB * ((Fintype.card SB : ℕ) : F) :=
      mul_nonneg hθB.le (Nat.cast_nonneg _)
    linarith
  have hD0 : D = 0 := by
    by_contra hDne
    have hDpos : 0 < D := lt_of_le_of_ne hDnn (Ne.symm hDne)
    nlinarith [hkey, hposcoef, hDpos]
  have hfin : |defc q πA u₁ x y x' y' M w| ≤ 0 := by rw [← hD0]; exact hle M hM
  exact abs_eq_zero.mp (le_antisymm hfin (abs_nonneg _))

end Dominance

section Main

variable {SA : Type u}
variable [Fintype SA] [DecidableEq SA]
variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}
variable (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
variable {q : Config KA KB → F} (hq : IsSolution θA θB ρ πA πB q)
variable {u₁ : SA} {x y x' y' : Fin KA → F}
include hθA hθB hρ hq

theorem defc_eq_zero_aux (hπA : ∑ i, πA i = 1) (hπB : ∑ j, πB j = 1)
    (hcard : Fintype.card SA = 2) {u₂ : SA} (hne : u₁ ≠ u₂)
    (hx : mean πA x = 0) (hy : mean πA y = 0) (hx' : mean πA x' = 0) (hy' : mean πA y' = 0) :
    ∀ (n : ℕ) {SB : Type v} [Fintype SB] [DecidableEq SB] (M : Finset (SA × SB))
      (w : SB → Fin KB → F), Fintype.card SB ≤ n → IsMatching M →
      defc q πA u₁ x y x' y' M w = 0 := by
  intro n
  induction n with
  | zero =>
      intro SB _ _ M w hn hM
      refine defc_eq_zero_step hθA hθB hρ hq hπA hπB hcard hne hx hy hx' hy' ?_ M hM w
      intro SB' _ _ M' w' hlt _
      omega
  | succ n ih =>
      intro SB _ _ M w hn hM
      refine defc_eq_zero_step hθA hθB hρ hq hπA hπB hcard hne hx hy hx' hy' ?_ M hM w
      intro SB' _ _ M' w' hlt hM'
      exact ih M' w' (by omega) hM'

variable {SB : Type v} [Fintype SB] [DecidableEq SB]

theorem Q_sPair_rank_one (hπA : ∑ i, πA i = 1) (hπB : ∑ j, πB j = 1)
    (hcard : Fintype.card SA = 2) {u₂ : SA} (hne : u₁ ≠ u₂)
    (hx : mean πA x = 0) (hy : mean πA y = 0) (hx' : mean πA x' = 0) (hy' : mean πA y' = 0)
    (M : Finset (SA × SB)) (hM : IsMatching M) (w : SB → Fin KB → F) :
    mean πA (x' * y') * Q q M (sPair u₁ x y) w
      = mean πA (x * y) * Q q M (sPair u₁ x' y') w := by
  have h := defc_eq_zero_aux hθA hθB hρ hq hπA hπB hcard hne hx hy hx' hy'
    (Fintype.card SB) M w le_rfl hM
  simp only [defc] at h
  linarith

end Main

end Rhone.Probability.GeneralAlphabet
