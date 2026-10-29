/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.RecombinationExpansion.Residual

/-! # Order matching for the linear term: `L₁ q₁ = 2 q₁` by block counts -/

@[expose] public section

namespace Rhone.Probability.RecombinationExpansion

open LinearAlgebra.Recursion LinearAlgebra.Recursion.Config

variable {KA KB : ℕ} {F : Type*} [Field F]
variable {θA θB : F} {πA : Fin KA → F} {πB : Fin KB → F}

theorem count_identity (N M : ℕ) :
    (N + M) * (N * (N - 1))
      = N * ((N - 1) * (N - 1 - 1)) + M * (N * (N - 1)) + 2 * (N * (N - 1)) := by
  match N with
  | 0 => simp
  | 1 => simp
  | (k + 2) =>
    have e1 : k + 2 - 1 = k + 1 := by omega
    have e2 : k + 1 - 1 = k := by omega
    rw [e1, e2]
    ring

theorem L1_sum {ι : Type*} [Fintype ι] (f : ι → Config KA KB → F) (ξ : Config KA KB) :
    Analysis.RecombinationExpansion.L1 (fun η => ∑ k, f k η) ξ = ∑ k,
        Analysis.RecombinationExpansion.L1 (f k) ξ := by
  simp only [Analysis.RecombinationExpansion.L1, Finset.mul_sum, Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_congr rfl fun i₀ _ => Finset.sum_comm]
  exact Finset.sum_comm

theorem count_split (ξ : Config KA KB) (N : Config KA KB → ℕ)
    (D E : Fin KA → Fin KB → ℕ)
    (hDE : ∀ i₀ j₀, D i₀ j₀ + E i₀ j₀ = 1)
    (hsp : ∀ i₀ j₀, ξ.c i₀ j₀ ≠ 0 → N (ξ.split i₀ j₀) + D i₀ j₀ = N ξ)
    (hsum : (∑ i₀, ∑ j₀, ξ.c i₀ j₀ * D i₀ j₀) = N ξ) (v : F) :
    ((ξ.t : ℕ) : F) * (((N ξ * (N ξ - 1) : ℕ) : F) * v)
      - (∑ i₀, ∑ j₀, ((ξ.c i₀ j₀ : ℕ) : F)
          * (((N (ξ.split i₀ j₀) * (N (ξ.split i₀ j₀) - 1) : ℕ) : F) * v))
      = 2 * (((N ξ * (N ξ - 1) : ℕ) : F) * v) := by
  have hstep : ∀ i₀ : Fin KA, ∀ j₀ : Fin KB, ((ξ.c i₀ j₀ : ℕ) : F)
        * (((N (ξ.split i₀ j₀) * (N (ξ.split i₀ j₀) - 1) : ℕ) : F) * v)
      = ((ξ.c i₀ j₀ * D i₀ j₀ : ℕ) : F)
          * ((((N ξ - 1) * (N ξ - 1 - 1) : ℕ) : F) * v)
        + ((ξ.c i₀ j₀ * E i₀ j₀ : ℕ) : F) * (((N ξ * (N ξ - 1) : ℕ) : F) * v) := by
    intro i₀ j₀
    by_cases hc : ξ.c i₀ j₀ = 0
    · rw [hc]; simp
    · have h := hsp i₀ j₀ hc
      have hd := hDE i₀ j₀
      rcases Nat.eq_zero_or_pos (D i₀ j₀) with hD0 | hD1
      · have hE1 : E i₀ j₀ = 1 := by omega
        have hN : N (ξ.split i₀ j₀) = N ξ := by omega
        rw [hN, hD0, hE1]
        push_cast
        ring
      · have hD1' : D i₀ j₀ = 1 := by omega
        have hE0 : E i₀ j₀ = 0 := by omega
        have hN : N (ξ.split i₀ j₀) = N ξ - 1 := by omega
        rw [hN, hD1', hE0]
        push_cast
        ring
  have htot : (∑ i₀, ∑ j₀, ξ.c i₀ j₀ * D i₀ j₀) + (∑ i₀, ∑ j₀, ξ.c i₀ j₀ * E i₀ j₀) = ξ.t := by
    rw [← Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl fun i₀ _ => (Finset.sum_add_distrib).symm]
    rw [Finset.sum_congr rfl fun i₀ _ => Finset.sum_congr rfl fun j₀ _ => by
      rw [← Nat.mul_add, hDE i₀ j₀, mul_one]]
    exact sum_c ξ
  have hle : N ξ ≤ ξ.t := by omega
  have hEsum : (∑ i₀, ∑ j₀, ξ.c i₀ j₀ * E i₀ j₀) = ξ.t - N ξ := by omega
  have hcD : (∑ i₀, ∑ j₀, ((ξ.c i₀ j₀ * D i₀ j₀ : ℕ) : F)) = ((N ξ : ℕ) : F) := by
    simp only [← Nat.cast_sum]
    rw [hsum]
  have hcE : (∑ i₀, ∑ j₀, ((ξ.c i₀ j₀ * E i₀ j₀ : ℕ) : F)) = ((ξ.t - N ξ : ℕ) : F) := by
    simp only [← Nat.cast_sum]
    rw [hEsum]
  have hnat : ξ.t * (N ξ * (N ξ - 1))
      = N ξ * ((N ξ - 1) * (N ξ - 1 - 1)) + (ξ.t - N ξ) * (N ξ * (N ξ - 1))
        + 2 * (N ξ * (N ξ - 1)) := by
    have h := count_identity (N ξ) (ξ.t - N ξ)
    rwa [show N ξ + (ξ.t - N ξ) = ξ.t from by omega] at h
  have hcast := congrArg (fun x : ℕ => ((x : ℕ) : F)) hnat
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hcast
  rw [Finset.sum_congr rfl fun i₀ _ => Finset.sum_congr rfl fun j₀ _ => hstep i₀ j₀]
  rw [Finset.sum_congr rfl fun i₀ _ => Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [← Finset.sum_mul]
  rw [hcD, hcE]
  push_cast at hcast ⊢
  linear_combination v * hcast

def blkT (θA θB : F) (πA : Fin KA → F) (πB : Fin KB → F) (η : Config KA KB) : F :=
  ((η.t * (η.t - 1) : ℕ) : F) * (qOne θA πA η.mA * qOne θB πB η.mB)

def blkR (θA θB : F) (πA : Fin KA → F) (πB : Fin KB → F) (η : Config KA KB) (i : Fin KA) : F :=
  ((η.cRow i * (η.cRow i - 1) : ℕ) : F)
    * (qOne θB πB η.mB * qOne θA πA (decf η.mA i))

def blkC (θA θB : F) (πA : Fin KA → F) (πB : Fin KB → F) (η : Config KA KB) (j : Fin KB) : F :=
  ((η.cCol j * (η.cCol j - 1) : ℕ) : F)
    * (qOne θA πA η.mA * qOne θB πB (decf η.mB j))

def blkE (θA θB : F) (πA : Fin KA → F) (πB : Fin KB → F) (η : Config KA KB) (i : Fin KA)
    (j : Fin KB) : F :=
  ((η.c i j * (η.c i j - 1) : ℕ) : F)
    * (qOne θA πA (decf η.mA i) * qOne θB πB (decf η.mB j))

theorem twoQ1_eq_blocks (ξ : Config KA KB) :
    twoQ1 θA θB πA πB ξ
      = blkT θA θB πA πB ξ - (∑ i, blkR θA θB πA πB ξ i) - (∑ j, blkC θA θB πA πB ξ j)
        + ∑ i, ∑ j, blkE θA θB πA πB ξ i j := by
  have h1 : qOne θB πB ξ.mB
        * ∑ i, ((ξ.cRow i * (ξ.cRow i - 1) : ℕ) : F) * qOne θA πA (decf ξ.mA i)
      = ∑ i, blkR θA θB πA πB ξ i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [blkR]; ring
  have h2 : qOne θA πA ξ.mA
        * ∑ j, ((ξ.cCol j * (ξ.cCol j - 1) : ℕ) : F) * qOne θB πB (decf ξ.mB j)
      = ∑ j, blkC θA θB πA πB ξ j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [blkC]; ring
  have h3 : (∑ i, ∑ j, ((ξ.c i j * (ξ.c i j - 1) : ℕ) : F)
        * (qOne θA πA (decf ξ.mA i) * qOne θB πB (decf ξ.mB j)))
      = ∑ i, ∑ j, blkE θA θB πA πB ξ i j :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => rfl
  rw [twoQ1, blkT, h1, h2, h3]

theorem L1_blkT (ξ : Config KA KB) :
    Analysis.RecombinationExpansion.L1 (fun η => blkT θA θB πA πB η) ξ = 2 * blkT θA θB πA πB ξ :=
        by
  have hterm : ∀ i₀ : Fin KA, ∀ j₀ : Fin KB,
      ((ξ.c i₀ j₀ : ℕ) : F) * blkT θA θB πA πB (ξ.split i₀ j₀)
        = ((ξ.c i₀ j₀ : ℕ) : F)
          * (((((ξ.split i₀ j₀).t) * (((ξ.split i₀ j₀).t) - 1) : ℕ) : F)
              * (qOne θA πA ξ.mA * qOne θB πB ξ.mB)) := by
    intro i₀ j₀
    by_cases hc : ξ.c i₀ j₀ = 0
    · rw [hc]; simp
    · rw [blkT, ξ.mA_split hc, ξ.mB_split hc]
  rw [Analysis.RecombinationExpansion.L1, Finset.sum_congr rfl fun i₀ _ => Finset.sum_congr rfl fun
      j₀ _ => hterm i₀ j₀]
  simp only [blkT]
  refine count_split ξ (fun η => η.t) (fun _ _ => 1) (fun _ _ => 0) (fun _ _ => rfl)
    (fun i₀ j₀ hc => ξ.t_split i₀ j₀ hc) ?_ _
  simp only [mul_one]
  exact sum_c ξ

theorem L1_blkR (ξ : Config KA KB) (i : Fin KA) :
    Analysis.RecombinationExpansion.L1 (fun η => blkR θA θB πA πB η i) ξ = 2 * blkR θA θB πA πB ξ
        i := by
  have hterm : ∀ i₀ : Fin KA, ∀ j₀ : Fin KB,
      ((ξ.c i₀ j₀ : ℕ) : F) * blkR θA θB πA πB (ξ.split i₀ j₀) i
        = ((ξ.c i₀ j₀ : ℕ) : F)
          * (((((ξ.split i₀ j₀).cRow i) * (((ξ.split i₀ j₀).cRow i) - 1) : ℕ) : F)
              * (qOne θB πB ξ.mB * qOne θA πA (decf ξ.mA i))) := by
    intro i₀ j₀
    by_cases hc : ξ.c i₀ j₀ = 0
    · rw [hc]; simp
    · rw [blkR, ξ.mA_split hc, ξ.mB_split hc]
  rw [Analysis.RecombinationExpansion.L1, Finset.sum_congr rfl fun i₀ _ => Finset.sum_congr rfl fun
      j₀ _ => hterm i₀ j₀]
  simp only [blkR]
  refine count_split ξ (fun η => η.cRow i) (fun i₀ _ => if i₀ = i then 1 else 0)
    (fun i₀ _ => if i₀ = i then 0 else 1) (fun i₀ _ => by split_ifs <;> rfl) ?_ ?_ _
  · intro i₀ j₀ hc
    rw [ξ.cRow_split hc]
    by_cases hi : i₀ = i
    · subst hi
      rw [decf_self, ite_eq_left rfl]
      have := ξ.le_cRow i₀ j₀
      omega
    · rw [decf_of_ne _ (fun h => hi h.symm), ite_eq_right hi]
      omega
  · have hrow : ∀ i₀ : Fin KA, (∑ j₀, ξ.c i₀ j₀ * (if i₀ = i then 1 else 0))
        = if i₀ = i then ξ.cRow i₀ else 0 := by
      intro i₀
      by_cases hi : i₀ = i
      · simp only [ite_eq_left hi, mul_one]
        rfl
      · simp only [ite_eq_right hi, mul_zero, Finset.sum_const_zero]
    rw [Finset.sum_congr rfl fun i₀ _ => hrow i₀,
      Finset.sum_ite_eq' Finset.univ i (fun i₀ => ξ.cRow i₀)]
    simp

theorem L1_blkC (ξ : Config KA KB) (j : Fin KB) :
    Analysis.RecombinationExpansion.L1 (fun η => blkC θA θB πA πB η j) ξ = 2 * blkC θA θB πA πB ξ
        j := by
  have hterm : ∀ i₀ : Fin KA, ∀ j₀ : Fin KB,
      ((ξ.c i₀ j₀ : ℕ) : F) * blkC θA θB πA πB (ξ.split i₀ j₀) j
        = ((ξ.c i₀ j₀ : ℕ) : F)
          * (((((ξ.split i₀ j₀).cCol j) * (((ξ.split i₀ j₀).cCol j) - 1) : ℕ) : F)
              * (qOne θA πA ξ.mA * qOne θB πB (decf ξ.mB j))) := by
    intro i₀ j₀
    by_cases hc : ξ.c i₀ j₀ = 0
    · rw [hc]; simp
    · rw [blkC, ξ.mA_split hc, ξ.mB_split hc]
  rw [Analysis.RecombinationExpansion.L1, Finset.sum_congr rfl fun i₀ _ => Finset.sum_congr rfl fun
      j₀ _ => hterm i₀ j₀]
  simp only [blkC]
  refine count_split ξ (fun η => η.cCol j) (fun _ j₀ => if j₀ = j then 1 else 0)
    (fun _ j₀ => if j₀ = j then 0 else 1) (fun _ j₀ => by split_ifs <;> rfl) ?_ ?_ _
  · intro i₀ j₀ hc
    rw [ξ.cCol_split hc]
    by_cases hj : j₀ = j
    · subst hj
      rw [decf_self, ite_eq_left rfl]
      have := ξ.le_cCol i₀ j₀
      omega
    · rw [decf_of_ne _ (fun h => hj h.symm), ite_eq_right hj]
      omega
  · rw [Finset.sum_comm]
    have hcol : ∀ j₀ : Fin KB, (∑ i₀, ξ.c i₀ j₀ * (if j₀ = j then 1 else 0))
        = if j₀ = j then ξ.cCol j₀ else 0 := by
      intro j₀
      by_cases hj : j₀ = j
      · simp only [ite_eq_left hj, mul_one]
        rfl
      · simp only [ite_eq_right hj, mul_zero, Finset.sum_const_zero]
    rw [Finset.sum_congr rfl fun j₀ _ => hcol j₀,
      Finset.sum_ite_eq' Finset.univ j (fun j₀ => ξ.cCol j₀)]
    simp

theorem L1_blkE (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) :
    Analysis.RecombinationExpansion.L1 (fun η => blkE θA θB πA πB η i j) ξ = 2 * blkE θA θB πA πB ξ
        i j := by
  have hterm : ∀ i₀ : Fin KA, ∀ j₀ : Fin KB,
      ((ξ.c i₀ j₀ : ℕ) : F) * blkE θA θB πA πB (ξ.split i₀ j₀) i j
        = ((ξ.c i₀ j₀ : ℕ) : F)
          * (((((ξ.split i₀ j₀).c i j) * (((ξ.split i₀ j₀).c i j) - 1) : ℕ) : F)
              * (qOne θA πA (decf ξ.mA i) * qOne θB πB (decf ξ.mB j))) := by
    intro i₀ j₀
    by_cases hc : ξ.c i₀ j₀ = 0
    · rw [hc]; simp
    · rw [blkE, ξ.mA_split hc, ξ.mB_split hc]
  rw [Analysis.RecombinationExpansion.L1, Finset.sum_congr rfl fun i₀ _ => Finset.sum_congr rfl fun
      j₀ _ => hterm i₀ j₀]
  simp only [blkE]
  refine count_split ξ (fun η => η.c i j)
    (fun i₀ j₀ => if i₀ = i then (if j₀ = j then 1 else 0) else 0)
    (fun i₀ j₀ => if i₀ = i then (if j₀ = j then 0 else 1) else 1)
    (fun i₀ j₀ => by split_ifs <;> rfl) ?_ ?_ _
  · intro i₀ j₀ hc
    rw [ξ.c_split i₀ j₀]
    by_cases hi : i₀ = i
    · subst hi
      rw [decC_self, ite_eq_left rfl]
      by_cases hj : j₀ = j
      · subst hj
        rw [decf_self, ite_eq_left rfl]
        omega
      · rw [decf_of_ne _ (fun h => hj h.symm), ite_eq_right hj]
        omega
    · rw [decC_of_ne ξ.c j₀ (fun h => hi h.symm) j, ite_eq_right hi]
      omega
  · have hin : ∀ i₀ : Fin KA,
        (∑ j₀, ξ.c i₀ j₀ * (if i₀ = i then (if j₀ = j then 1 else 0) else 0))
          = if i₀ = i then ξ.c i₀ j else 0 := by
      intro i₀
      by_cases hi : i₀ = i
      · simp only [ite_eq_left hi]
        have hstep : ∀ j₀ : Fin KB, ξ.c i₀ j₀ * (if j₀ = j then 1 else 0)
            = if j₀ = j then ξ.c i₀ j₀ else 0 := by
          intro j₀
          split_ifs <;> simp
        rw [Finset.sum_congr rfl fun j₀ _ => hstep j₀,
          Finset.sum_ite_eq' Finset.univ j (fun j₀ => ξ.c i₀ j₀)]
        simp
      · simp only [ite_eq_right hi, mul_zero, Finset.sum_const_zero]
    rw [Finset.sum_congr rfl fun i₀ _ => hin i₀,
      Finset.sum_ite_eq' Finset.univ i (fun i₀ => ξ.c i₀ j)]
    simp

theorem L1_twoQ1 (ξ : Config KA KB) :
    Analysis.RecombinationExpansion.L1 (twoQ1 θA θB πA πB) ξ = 2 * twoQ1 θA θB πA πB ξ := by
  have hfun : (twoQ1 θA θB πA πB : Config KA KB → F)
      = fun η => blkT θA θB πA πB η - (∑ i, blkR θA θB πA πB η i)
        - (∑ j, blkC θA θB πA πB η j) + ∑ i, ∑ j, blkE θA θB πA πB η i j :=
    funext fun η => twoQ1_eq_blocks η
  rw [hfun]
  have hlin : ∀ f1 f2 f3 f4 : Config KA KB → F,
      Analysis.RecombinationExpansion.L1 (fun η => f1 η - f2 η - f3 η + f4 η) ξ
        = Analysis.RecombinationExpansion.L1 f1 ξ - Analysis.RecombinationExpansion.L1 f2 ξ -
            Analysis.RecombinationExpansion.L1 f3 ξ + Analysis.RecombinationExpansion.L1 f4 ξ := by
    intro f1 f2 f3 f4
    simp only [Analysis.RecombinationExpansion.L1, mul_sub, mul_add, Finset.sum_sub_distrib,
        Finset.sum_add_distrib]
    ring
  rw [hlin, L1_blkT, L1_sum (fun i η => blkR θA θB πA πB η i),
    L1_sum (fun j η => blkC θA θB πA πB η j),
    L1_sum (fun i η => ∑ j, blkE θA θB πA πB η i j)]
  rw [Finset.sum_congr rfl fun i _ => L1_sum (fun j η => blkE θA θB πA πB η i j) ξ]
  rw [Finset.sum_congr rfl fun i _ => L1_blkR ξ i,
    Finset.sum_congr rfl fun j _ => L1_blkC ξ j,
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => L1_blkE ξ i j]
  change _ = 2 * (blkT θA θB πA πB ξ - (∑ i, blkR θA θB πA πB ξ i)
    - (∑ j, blkC θA θB πA πB ξ j) + ∑ i, ∑ j, blkE θA θB πA πB ξ i j)
  simp only [← Finset.mul_sum]
  ring

end Rhone.Probability.RecombinationExpansion
