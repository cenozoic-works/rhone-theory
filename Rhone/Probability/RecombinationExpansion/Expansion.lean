/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.RecombinationExpansion.OrderMatch
public import Mathlib.RingTheory.PowerSeries.Basic

/-! # Order matching in the `1/ρ` expansion of the sampling probability -/

@[expose] public section

namespace Rhone.Probability.RecombinationExpansion

open LinearAlgebra.Recursion LinearAlgebra.Recursion.Config

section Substitution

variable {KA KB : ℕ} {S : Type*} [CommRing S]
variable {θA θB ρ : S} {πA : Fin KA → S} {πB : Fin KB → S}

theorem Lop_expansion (x : S) (hx : ρ * x = 1) (qk : ℕ → Config KA KB → S) (K : ℕ)
    (ξ : Config KA KB) :
    Analysis.RecombinationExpansion.Lop θA θB ρ πA πB
        (fun η => ∑ k ∈ Finset.range K, x ^ (k + 1) * qk (k + 1) η) ξ
      = (∑ k ∈ Finset.range K, x ^ (k + 1) * Analysis.RecombinationExpansion.L0 θA θB πA πB
          (qk (k + 1)) ξ)
        + ∑ k ∈ Finset.range K, x ^ k * Analysis.RecombinationExpansion.L1 (qk (k + 1)) ξ := by
  have hL0 : Analysis.RecombinationExpansion.L0 θA θB πA πB
      (fun η => ∑ k ∈ Finset.range K, x ^ (k + 1) * qk (k + 1) η) ξ
      = ∑ k ∈ Finset.range K, x ^ (k + 1) * Analysis.RecombinationExpansion.L0 θA θB πA πB
          (qk (k + 1)) ξ := by
    rw [Analysis.RecombinationExpansion.L0, Analysis.RecombinationExpansion.Lop_sum_range
        (fun k η => x ^ (k + 1) * qk (k + 1) η)]
    exact Finset.sum_congr rfl fun k _ => Analysis.RecombinationExpansion.Lop_smul _ _ ξ
  have hL1 : Analysis.RecombinationExpansion.L1
      (fun η => ∑ k ∈ Finset.range K, x ^ (k + 1) * qk (k + 1) η) ξ
      = ∑ k ∈ Finset.range K, x ^ (k + 1) * Analysis.RecombinationExpansion.L1 (qk (k + 1)) ξ := by
    rw [Analysis.RecombinationExpansion.L1_sum_range (fun k η => x ^ (k + 1) * qk (k + 1) η)]
    exact Finset.sum_congr rfl fun k _ => Analysis.RecombinationExpansion.L1_smul _ _ ξ
  rw [Analysis.RecombinationExpansion.Lop_split, hL0, hL1, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  have hstep : ρ * (x ^ (k + 1) * Analysis.RecombinationExpansion.L1 (qk (k + 1)) ξ)
      = (ρ * x) * (x ^ k * Analysis.RecombinationExpansion.L1 (qk (k + 1)) ξ) := by ring
  rw [hstep, hx, one_mul]

end Substitution

section Coeff

open PowerSeries

variable {KA KB : ℕ} {F : Type*} [CommRing F]
variable {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}

theorem diag_C (ξ : Config KA KB) :
    diag (C θA) (C θB) (C ρ) ξ = C (diag θA θB ρ ξ) := by
  simp only [diag, map_add, map_mul, map_natCast]

theorem coeff_rhs (k : ℕ) (Q : Config KA KB → PowerSeries F) (ξ : Config KA KB) :
    PowerSeries.coeff k
        (rhs (C θA) (C θB) (C ρ) (fun i => C (πA i)) (fun j => C (πB j)) Q ξ)
      = rhs θA θB ρ πA πB (fun η => PowerSeries.coeff k (Q η)) ξ := by
  simp only [rhs, map_add, map_sum, ← map_natCast (PowerSeries.C (R := F)),
    PowerSeries.coeff_C_mul]

theorem coeff_Lop (k : ℕ) (Q : Config KA KB → PowerSeries F) (ξ : Config KA KB) :
    PowerSeries.coeff k
        (Analysis.RecombinationExpansion.Lop (C θA) (C θB) (C ρ) (fun i => C (πA i))
            (fun j => C (πB j)) Q ξ)
      = Analysis.RecombinationExpansion.Lop θA θB ρ πA πB (fun η => PowerSeries.coeff k (Q η)) ξ :=
          by
  rw [Analysis.RecombinationExpansion.Lop, Analysis.RecombinationExpansion.Lop, map_sub, diag_C,
      PowerSeries.coeff_C_mul, coeff_rhs]

theorem coeff_L0 (k : ℕ) (Q : Config KA KB → PowerSeries F) (ξ : Config KA KB) :
    PowerSeries.coeff k
        (Analysis.RecombinationExpansion.L0 (C θA) (C θB) (fun i => C (πA i)) (fun j => C (πB j)) Q
            ξ)
      = Analysis.RecombinationExpansion.L0 θA θB πA πB (fun η => PowerSeries.coeff k (Q η)) ξ := by
  rw [Analysis.RecombinationExpansion.L0, Analysis.RecombinationExpansion.L0, show
      (0 : PowerSeries F) = C (0 : F) from (map_zero _).symm, coeff_Lop]

theorem coeff_L1 (k : ℕ) (Q : Config KA KB → PowerSeries F) (ξ : Config KA KB) :
    PowerSeries.coeff k (Analysis.RecombinationExpansion.L1 Q ξ) =
        Analysis.RecombinationExpansion.L1 (fun η => PowerSeries.coeff k (Q η)) ξ := by
  simp only [Analysis.RecombinationExpansion.L1, map_sub, map_sum, ← map_natCast
      (PowerSeries.C (R := F)),
    PowerSeries.coeff_C_mul]

end Coeff

section Matching

open PowerSeries

variable {KA KB : ℕ} {F : Type*} [CommRing F]
variable {θA θB : F} {πA : Fin KA → F} {πB : Fin KB → F}

noncomputable def gen (qk : ℕ → Config KA KB → F) (ξ : Config KA KB) : PowerSeries F :=
  PowerSeries.mk fun k => qk (k + 1) ξ

@[simp]
theorem coeff_gen (qk : ℕ → Config KA KB → F) (ξ : Config KA KB) (k : ℕ) :
    PowerSeries.coeff k (gen qk ξ) = qk (k + 1) ξ := by
  rw [gen, PowerSeries.coeff_mk]

theorem order_matching (qk : ℕ → Config KA KB → F) (src : Config KA KB → F)
    (ξ : Config KA KB)
    (h : PowerSeries.X
          * Analysis.RecombinationExpansion.L0 (C θA) (C θB) (fun i => C (πA i)) (fun j => C (πB j))
              (gen qk) ξ
        + Analysis.RecombinationExpansion.L1 (gen qk) ξ = C (src ξ)) :
    Analysis.RecombinationExpansion.L1 (qk 1) ξ = src ξ ∧
      ∀ m : ℕ, Analysis.RecombinationExpansion.L1 (qk (m + 2)) ξ =
          -Analysis.RecombinationExpansion.L0 θA θB πA πB (qk (m + 1)) ξ := by
  constructor
  · have h0 := congrArg (PowerSeries.coeff 0) h
    rw [map_add, PowerSeries.coeff_zero_X_mul, coeff_L1, PowerSeries.coeff_zero_C,
      zero_add] at h0
    simpa using h0
  · intro m
    have hm := congrArg (PowerSeries.coeff (m + 1)) h
    rw [map_add, PowerSeries.coeff_succ_X_mul, coeff_L0, coeff_L1,
      PowerSeries.coeff_C] at hm
    simp only [coeff_gen] at hm
    rw [ite_eq_right (by omega)] at hm
    have e : m + 1 + 1 = m + 2 := by omega
    rw [e] at hm
    linear_combination hm

end Matching

end Rhone.Probability.RecombinationExpansion
