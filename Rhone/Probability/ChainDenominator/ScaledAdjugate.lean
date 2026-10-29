/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.ChainDenominator.GenericDegree
public import Rhone.Analysis.DenominatorEquation.TopForm
public import Rhone.Probability.DiagonalChain.TopFormRec

/-! # Scaled principal minors and adjugate entries for the diagonal chain -/

@[expose] public section

noncomputable section

namespace Rhone.Probability.ChainDenominator

open Polynomial DiagonalChain Analysis.DenominatorEquation LinearAlgebra.DenominatorEquation
    Analysis.RecombinationExpansion LinearAlgebra.RecombinationExpansion LinearAlgebra.Tridiag

def lead (A B : ℤ) (k t : ℕ) : ℤ[X] :=
  Delta ℤ[X] k k (C A * X) 0 (C B * X) t

def trail (A B : ℤ) (k t : ℕ) : ℤ[X] :=
  DeltaP ℤ[X] k k (C A * X) 0 (C B * X) t

theorem lead_natDegree_le (A B : ℤ) (k t : ℕ) : (lead A B k t).natDegree ≤ t := by
  simpa [lead] using Delta_scaled_natDegree_le k k A 0 B t

theorem lead_coeff (A B : ℤ) (k t : ℕ) :
    (lead A B k t).coeff t = ∏ x ∈ Finset.range t, Lam A B k x := by
  simpa [lead, Lam, mul_comm] using Delta_scaled_coeff_top k k A 0 B t

theorem trail_natDegree_le (A B : ℤ) (k t : ℕ) (ht : t ≤ k + 1) :
    (trail A B k t).natDegree ≤ k + 1 - t := by
  simpa [trail] using DeltaP_scaled_natDegree_le k k A 0 B (by simpa using ht)

theorem trail_coeff (A B : ℤ) (k t : ℕ) (ht : t ≤ k + 1) :
    (trail A B k t).coeff (k + 1 - t) =
      ∏ x ∈ Finset.Ico t (k + 1), Lam A B k x := by
  rw [Finset.prod_Ico_eq_prod_range]
  have h := DeltaP_scaled_coeff_top k k A 0 B (by simpa using ht)
  simp only [min_self, map_zero, zero_mul, add_zero] at h
  rw [trail, h]
  apply Finset.prod_congr rfl
  intro x _
  simp only [Lam, Nat.cast_add]
  ring

def upperWeight (k t u : ℕ) : ℤ :=
  2 ^ (u - t) * ∏ s ∈ Finset.Ico t u, (((k - s) * (k - s) : ℕ) : ℤ)

theorem adj_scaled_upper (A B : ℤ) (k t u : ℕ) (h : t ≤ u) :
    adjD k (C A * X) (C B * X) t u =
      C (upperWeight k t u) * lead A B k t * trail A B k (u + 1) := by
  rw [adjD, usmaniEntry_T_of_le k k (C A * X) 0 (C B * X) h]
  simp only [upperWeight, map_mul, map_pow, map_ofNat, map_prod, map_natCast]
  rfl

theorem adj_scaled_upper_degree (A B : ℤ) (k t u : ℕ) (h : t ≤ u) (hu : u ≤ k) :
    (adjD k (C A * X) (C B * X) t u).natDegree ≤ t + (k - u) := by
  rw [adj_scaled_upper A B k t u h]
  have hl := natDegree_mul_le (p := C (upperWeight k t u)) (q := lead A B k t)
  have hr := trail_natDegree_le A B k (u + 1) (by omega)
  simp only [natDegree_C, Nat.zero_add] at hl
  have hd := natDegree_mul_le (p := C (upperWeight k t u) * lead A B k t)
    (q := trail A B k (u + 1))
  have hh := lead_natDegree_le A B k t
  omega

theorem adj_scaled_upper_coeff (A B : ℤ) (k t u : ℕ) (h : t ≤ u) (hu : u ≤ k) :
    (adjD k (C A * X) (C B * X) t u).coeff (t + (k - u)) =
      upperWeight k t u * (∏ x ∈ Finset.range t, Lam A B k x) *
        (∏ x ∈ Finset.Ico (u + 1) (k + 1), Lam A B k x) := by
  rw [adj_scaled_upper A B k t u h, mul_assoc, coeff_C_mul]
  have hr : (trail A B k (u + 1)).natDegree ≤ k - u := by
    simpa using trail_natDegree_le A B k (u + 1) (by omega)
  rw [coeff_mul_add_eq_of_natDegree_le (lead_natDegree_le A B k t) hr, lead_coeff]
  have hc := trail_coeff A B k (u + 1) (by omega)
  simp only [Nat.add_sub_add_right] at hc
  rw [hc, mul_assoc]

theorem adj_scaled_lower (A B : ℤ) (k t u : ℕ) (h : u ≤ t) :
    adjD k (C A * X) (C B * X) t u =
      (C B * X) ^ (t - u) * C (∏ s ∈ Finset.Ico u t, ((s : ℤ) + 1)) *
        lead A B k u * trail A B k (t + 1) := by
  rw [adjD, usmaniEntry_T_of_ge k k (C A * X) 0 (C B * X) h]
  simp only [map_prod, map_add, map_natCast, map_one]
  rfl

theorem adj_scaled_lower_degree (A B : ℤ) (k t u : ℕ) (h : u ≤ t) (ht : t ≤ k) :
    (adjD k (C A * X) (C B * X) t u).natDegree ≤ k := by
  rw [adj_scaled_lower A B k t u h]
  have hp : ((C B * X) ^ (t - u) : ℤ[X]).natDegree ≤ t - u := by
    calc
      _ ≤ (C B * X : ℤ[X]).natDegree * (t - u) := by
        rw [Nat.mul_comm]
        exact natDegree_pow_le
      _ ≤ 1 * (t - u) := Nat.mul_le_mul_right _ (by
        simpa using natDegree_mul_le (p := C B) (q := (X : ℤ[X])))
      _ = t - u := Nat.one_mul _
  have h1 := natDegree_mul_le (p := (C B * X : ℤ[X]) ^ (t - u))
    (q := C (∏ s ∈ Finset.Ico u t, ((s : ℤ) + 1)))
  simp only [natDegree_C, Nat.add_zero] at h1
  have h2 := natDegree_mul_le
    (p := (C B * X) ^ (t - u) * C (∏ s ∈ Finset.Ico u t, ((s : ℤ) + 1)))
    (q := lead A B k u)
  have h3 := natDegree_mul_le
    (p := (C B * X) ^ (t - u) * C (∏ s ∈ Finset.Ico u t, ((s : ℤ) + 1)) * lead A B k u)
    (q := trail A B k (t + 1))
  have hl := lead_natDegree_le A B k u
  have hr := trail_natDegree_le A B k (t + 1) (by omega)
  omega

theorem upperWeight_eq (k t u : ℕ) (hu : u ≤ k) :
    upperWeight k t u =
      2 ^ (u - t) * ∏ s ∈ Finset.Ico t u, ((k : ℤ) - (s : ℤ)) ^ 2 := by
  unfold upperWeight
  congr 1
  apply Finset.prod_congr rfl
  intro s hs
  have hsk : s ≤ k := by rw [Finset.mem_Ico] at hs; omega
  rw [Nat.cast_mul, Nat.cast_sub hsk]
  ring

end Rhone.Probability.ChainDenominator
