/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.Biallelic.TwoState
public import Rhone.LinearAlgebra.Recursion.OneLocus

/-! # The one-locus general-mutation-matrix recursion, and the biallelic sampling distribution -/

@[expose] public section

namespace Rhone.MarkovChain.Biallelic

open Finset LinearAlgebra.Recursion

variable {K : ℕ} {F : Type*} [Field F]

theorem prod_rising_incf (f : Fin K → F) (m : Fin K → ℕ) (i : Fin K) :
    ∏ k, rising (f k) (incf m i k) = (∏ k, rising (f k) (m k)) * (f i + ((m i : ℕ) : F)) := by
  have hsplit : ∀ g : Fin K → ℕ, (∏ k, rising (f k) (g k))
      = rising (f i) (g i) * ∏ k ∈ Finset.univ.erase i, rising (f k) (g k) :=
    fun g => (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
  have herase : ∀ k ∈ Finset.univ.erase i, rising (f k) (incf m i k) = rising (f k) (m k) := by
    intro k hk
    rw [incf_of_ne _ (Finset.mem_erase.mp hk).1]
  rw [hsplit (incf m i), hsplit m, Finset.prod_congr rfl herase, incf_self, rising_succ]
  ring

variable [LinearOrder F] [IsStrictOrderedRing F]

theorem qOne_marginal {θ : F} {π : Fin K → F} (hθ : 0 < θ) (hπ : ∑ i, π i = 1)
    (m : Fin K → ℕ) : ∑ k, qOne θ π (incf m k) = qOne θ π m := by
  have hR : rising θ (∑ i, m i) ≠ 0 := rising_ne_zero hθ _
  have hNnn : (0 : F) ≤ ((∑ i, m i : ℕ) : F) := Nat.cast_nonneg _
  have hlast : θ + ((∑ i, m i : ℕ) : F) ≠ 0 := by positivity
  have hterm : ∀ k : Fin K, qOne θ π (incf m k)
      = (∏ i, rising (θ * π i) (m i)) * (θ * π k + ((m k : ℕ) : F))
        / rising θ ((∑ i, m i) + 1) := by
    intro k
    rw [qOne, sum_incf, prod_rising_incf]
  rw [Finset.sum_congr rfl fun k _ => hterm k, ← Finset.sum_div]
  have hnum : ∑ k, (∏ i, rising (θ * π i) (m i)) * (θ * π k + ((m k : ℕ) : F))
      = (∏ i, rising (θ * π i) (m i)) * (θ + ((∑ i, m i : ℕ) : F)) := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, hπ, mul_one, ← Nat.cast_sum]
  rw [hnum, rising_succ, qOne]
  field_simp

structure IsSolutionOneGen (θ : F) (P : Fin K → Fin K → F) (q : (Fin K → ℕ) → F) : Prop where
  empty : q (fun _ => 0) = 1
  norm : ∑ i, q (incf (fun _ => 0) i) = 1
  recursion : ∀ m : Fin K → ℕ,
    ((((∑ k, m k) * ((∑ k, m k) - 1) : ℕ) : F) + θ * ((∑ k, m k : ℕ) : F)) * q m
      = (∑ i, ((m i * (m i - 1) : ℕ) : F) * q (decf m i))
        + θ * ∑ i, ∑ k, ((m i : ℕ) : F) * P k i * q (incf (decf m i) k)

theorem qOne_isSolutionOneGen {θ : F} {π : Fin K → F} (hθ : 0 < θ) (hπ : ∑ i, π i = 1) :
    IsSolutionOneGen θ (fun _ j => π j) (qOne θ π) where
  empty := qOne_zero
  norm := by rw [qOne_marginal hθ hπ (fun _ => 0), qOne_zero]
  recursion m := by
    have hmut : ∀ i : Fin K, (∑ k, ((m i : ℕ) : F) * π i * qOne θ π (incf (decf m i) k))
        = ((m i : ℕ) : F) * π i * qOne θ π (decf m i) := by
      intro i
      rw [← Finset.mul_sum, qOne_marginal hθ hπ]
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hmut i, Finset.mul_sum,
      ← Finset.sum_add_distrib, qOne_recursion hθ m]
    exact Finset.sum_congr rfl fun i _ => by ring

theorem IsSolutionOneGen.eq_qOne_of_marginal {θ : F} {π : Fin K → F} (hθ : 0 < θ)
    {q : (Fin K → ℕ) → F} (hq : IsSolutionOneGen θ (fun _ j => π j) q)
    (hcons : ∀ m : Fin K → ℕ, ∑ k, q (incf m k) = q m) : q = qOne θ π := by
  funext m₀
  induction hN : ∑ k, m₀ k using Nat.strong_induction_on generalizing m₀ with
  | _ N IH =>
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · have hm : m₀ = fun _ => 0 := by
        funext i
        exact Finset.sum_eq_zero_iff.mp (hN.trans h0) i (Finset.mem_univ i)
      rw [hm, hq.empty, qOne_zero]
    · have hrec := hq.recursion m₀
      have hmut : ∀ i : Fin K, (∑ k, ((m₀ i : ℕ) : F) * π i * q (incf (decf m₀ i) k))
          = ((m₀ i : ℕ) : F) * π i * q (decf m₀ i) := by
        intro i
        rw [← Finset.mul_sum, hcons]
      rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hmut i, Finset.mul_sum,
        ← Finset.sum_add_distrib] at hrec
      have hstep : ∀ i : Fin K, q (decf m₀ i) = qOne θ π (decf m₀ i) ∨ m₀ i = 0 := by
        intro i
        by_cases hi : m₀ i = 0
        · exact Or.inr hi
        · refine Or.inl (IH (∑ k, decf m₀ i k) ?_ (decf m₀ i) rfl)
          have := sum_decf (f := m₀) (i := i) hi
          omega
      have hsum : (∑ i, (((m₀ i * (m₀ i - 1) : ℕ) : F) * q (decf m₀ i)
            + θ * (((m₀ i : ℕ) : F) * π i * q (decf m₀ i))))
          = ∑ i, (((m₀ i * (m₀ i - 1) : ℕ) : F) + θ * π i * ((m₀ i : ℕ) : F))
            * qOne θ π (decf m₀ i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rcases hstep i with h | h
        · rw [h]; ring
        · rw [h]; simp
      rw [hsum, ← qOne_recursion hθ m₀] at hrec
      have hD : (0 : F) < (((∑ k, m₀ k) * ((∑ k, m₀ k) - 1) : ℕ) : F)
          + θ * ((∑ k, m₀ k : ℕ) : F) := by
        have h1 : (0 : F) ≤ (((∑ k, m₀ k) * ((∑ k, m₀ k) - 1) : ℕ) : F) := Nat.cast_nonneg _
        have h2 : (0 : F) < ((∑ k, m₀ k : ℕ) : F) := by
          have : 0 < ∑ k, m₀ k := by omega
          exact_mod_cast this
        nlinarith
      exact mul_left_cancel₀ hD.ne' hrec

theorem biallelic_sampling_eq_qOne {u12 u21 : F} (h12 : 0 ≤ u12) (h21 : 0 ≤ u21)
    (hs : u12 + u21 ≠ 0) :
    IsSolutionOneGen (thetaOf u12 u21) (jump (thetaOf u12 u21) (rate2 u12 u21))
      (qOne (thetaOf u12 u21) (piOf u12 u21)) := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  rw [jump_rate2 h2 hs]
  exact qOne_isSolutionOneGen (thetaOf_pos h12 h21 hs) (sum_piOf hs)

end Rhone.MarkovChain.Biallelic
