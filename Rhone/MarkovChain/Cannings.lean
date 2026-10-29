/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Cannings models: exchangeable offspring numbers

Source: cannings1974, sec. 3, eq. (7), p. 267; ewens2004, sec. 3.3. -/

@[expose] public section

namespace Rhone.MarkovChain

open Finset

structure CanningsModel (N : ℕ) (Ω : Type*) [Fintype Ω] where
  w : Ω → ℝ
  ν : Ω → Fin N → ℕ
  w_nonneg : ∀ ω, 0 ≤ w ω
  sum_w : ∑ ω, w ω = 1
  sum_ν : ∀ ω, ∑ k, ν ω k = N
  exchangeable : ∀ (σ : Equiv.Perm (Fin N)) (f : (Fin N → ℕ) → ℝ),
    ∑ ω, w ω * f (fun k => ν ω (σ k)) = ∑ ω, w ω * f (ν ω)

namespace CanningsModel

variable {N : ℕ} {Ω : Type*} [Fintype Ω] (M : CanningsModel N Ω)

def expectedOffspring (k : Fin N) : ℝ := ∑ ω, M.w ω * (M.ν ω k : ℝ)

theorem expectedOffspring_eq (k l : Fin N) : M.expectedOffspring k = M.expectedOffspring l := by
  have h := M.exchangeable (Equiv.swap k l) (fun x => (x k : ℝ))
  simp only [Equiv.swap_apply_left] at h
  exact h.symm.trans rfl

theorem expected_offspring (k : Fin N) : M.expectedOffspring k = 1 := by
  have hN : 0 < N := Fin.pos k
  have hsum : ∑ l, M.expectedOffspring l = N := by
    unfold expectedOffspring
    rw [Finset.sum_comm]
    have : ∀ ω, ∑ l, M.w ω * (M.ν ω l : ℝ) = M.w ω * N := fun ω => by
      rw [← Finset.mul_sum]
      congr 1
      exact_mod_cast M.sum_ν ω
    simp only [this, ← Finset.sum_mul, M.sum_w, one_mul]
  have hconst : ∑ l, M.expectedOffspring l = N * M.expectedOffspring k := by
    rw [Finset.sum_congr rfl (fun l _ => M.expectedOffspring_eq l k)]
    simp
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have : (N : ℝ) * M.expectedOffspring k = N * 1 := by rw [← hconst, hsum, mul_one]
  exact mul_left_cancel₀ hN' this

theorem expected_next_count (S : Finset (Fin N)) :
    ∑ ω, M.w ω * (∑ k ∈ S, (M.ν ω k : ℝ)) = S.card := by
  have : ∑ ω, M.w ω * (∑ k ∈ S, (M.ν ω k : ℝ)) = ∑ k ∈ S, M.expectedOffspring k := by
    unfold expectedOffspring
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun ω _ => by rw [Finset.mul_sum]
  rw [this, Finset.sum_congr rfl (fun k _ => M.expected_offspring k)]
  simp

end CanningsModel

def moranOffspring (N : ℕ) (pd : Fin N × Fin N) (k : Fin N) : ℕ :=
  (if k = pd.2 then 0 else 1) + (if k = pd.1 then 1 else 0)

noncomputable def moranModel (N : ℕ) (hN : 0 < N) : CanningsModel N (Fin N × Fin N) where
  w _ := 1 / (N : ℝ) ^ 2
  ν := moranOffspring N
  w_nonneg _ := by positivity
  sum_w := by
    have : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast
    field_simp
  sum_ν pd := by
    have hp : ∑ k : Fin N, (if k = pd.1 then 1 else 0) = 1 := by simp
    have hd : ∑ k : Fin N, (if k = pd.2 then 0 else 1) = N - 1 := by
      have : ∀ k : Fin N, (if k = pd.2 then 0 else 1) = 1 - (if k = pd.2 then 1 else 0) := by
        intro k; split_ifs <;> simp
      simp only [this]
      rw [Finset.sum_tsub_distrib]
      · simp
      · intro k _; split_ifs <;> simp
    simp only [moranOffspring, Finset.sum_add_distrib, hp, hd]
    omega
  exchangeable σ f := by
    refine (Fintype.sum_equiv ((σ.symm).prodCongr (σ.symm)) _ _ ?_)
    intro pd
    have : (fun k => moranOffspring N pd (σ k)) =
        moranOffspring N ((σ.symm).prodCongr (σ.symm) pd) := by
      funext k
      simp only [moranOffspring, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd]
      have h1 : (σ k = pd.2) ↔ (k = σ.symm pd.2) := by
        rw [Equiv.eq_symm_apply]
      have h2 : (σ k = pd.1) ↔ (k = σ.symm pd.1) := by
        rw [Equiv.eq_symm_apply]
      simp only [h1, h2]
    rw [this]

end Rhone.MarkovChain
