/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.Recursion.Config

/-! # The per-allele form `Γ`, the rank-one source `Φ`, and monomorphy -/

@[expose] public section

namespace Rhone.Probability.Converse

open Finset

variable {K : ℕ} {F : Type*} [Field F]

def uu (θ : F) (n : ℕ) : F := (n : F) - 1 + θ

def GcoefA (α : Fin K → F) (m : Fin K → ℕ) (i : Fin K) : F :=
  ((((∑ k, m k : ℕ) : F) - 1) * α i - (((m i : ℕ) : F) - 1) * (∑ k, α k))
    / (α i + ((m i : ℕ) : F) - 1)

def Gcoef (θ : F) (π : Fin K → F) (m : Fin K → ℕ) (i : Fin K) : F :=
  ((((∑ k, m k : ℕ) : F) - 1) * (θ * π i) - (((m i : ℕ) : F) - 1) * θ)
    / (θ * π i + ((m i : ℕ) : F) - 1)

def PhiA (α : Fin K → F) (m : Fin K → ℕ) : F := ∑ i, ((m i : ℕ) : F) * GcoefA α m i

def Phi (θ : F) (π : Fin K → F) (m : Fin K → ℕ) : F := ∑ i, ((m i : ℕ) : F) * Gcoef θ π m i

theorem sum_mul_pi {θ : F} {π : Fin K → F} (hs : ∑ k, π k = 1) : ∑ k, θ * π k = θ := by
  rw [← Finset.mul_sum, hs, mul_one]

theorem Gcoef_eq_GcoefA {θ : F} {π : Fin K → F} (hs : ∑ k, π k = 1) (m : Fin K → ℕ)
    (i : Fin K) : Gcoef θ π m i = GcoefA (fun k => θ * π k) m i := by
  rw [Gcoef, GcoefA, sum_mul_pi hs]

theorem Phi_eq_PhiA {θ : F} {π : Fin K → F} (hs : ∑ k, π k = 1) (m : Fin K → ℕ) :
    Phi θ π m = PhiA (fun k => θ * π k) m := by
  simp only [Phi, PhiA, Gcoef_eq_GcoefA hs]

theorem GcoefA_of_mi_one {α : Fin K → F} {m : Fin K → ℕ} {i : Fin K} (h : m i = 1)
    (hα : α i ≠ 0) : GcoefA α m i = (((∑ k, m k : ℕ) : F) - 1) := by
  rw [GcoefA, h]
  push_cast
  rw [show α i + (1 : F) - 1 = α i by ring, show (1 : F) - 1 = 0 by ring, zero_mul, sub_zero]
  field_simp

theorem Gcoef_of_mi_one {θ : F} {π : Fin K → F} {m : Fin K → ℕ} {i : Fin K} (h : m i = 1)
    (hα : θ * π i ≠ 0) : Gcoef θ π m i = (((∑ k, m k : ℕ) : F) - 1) := by
  rw [Gcoef, h]
  push_cast
  rw [show θ * π i + (1 : F) - 1 = θ * π i by ring, show (1 : F) - 1 = 0 by ring, zero_mul,
    sub_zero, mul_div_assoc, div_self hα, mul_one]

theorem term_GcoefA (α : Fin K → F) (m : Fin K → ℕ) (i : Fin K)
    (h : m i ≠ 0 → α i + ((m i : ℕ) : F) - 1 ≠ 0) :
    ((m i : ℕ) : F) * GcoefA α m i
      = ((m i : ℕ) : F) * (((∑ k, m k : ℕ) : F) - 1)
        - uu (∑ k, α k) (∑ k, m k)
          * (((m i : ℕ) : F) * (((m i : ℕ) : F) - 1) / (α i + ((m i : ℕ) : F) - 1)) := by
  by_cases h0 : m i = 0
  · rw [h0]
    simp
  · have hd := h h0
    rw [GcoefA, uu]
    field_simp
    ring

theorem PhiA_eq_alt (α : Fin K → F) (m : Fin K → ℕ)
    (h : ∀ i, m i ≠ 0 → α i + ((m i : ℕ) : F) - 1 ≠ 0) :
    PhiA α m
      = ((∑ k, m k : ℕ) : F) * (((∑ k, m k : ℕ) : F) - 1)
        - uu (∑ k, α k) (∑ k, m k)
          * ∑ i, ((m i : ℕ) : F) * (((m i : ℕ) : F) - 1) / (α i + ((m i : ℕ) : F) - 1) := by
  rw [PhiA, Finset.sum_congr rfl fun i _ => term_GcoefA α m i (h i), Finset.sum_sub_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, ← Nat.cast_sum]

theorem Phi_eq_alt {θ : F} {π : Fin K → F} (hs : ∑ k, π k = 1) (m : Fin K → ℕ)
    (h : ∀ i, m i ≠ 0 → θ * π i + ((m i : ℕ) : F) - 1 ≠ 0) :
    Phi θ π m
      = ((∑ k, m k : ℕ) : F) * (((∑ k, m k : ℕ) : F) - 1)
        - uu θ (∑ k, m k)
          * ∑ i, ((m i : ℕ) : F) * (((m i : ℕ) : F) - 1) / (θ * π i + ((m i : ℕ) : F) - 1) := by
  rw [Phi_eq_PhiA hs, PhiA_eq_alt _ m h, sum_mul_pi hs]

def Mono (m : Fin K → ℕ) : Prop := ∃ i, ∀ k, k ≠ i → m k = 0

instance (m : Fin K → ℕ) : Decidable (Mono m) := by
  unfold Mono
  infer_instance

def mu (m : Fin K → ℕ) : ℕ := if Mono m then 1 else 0

def sing (m : Fin K → ℕ) : ℕ := (Finset.univ.filter fun i => m i = 1).card

@[simp] theorem mu_of_mono {m : Fin K → ℕ} (h : Mono m) : mu m = 1 := ite_eq_left h

@[simp] theorem mu_of_not_mono {m : Fin K → ℕ} (h : ¬ Mono m) : mu m = 0 := ite_eq_right h

theorem mu_le_one (m : Fin K → ℕ) : mu m ≤ 1 := by
  unfold mu; split <;> omega

theorem not_mono_of_pair {m : Fin K → ℕ} {i j : Fin K} (hij : i ≠ j) (hi : m i ≠ 0)
    (hj : m j ≠ 0) : ¬ Mono m := by
  rintro ⟨l, hl⟩
  by_cases hli : i = l
  · exact hj (hl j (by omega))
  · exact hi (hl i hli)

theorem exists_pair_of_not_mono {m : Fin K → ℕ} (hK : 0 < K) (h : ¬ Mono m) :
    ∃ i j, i ≠ j ∧ m i ≠ 0 ∧ m j ≠ 0 := by
  by_contra hc
  push Not at hc
  refine h ?_
  by_cases hex : ∃ i, m i ≠ 0
  · obtain ⟨i, hi⟩ := hex
    refine ⟨i, fun k hk => ?_⟩
    by_contra hk0
    exact hi (hc k i hk hk0)
  · push Not at hex
    exact ⟨⟨0, hK⟩, fun k _ => hex k⟩

theorem mu_le_mu_decf {m : Fin K → ℕ} {i : Fin K} (hi : m i ≠ 0) :
    mu m ≤ mu (Rhone.LinearAlgebra.Recursion.decf m i) := by
  by_cases hm : Mono m
  · obtain ⟨l, hl⟩ := id hm
    have hil : i = l := by
      by_contra hne
      exact hi (hl i hne)
    subst hil
    rw [mu_of_mono hm, mu_of_mono ⟨i, fun k hk => by
      rw [Rhone.LinearAlgebra.Recursion.decf_of_ne _ hk, hl k hk]⟩]
  · rw [mu_of_not_mono hm]
    exact Nat.zero_le _

end Rhone.Probability.Converse
