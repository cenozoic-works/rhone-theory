/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Analysis.DenominatorEquation.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.PrincipalIdealDomain

/-! # Block separation of the roots of `E_{i,j}`: squarefree and coprime reduction -/

@[expose] public section

namespace Rhone.Analysis.DenominatorEquation

open Polynomial

section Arithmetic

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

def Wsep (a b t : F) : F := a ^ 2 + b ^ 2 + t ^ 2 + 4 * t * (a + b)

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem Wsep_eq (a b t : F) :
    (a + b + t) ^ 2 - 2 * (a * b) + 2 * t * (a + b) = Wsep a b t := by
  rw [Wsep]; ring

theorem Wsep_pos {a b t : F} (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 < t) : 0 < Wsep a b t := by
  have h1 : 0 < t ^ 2 := by positivity
  have h2 : 0 ≤ a ^ 2 := sq_nonneg a
  have h3 : 0 ≤ b ^ 2 := sq_nonneg b
  have h4 : 0 ≤ 4 * t * (a + b) := by positivity
  rw [Wsep]
  linarith

def z1sep (a b t : F) : F :=
  -((a + b + t) * (a + b + t - 1) - 2 * (t + 1) * (a * b) + 2 * t * (a + 1) * (b + 1)) / t

theorem z1sep_eq (a b t : F) : z1sep a b t = -(Wsep a b t - (a + b + t) + 2 * t) / t := by
  rw [z1sep, Wsep]; ring

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem z1sep_scaling (a b t lam : F) (ht : t ≠ 0) (hlam : lam ≠ 0) :
    z1sep (lam * a) (lam * b) (lam * t)
      = -(lam * Wsep a b t - (a + b + t) + 2 * t) / t := by
  rw [z1sep, Wsep]
  field_simp
  ring

theorem z1sep_injective {a b t lam : F} (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 < t)
    (hlam : lam ≠ 0) (h : z1sep (lam * a) (lam * b) (lam * t) = z1sep a b t) : lam = 1 := by
  have ht0 : t ≠ 0 := ht.ne'
  rw [z1sep_scaling a b t lam ht0 hlam, z1sep_eq] at h
  rw [div_eq_div_iff ht0 ht0] at h
  have h3 : -(lam * Wsep a b t - (a + b + t) + 2 * t)
      = -(Wsep a b t - (a + b + t) + 2 * t) := mul_right_cancel₀ ht0 h
  have hW : 0 < Wsep a b t := Wsep_pos ha hb ht
  have h4 : (lam - 1) * Wsep a b t = 0 := by linarith
  rcases mul_eq_zero.mp h4 with h5 | h5
  · linarith
  · exact absurd h5 hW.ne'

end Arithmetic

section Core

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

theorem separation_core {i j p q t t' : ℕ} (ht : 1 ≤ t) (ht' : 1 ≤ t')
    (hti : t ≤ i) (htj : t ≤ j)
    (hp : i * t' = p * t) (hq : j * t' = q * t)
    (hz : z1sep ((p : F) - (t' : F)) ((q : F) - (t' : F)) ((t' : F))
        = z1sep ((i : F) - (t : F)) ((j : F) - (t : F)) ((t : F))) :
    p = i ∧ q = j ∧ t' = t := by
  have htF : (0 : F) < (t : F) := by exact_mod_cast ht
  have ht'F : (0 : F) < (t' : F) := by exact_mod_cast ht'
  have ht0 : (t : F) ≠ 0 := htF.ne'
  obtain ⟨lam, hlamdef⟩ : ∃ lam : F, lam = (t' : F) / (t : F) := ⟨_, rfl⟩
  have hlam : lam ≠ 0 := by
    rw [hlamdef]; exact div_ne_zero ht'F.ne' ht0
  have hpF : (i : F) * (t' : F) = (p : F) * (t : F) := by exact_mod_cast hp
  have hqF : (j : F) * (t' : F) = (q : F) * (t : F) := by exact_mod_cast hq
  have hpl : (p : F) = lam * (i : F) := by
    rw [hlamdef, div_mul_eq_mul_div, eq_div_iff ht0]
    linear_combination -hpF
  have hql : (q : F) = lam * (j : F) := by
    rw [hlamdef, div_mul_eq_mul_div, eq_div_iff ht0]
    linear_combination -hqF
  have htl : (t' : F) = lam * (t : F) := by
    rw [hlamdef]; field_simp
  have ha : (0 : F) ≤ (i : F) - (t : F) := by
    have : (t : F) ≤ (i : F) := by exact_mod_cast hti
    linarith
  have hb : (0 : F) ≤ (j : F) - (t : F) := by
    have : (t : F) ≤ (j : F) := by exact_mod_cast htj
    linarith
  have hz' : z1sep (lam * ((i : F) - (t : F))) (lam * ((j : F) - (t : F))) (lam * (t : F))
      = z1sep ((i : F) - (t : F)) ((j : F) - (t : F)) ((t : F)) := by
    rw [← hz, hpl, hql, htl]
    simp only [z1sep]
    ring
  have hone : lam = 1 := z1sep_injective ha hb htF hlam hz'
  have htt : (t' : F) = (t : F) := by rw [htl, hone, one_mul]
  have httn : t' = t := by exact_mod_cast htt
  rw [httn] at hp hq
  exact ⟨Nat.eq_of_mul_eq_mul_right (by omega) hp.symm,
    Nat.eq_of_mul_eq_mul_right (by omega) hq.symm, httn⟩

end Core

section Reduction

variable {L : Type*} [Field L] {ι κ : Type*}

theorem squarefree_prod_X_sub_C {s : Finset ι} {α : ι → L} (hinj : Set.InjOn α s) :
    Squarefree (∏ t ∈ s, (X - C (α t))) :=
  (Polynomial.separable_prod_X_sub_C_iff'.mpr hinj).squarefree

theorem squarefree_of_split {f : L[X]} {c : L} {s : Finset ι} {α : ι → L} (hc : c ≠ 0)
    (hf : f = C c * ∏ t ∈ s, (X - C (α t))) (hinj : Set.InjOn α s) : Squarefree f := by
  have hassoc : Associated (∏ t ∈ s, (X - C (α t))) f := by
    refine ⟨(Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc)).unit, ?_⟩
    rw [IsUnit.unit_spec, hf]
    exact mul_comm _ _
  exact hassoc.squarefree_iff.mp (squarefree_prod_X_sub_C hinj)

theorem isCoprime_prod_X_sub_C {s : Finset ι} {α : ι → L} {g : L[X]}
    (h : ∀ t ∈ s, g.eval (α t) ≠ 0) : IsCoprime (∏ t ∈ s, (X - C (α t))) g := by
  refine IsCoprime.prod_left fun t ht => ?_
  refine (Polynomial.prime_X_sub_C (α t)).coprime_iff_not_dvd.mpr ?_
  rw [Polynomial.dvd_iff_isRoot]
  exact h t ht

theorem isCoprime_of_split {f g : L[X]} {c c' : L} {s : Finset ι} {u : Finset κ}
    {α : ι → L} {β : κ → L} (hc : c ≠ 0) (hc' : c' ≠ 0)
    (hf : f = C c * ∏ t ∈ s, (X - C (α t)))
    (hg : g = C c' * ∏ t' ∈ u, (X - C (β t')))
    (hsep : ∀ t ∈ s, ∀ t' ∈ u, α t ≠ β t') : IsCoprime f g := by
  have hQ : ∀ t ∈ s, (∏ t' ∈ u, (X - C (β t'))).eval (α t) ≠ 0 := by
    intro t ht
    rw [Polynomial.eval_prod]
    refine Finset.prod_ne_zero_iff.mpr fun t' ht' => ?_
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact sub_ne_zero.mpr (hsep t ht t' ht')
  obtain ⟨x, y, hxy⟩ := isCoprime_prod_X_sub_C hQ
  refine ⟨x * C c⁻¹, y * C c'⁻¹, ?_⟩
  have h1 : (C c⁻¹ : L[X]) * C c = 1 := by rw [← C_mul, inv_mul_cancel₀ hc, map_one]
  have h2 : (C c'⁻¹ : L[X]) * C c' = 1 := by rw [← C_mul, inv_mul_cancel₀ hc', map_one]
  rw [hf, hg]
  calc x * C c⁻¹ * (C c * ∏ t ∈ s, (X - C (α t)))
        + y * C c'⁻¹ * (C c' * ∏ t' ∈ u, (X - C (β t')))
      = x * ((C c⁻¹ : L[X]) * C c) * (∏ t ∈ s, (X - C (α t)))
        + y * ((C c'⁻¹ : L[X]) * C c') * (∏ t' ∈ u, (X - C (β t'))) := by ring
    _ = x * (∏ t ∈ s, (X - C (α t))) + y * (∏ t' ∈ u, (X - C (β t'))) := by
        rw [h1, h2, mul_one, mul_one]
    _ = 1 := hxy

end Reduction

end Rhone.Analysis.DenominatorEquation
