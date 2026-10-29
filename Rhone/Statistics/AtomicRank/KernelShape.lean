/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.AtomicRank.LinearOperator

/-! # Exact kernel shape of the finite-grid polynomial jump operator -/

@[expose] public section

noncomputable section
open Polynomial
namespace Rhone.Statistics.AtomicRank

def pureCoefficients (r : ℕ) (a : ℝ) : Coefficients :=
  Finsupp.single (r, 0) a + Finsupp.single (0, r) (2 * a)

lemma scaledPowerSum_zero {h : ℝ} (hh : h ≠ 0) : scaledPowerSum h 0 = X - C h := by
  ext i
  rw [scaledPowerSum_coeff]
  by_cases h0 : i = 0
  · subst i
    simp [powerSum_zero]
  by_cases h1 : i = 1
  · subst i
    simp [powerSum_zero, coeff_one, hh]
  · simp [powerSum_zero, coeff_X, coeff_one, coeff_C, h0, h1, eq_comm]

lemma jumpBasis_pure {h : ℝ} (hh : h ≠ 0) (z : ℝ) (r : ℕ) :
    jumpBasis h z r 0 + (2 : ℝ) • jumpBasis h z 0 r = 0 := by
  simp only [jumpBasis, Nat.cast_zero, zero_mul, C_0, zero_sub,
    zero_add, pow_one, scaledPowerSum_zero hh, smul_eq_C_mul]
  have hc : (2 : ℝ[X]) * C (h / 2) = C h := by
    rw [← C_ofNat 2, ← C_mul]
    congr 1
    ring
  norm_num only [map_ofNat]
  linear_combination C ((r : ℝ) * z ^ (r - 1)) * hc

lemma jump_pure {h : ℝ} (hh : h ≠ 0) (z : ℝ) (r : ℕ) (a : ℝ) :
    jump h z (pureCoefficients r a) = 0 := by
  simp only [pureCoefficients, map_add, jump, Finsupp.linearCombination_single]
  have he := congrArg (fun P : ℝ[X] => a • P) (jumpBasis_pure hh z r)
  simpa [smul_add, smul_smul, mul_comm] using he

lemma pure_apply (r : ℕ) (a : ℝ) (v : ℕ × ℕ) :
    pureCoefficients r a v =
      (if v = (r, 0) then a else 0) + (if v = (0, r) then 2 * a else 0) := by
  simp [pureCoefficients, Finsupp.single_apply, eq_comm]

lemma pure_degree (r : ℕ) (a : ℝ) : DegreeBound (pureCoefficients r a) r := by
  intro v hv
  have h1 : v ≠ (r, 0) := by intro he; subst v; simp at hv
  have h2 : v ≠ (0, r) := by intro he; subst v; simp at hv
  simp [pure_apply, h1, h2]

lemma kernel_top_shape {h : ℝ} (hh : h ≠ 0) {f : Coefficients} {r : ℕ}
    (hr : 0 < r) (hd : DegreeBound f r) (hz : ∀ z : ℝ, jump h z f = 0) :
    (∀ p q : ℕ, p + q = r → 0 < p → 0 < q → f (p, q) = 0) ∧
      f (0, r) = 2 * f (r, 0) := by
  apply homogeneous_coefficients_shape r hr (fun p q => f (p, q))
  intro p q hpq hp
  apply top_coefficient_relation hh hp
  · simpa [hpq] using hd
  · exact hz

lemma strip_top_degree {h : ℝ} (hh : h ≠ 0) {f : Coefficients} {n : ℕ}
    (hd : DegreeBound f (n + 1)) (hz : ∀ z : ℝ, jump h z f = 0) :
    DegreeBound (f - pureCoefficients (n + 1) (f (n + 1, 0))) n := by
  have ht := kernel_top_shape hh (Nat.succ_pos n) hd hz
  intro v hv
  simp only [Finsupp.sub_apply]
  by_cases he : v.1 + v.2 = n + 1
  · by_cases h1 : v.1 = 0
    · have hvv : v = (0, n + 1) := by ext <;> dsimp <;> omega
      subst v
      simp [pure_apply, ht.2]
    · by_cases h2 : v.2 = 0
      · have hvv : v = (n + 1, 0) := by ext <;> dsimp <;> omega
        subst v
        simp [pure_apply]
      · have hf := ht.1 v.1 v.2 he (Nat.pos_of_ne_zero h1) (Nat.pos_of_ne_zero h2)
        have hp1 : v ≠ (n + 1, 0) := by intro hvv; exact h2 (congrArg Prod.snd hvv)
        have hp2 : v ≠ (0, n + 1) := by intro hvv; exact h1 (congrArg Prod.fst hvv)
        simpa [pure_apply, hp1, hp2] using hf
  · have hv' : n + 1 < v.1 + v.2 := by omega
    rw [hd v hv', pure_degree (n + 1) (f (n + 1, 0)) v hv', sub_self]

theorem jump_kernel_shape {h : ℝ} (hh : h ≠ 0) (n : ℕ) (f : Coefficients)
    (hd : DegreeBound f n) (hz : ∀ z : ℝ, jump h z f = 0) :
    (∀ p q : ℕ, 0 < p → 0 < q → f (p, q) = 0) ∧
      ∀ r : ℕ, 0 < r → f (0, r) = 2 * f (r, 0) := by
  induction n generalizing f with
  | zero =>
      constructor
      · intro p q hp hq
        exact hd (p, q) (by dsimp; omega)
      · intro r hr
        rw [hd (0, r) (by simpa using hr), hd (r, 0) (by simpa using hr), mul_zero]
  | succ n ih =>
      let g := f - pureCoefficients (n + 1) (f (n + 1, 0))
      have hgd : DegreeBound g n := strip_top_degree hh hd hz
      have hgz : ∀ z : ℝ, jump h z g = 0 := by
        intro z
        simp [g, map_sub, hz z, jump_pure hh]
      obtain ⟨hm, hpure⟩ := ih g hgd hgz
      constructor
      · intro p q hp hq
        have hg := hm p q hp hq
        simpa [g, pure_apply, hp.ne', hq.ne'] using hg
      · intro r hr
        by_cases he : r = n + 1
        · subst r
          exact (kernel_top_shape hh (Nat.succ_pos n) hd hz).2
        · have hg := hpure r hr
          simpa [g, pure_apply, he, hr.ne'] using hg

end Rhone.Statistics.AtomicRank
