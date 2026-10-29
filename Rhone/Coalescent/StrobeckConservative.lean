/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.StructuredPair
public import Mathlib.Tactic.LinearCombination

/-!
# Strobeck's theorem for conservative migration

Source: strobeck1987, pp. 150–151, eq. (9)–(10); nagylaki1998, p. 1601, eq. (9). -/

@[expose] public section

namespace Rhone.Coalescent.StructuredPair

open Finset
open IslandPair (State)
open Structured (MigAdj MigIrreducible)

variable {d : ℕ}

def IsConservative (M : Fin d → Fin d → ℝ) (w : Fin d → ℝ) : Prop :=
  ∀ a, ∑ b, (if a ≠ b then w a * M a b else 0) = ∑ b, if a ≠ b then w b * M b a else 0

theorem IsConservative.sum_eq_zero {M : Fin d → Fin d → ℝ} {w : Fin d → ℝ}
    (hcons : IsConservative M w) (h : Fin d → ℝ) :
    ∑ a, ∑ x, (if a ≠ x then w a * M a x * (h x - h a) else 0) = 0 := by
  have h1 : ∀ a, ∑ x, (if a ≠ x then w a * M a x * (h x - h a) else 0) =
      (∑ x, if a ≠ x then w a * M a x * h x else 0) -
        h a * ∑ x, if a ≠ x then w x * M x a else 0 := by
    intro a
    rw [← hcons a, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> ring
  simp only [h1, Finset.sum_sub_distrib]
  rw [sub_eq_zero, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases hax : a = x
  · simp [hax]
  · simp only [ne_eq, hax, Ne.symm hax, not_false_eq_true, ↓reduceIte]
    ring

theorem strobeck_weighted (M : Fin d → Fin d → ℝ) (c w : Fin d → ℝ)
    (hM : ∀ a b, a ≠ b → 0 ≤ M a b) (hirr : MigIrreducible M) (hc : ∀ a, 0 < c a)
    (hcw : ∀ a, c a * w a = 1) (hcons : IsConservative M w) :
    ∑ a, w a * (chain M c hM fun a => (hc a).le).expectedTime {none} (some (a, a)) =
      (∑ a, w a) ^ 2 := by
  set u := (chain M c hM fun a => (hc a).le).expectedTime {none} with hu
  have hE : ∀ a b, (if a = b then c a * (0 - u (some (a, b))) else 0) +
      (∑ x, if a ≠ x then M a x * (u (some (x, b)) - u (some (a, b))) else 0) +
      (∑ y, if b ≠ y then M b y * (u (some (a, y)) - u (some (a, b))) else 0) = -1 := by
    intro a b
    have h := expectedTime_generator M c hM hirr hc a b
    rw [sum_generator_mul, expectedTime_none] at h
    exact h
  have hsum : ∑ a, ∑ b, w a * w b * ((if a = b then c a * (0 - u (some (a, b))) else 0) +
      (∑ x, if a ≠ x then M a x * (u (some (x, b)) - u (some (a, b))) else 0) +
      (∑ y, if b ≠ y then M b y * (u (some (a, y)) - u (some (a, b))) else 0)) =
      ∑ a, ∑ b, w a * w b * (-1) := by
    simp only [hE]
  have hL1 : ∑ a, ∑ b, w a * w b * (if a = b then c a * (0 - u (some (a, b))) else 0) =
      -∑ a, w a * u (some (a, a)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single a]
    · simp only [↓reduceIte]
      linear_combination (-(w a * u (some (a, a)))) * hcw a
    · intro b _ hb
      simp [Ne.symm hb]
    · exact fun h => absurd (mem_univ a) h
  have hL2 : ∑ a, ∑ b, w a * w b *
      (∑ x, if a ≠ x then M a x * (u (some (x, b)) - u (some (a, b))) else 0) = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun b _ => ?_
    have h0 := hcons.sum_eq_zero fun a => u (some (a, b))
    have h1 : ∑ a, w a * w b *
        (∑ x, if a ≠ x then M a x * (u (some (x, b)) - u (some (a, b))) else 0) =
        w b * ∑ a, ∑ x,
          (if a ≠ x then w a * M a x * (u (some (x, b)) - u (some (a, b))) else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      split_ifs <;> ring
    rw [h1, h0, mul_zero]
  have hL3 : ∑ a, ∑ b, w a * w b *
      (∑ y, if b ≠ y then M b y * (u (some (a, y)) - u (some (a, b))) else 0) = 0 := by
    refine Finset.sum_eq_zero fun a _ => ?_
    have h0 := hcons.sum_eq_zero fun b => u (some (a, b))
    have h1 : ∑ b, w a * w b *
        (∑ y, if b ≠ y then M b y * (u (some (a, y)) - u (some (a, b))) else 0) =
        w a * ∑ b, ∑ y,
          (if b ≠ y then w b * M b y * (u (some (a, y)) - u (some (a, b))) else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      split_ifs <;> ring
    rw [h1, h0, mul_zero]
  have hR : ∑ a, ∑ b, w a * w b * (-1) = -(∑ a, w a) ^ 2 := by
    rw [sq, Finset.sum_mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun b _ => by ring
  simp only [mul_add, Finset.sum_add_distrib] at hsum
  rw [hL1, hL2, hL3, hR] at hsum
  linarith

theorem expectedTime_perm (M : Fin d → Fin d → ℝ) (c : Fin d → ℝ)
    (hM : ∀ a b, a ≠ b → 0 ≤ M a b) (hirr : MigIrreducible M) (hc : ∀ a, 0 < c a)
    (σ : Equiv.Perm (Fin d)) (hσM : ∀ x y, M (σ x) (σ y) = M x y) (hσc : ∀ x, c (σ x) = c x)
    (a b : Fin d) :
    (chain M c hM fun a => (hc a).le).expectedTime {none} (some (σ a, σ b)) =
      (chain M c hM fun a => (hc a).le).expectedTime {none} (some (a, b)) := by
  obtain ⟨u, hu⟩ : ∃ u : State d → ℝ,
      u = (chain M c hM fun a => (hc a).le).expectedTime {none} := ⟨_, rfl⟩
  have hnone : u none = 0 := by
    rw [hu]
    exact expectedTime_none M c hM fun a => (hc a).le
  have hE : ∀ a b, ∑ t, generator M c (some (a, b)) t * u t = -1 := by
    intro a b
    rw [hu]
    exact expectedTime_generator M c hM hirr hc a b
  have huniq : ∀ v : State d → ℝ, v none = 0 →
      (∀ a b, ∑ t, generator M c (some (a, b)) t * v t = -1) → v = u := by
    intro v h0 hg
    rw [hu]
    exact eq_expectedTime_of_generator M c hM hirr hc h0 hg
  rw [← hu]
  have hgen : ∀ a b, ∑ t, generator M c (some (a, b)) t *
      u (t.map (Prod.map σ σ)) = -1 := by
    intro a b
    have key := hE (σ a) (σ b)
    rw [sum_generator_mul] at key
    rw [sum_generator_mul (f := fun t => u (t.map (Prod.map σ σ))), ← key]
    simp only [Option.map_some, Option.map_none, Prod.map_apply]
    congr 1
    · congr 1
      · simp only [EmbeddingLike.apply_eq_iff_eq, hσc]
      · refine (Finset.sum_congr rfl fun x _ => ?_).trans (Equiv.sum_comp σ fun x =>
          if σ a ≠ x then M (σ a) x * (u (some (x, σ b)) - u (some (σ a, σ b))) else 0)
        simp only [ne_eq, EmbeddingLike.apply_eq_iff_eq, hσM]
    · refine (Finset.sum_congr rfl fun y _ => ?_).trans (Equiv.sum_comp σ fun y =>
        if σ b ≠ y then M (σ b) y * (u (some (σ a, y)) - u (some (σ a, σ b))) else 0)
      simp only [ne_eq, EmbeddingLike.apply_eq_iff_eq, hσM]
  exact congrFun (huniq (fun t => u (t.map (Prod.map σ σ))) hnone hgen) (some (a, b))

theorem strobeck_transitive (M : Fin d → Fin d → ℝ) {c : ℝ}
    (hM : ∀ a b, a ≠ b → 0 ≤ M a b) (hirr : MigIrreducible M) (hc : 0 < c)
    (hsym : ∀ a b, ∃ σ : Equiv.Perm (Fin d), σ a = b ∧ ∀ x y, M (σ x) (σ y) = M x y)
    (a : Fin d) :
    (chain M (fun _ => c) hM fun _ => hc.le).expectedTime {none} (some (a, a)) = d / c := by
  set u := (chain M (fun _ => c) hM fun _ => hc.le).expectedTime {none} with hu
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.pos_of_ne_zero fun h => by
    subst h
    exact a.elim0).ne'
  have hall : ∀ a', u (some (a', a')) = u (some (a, a)) := by
    intro a'
    obtain ⟨σ, hσ, hσM⟩ := hsym a a'
    have h := expectedTime_perm M (fun _ => c) hM hirr (fun _ => hc) σ hσM (fun _ => rfl) a a
    rw [hσ] at h
    exact h
  have hrow : ∀ a', (∑ b, if a' ≠ b then M a' b else 0) = ∑ b, if a ≠ b then M a b else 0 := by
    intro a'
    obtain ⟨σ, hσ, hσM⟩ := hsym a a'
    rw [← hσ, ← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [ne_eq, EmbeddingLike.apply_eq_iff_eq, hσM]
  have hcol : ∀ a', (∑ b, if a' ≠ b then M b a' else 0) = ∑ b, if a ≠ b then M b a else 0 := by
    intro a'
    obtain ⟨σ, hσ, hσM⟩ := hsym a a'
    rw [← hσ, ← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [ne_eq, EmbeddingLike.apply_eq_iff_eq, hσM]
  have htot : ∑ a', (∑ b, if a' ≠ b then M a' b else 0) =
      ∑ a', ∑ b, if a' ≠ b then M b a' else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    simp only [ne_comm]
  have hrc : (∑ b, if a ≠ b then M a b else 0) = ∑ b, if a ≠ b then M b a else 0 := by
    simp only [hrow, hcol, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at htot
    exact mul_left_cancel₀ hd htot
  have hcons : IsConservative M fun _ => 1 / c := by
    intro a'
    have h1 : ∀ F : Fin d → ℝ, (∑ b, if a' ≠ b then 1 / c * F b else 0) =
        1 / c * ∑ b, if a' ≠ b then F b else 0 := by
      intro F
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => by split_ifs <;> ring
    rw [h1 fun b => M a' b, h1 fun b => M b a', hrow, hcol, hrc]
  have hW := strobeck_weighted M (fun _ => c) (fun _ => 1 / c) hM hirr (fun _ => hc)
    (fun _ => mul_one_div_cancel hc.ne') hcons
  rw [← hu] at hW
  simp only [hall] at hW
  rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    nsmul_eq_mul] at hW
  have h2 : (d : ℝ) * (1 / c) * (u (some (a, a)) - d / c) = 0 := by
    linear_combination hW
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd h3 (mul_ne_zero hd (one_div_ne_zero hc.ne'))
  · linarith

theorem strobeck_two_deme_ne (M : Fin 2 → Fin 2 → ℝ) (c w : Fin 2 → ℝ)
    (hM : ∀ a b, a ≠ b → 0 < M a b) (hc : ∀ a, 0 < c a)
    (hcw : ∀ a, c a * w a = 1) (hcons : IsConservative M w) (hw : w 0 ≠ w 1) :
    (chain M c (fun a b h => (hM a b h).le) fun a => (hc a).le).expectedTime {none}
        (some (0, 0)) ≠
      (chain M c (fun a b h => (hM a b h).le) fun a => (hc a).le).expectedTime {none}
        (some (1, 1)) := by
  have hirr : MigIrreducible M := fun a b => by
    by_cases h : a = b
    · rw [h]
    · exact Relation.ReflTransGen.single ⟨h, hM a b h⟩
  set u := (chain M c (fun a b h => (hM a b h).le) fun a => (hc a).le).expectedTime {none}
    with hu
  intro heq
  have hE : ∀ a b, (if a = b then c a * (0 - u (some (a, b))) else 0) +
      (∑ x, if a ≠ x then M a x * (u (some (x, b)) - u (some (a, b))) else 0) +
      (∑ y, if b ≠ y then M b y * (u (some (a, y)) - u (some (a, b))) else 0) = -1 := by
    intro a b
    have h := expectedTime_generator M c (fun a b h => (hM a b h).le) hirr hc a b
    rw [sum_generator_mul, expectedTime_none] at h
    exact h
  have e00 := hE 0 0
  have e11 := hE 1 1
  have hk := hcons 0
  simp [Fin.sum_univ_two] at e00 e11 hk
  apply hw
  linear_combination w 0 * e00 - w 1 * e11 + u (some (0, 0)) * hcw 0 -
    u (some (1, 1)) * hcw 1 + (1 + 2 * w 1 * M 1 0) * heq -
    (u (some (1, 0)) + u (some (0, 1)) - 2 * u (some (0, 0))) * hk

end Rhone.Coalescent.StructuredPair
