/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.Propagation.Propagate

/-! # The first row and the first column: the pole survives at every distance -/

@[expose] public section

namespace Rhone.Probability.Propagation

open Matrix LinearAlgebra.Tridiag

variable {K : Type*} [Field K] [CharZero K]

theorem w_row_ne_zero {θA θB ρ γA κB γB : K} {p q : ℕ} {v : ℕ → K} (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hγ : γA ≠ 0) (hv : v 0 ≠ 0) (hE : ∀ i, p < i → E K i q θA θB ρ ≠ 0) :
    ∀ k, ∃ t, t ≤ min (p + k) q ∧ w θA θB ρ 0 γA κB γB p q v (p + k) q t ≠ 0 := by
  intro k
  induction k with
  | zero =>
    refine ⟨0, Nat.zero_le _, ?_⟩
    rw [Nat.add_zero, w_base_le (Nat.zero_le _)]
    exact hv
  | succ k ih =>
    obtain ⟨t0, ht0, hne0⟩ := ih
    set i : ℕ := p + (k + 1) with hi
    by_contra hcon
    have hcon' : ∀ s, s ≤ min i q → w θA θB ρ 0 γA κB γB p q v i q s = 0 := fun s hs => by
      by_contra hne
      exact hcon ⟨s, hs, hne⟩
    have hi2 : 2 ≤ i := by omega
    have hipred : i - 1 = p + k := by omega
    have hzero : (fun s : Fin (min i q + 1) => w θA θB ρ 0 γA κB γB p q v i q (s : ℕ)) = 0 := by
      funext s
      exact hcon' (s : ℕ) (by have := s.isLt; omega)
    have hrec := w_rec (θA := θA) (θB := θB) (ρ := ρ) (κA := 0) (γA := γA) (κB := κB) (γB := γB)
      (v := v) (p := p) (q := q) (i := i) (j := q) (by omega) le_rfl
      (by intro he; exact absurd (congrArg Prod.fst he) (by omega)) hi2 hq
      (hE i (by omega))
    rw [hzero, Matrix.mulVec_zero] at hrec
    have hsrc : ∀ s : Fin (min i q + 1),
        γA * ((lamA i (s : ℕ) : ℕ) : K) * w θA θB ρ 0 γA κB γB p q v (i - 1) q (s : ℕ) = 0 := by
      intro s
      have h1 := congrFun hrec s
      rw [src_row_collapse (p := p) (q := q) γA κB γB
        (w θA θB ρ 0 γA κB γB p q v) hq (fun a b u h => w_off h u) (s : ℕ)] at h1
      exact h1.symm
    have hkill : ∀ s, s ≤ min (p + k) q → w θA θB ρ 0 γA κB γB p q v (p + k) q s = 0 := by
      intro s hs
      have hslt : s < min i q + 1 := by omega
      have h1 := hsrc ⟨s, hslt⟩
      simp only at h1
      have hlam : ((lamA i s : ℕ) : K) ≠ 0 := lamA_ne_zero hi2 (by omega)
      have := (mul_eq_zero.1 h1).resolve_left (mul_ne_zero hγ hlam)
      rwa [hipred] at this
    exact hne0 (hkill t0 ht0)

theorem w_col_ne_zero {θA θB ρ κA γA γB : K} {p q : ℕ} {v : ℕ → K} (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hγ : γB ≠ 0) (hv : v 0 ≠ 0) (hE : ∀ j, q < j → E K p j θA θB ρ ≠ 0) :
    ∀ k, ∃ t, t ≤ min p (q + k) ∧ w θA θB ρ κA γA 0 γB p q v p (q + k) t ≠ 0 := by
  intro k
  induction k with
  | zero =>
    refine ⟨0, Nat.zero_le _, ?_⟩
    rw [Nat.add_zero, w_base_le (Nat.zero_le _)]
    exact hv
  | succ k ih =>
    obtain ⟨t0, ht0, hne0⟩ := ih
    set j : ℕ := q + (k + 1) with hj
    by_contra hcon
    have hcon' : ∀ s, s ≤ min p j → w θA θB ρ κA γA 0 γB p q v p j s = 0 := fun s hs => by
      by_contra hne
      exact hcon ⟨s, hs, hne⟩
    have hj2 : 2 ≤ j := by omega
    have hjpred : j - 1 = q + k := by omega
    have hzero : (fun s : Fin (min p j + 1) => w θA θB ρ κA γA 0 γB p q v p j (s : ℕ)) = 0 := by
      funext s
      exact hcon' (s : ℕ) (by have := s.isLt; omega)
    have hrec := w_rec (θA := θA) (θB := θB) (ρ := ρ) (κA := κA) (γA := γA) (κB := 0) (γB := γB)
      (v := v) (p := p) (q := q) (i := p) (j := j) le_rfl (by omega)
      (by intro he; exact absurd (congrArg Prod.snd he) (by omega)) hp hj2
      (hE j (by omega))
    rw [hzero, Matrix.mulVec_zero] at hrec
    have hsrc : ∀ s : Fin (min p j + 1),
        γB * ((lamB j (s : ℕ) : ℕ) : K) * w θA θB ρ κA γA 0 γB p q v p (j - 1) (s : ℕ) = 0 := by
      intro s
      have h1 := congrFun hrec s
      rw [src_col_collapse (p := p) (q := q) κA γA γB
        (w θA θB ρ κA γA 0 γB p q v) hp (fun a b u h => w_off h u) (s : ℕ)] at h1
      exact h1.symm
    have hkill : ∀ s, s ≤ min p (q + k) → w θA θB ρ κA γA 0 γB p q v p (q + k) s = 0 := by
      intro s hs
      have hslt : s < min p j + 1 := by omega
      have h1 := hsrc ⟨s, hslt⟩
      simp only at h1
      have hlam : ((lamB j s : ℕ) : K) ≠ 0 := lamB_ne_zero hj2 (by omega)
      have := (mul_eq_zero.1 h1).resolve_left (mul_ne_zero hγ hlam)
      rwa [hjpred] at this
    exact hne0 (hkill t0 ht0)

theorem res_row_ne_zero {θA θB ρ γA κB γB : K} {p q : ℕ} {v : ℕ → K} {r : ℕ → ℕ → ℕ → K}
    {c : K} (hp : 2 ≤ p) (hq : 2 ≤ q) (hγ : γA ≠ 0) (hv : v 0 ≠ 0) (hc : c ≠ 0)
    (hE : ∀ i, p < i → E K i q θA θB ρ ≠ 0)
    (hprop : ∀ i j t, t ≤ min i j → r i j t = c * w θA θB ρ 0 γA κB γB p q v i j t) :
    ∀ k, ∃ t, t ≤ min (p + k) q ∧ r (p + k) q t ≠ 0 := by
  intro k
  obtain ⟨t, ht, hne⟩ := w_row_ne_zero hp hq hγ hv hE k
  exact ⟨t, ht, by rw [hprop _ _ _ ht]; exact mul_ne_zero hc hne⟩

theorem res_col_ne_zero {θA θB ρ κA γA γB : K} {p q : ℕ} {v : ℕ → K} {r : ℕ → ℕ → ℕ → K}
    {c : K} (hp : 2 ≤ p) (hq : 2 ≤ q) (hγ : γB ≠ 0) (hv : v 0 ≠ 0) (hc : c ≠ 0)
    (hE : ∀ j, q < j → E K p j θA θB ρ ≠ 0)
    (hprop : ∀ i j t, t ≤ min i j → r i j t = c * w θA θB ρ κA γA 0 γB p q v i j t) :
    ∀ k, ∃ t, t ≤ min p (q + k) ∧ r p (q + k) t ≠ 0 := by
  intro k
  obtain ⟨t, ht, hne⟩ := w_col_ne_zero (κA := κA) (γA := γA) hp hq hγ hv hE k
  exact ⟨t, ht, by rw [hprop _ _ _ ht]; exact mul_ne_zero hc hne⟩

end Rhone.Probability.Propagation
