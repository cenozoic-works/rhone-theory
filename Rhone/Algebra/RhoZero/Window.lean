/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.ClosedForms.Overcount

/-! # The `ρ = 0` `ℓ`-states are indexed by their lineage count -/

@[expose] public section

namespace Rhone.Algebra.RhoZero

open Finset

structure Prim where
  α : ℕ
  β : ℕ
  γ : ℕ
  hα : 0 < α
  hβ : 0 < β
  hγ : 0 < γ
  hprim : Nat.gcd (Nat.gcd α β) γ = 1

def Prim.propTo (L : Prim) (i j k : ℕ) : Prop :=
  ∃ c : ℚ, 0 < c ∧ ((k * (k - 1) : ℕ) : ℚ) = c * (L.γ : ℚ) ∧ (i : ℚ) = c * (L.α : ℚ)
    ∧ (j : ℚ) = c * (L.β : ℚ)

theorem propTo_iff_cross (L : Prim) {i j k : ℕ} (hk : 2 ≤ k) :
    L.propTo i j k ↔ L.γ * i = L.α * (k * (k - 1)) ∧ L.γ * j = L.β * (k * (k - 1)) := by
  have hγ0 : (0 : ℚ) < (L.γ : ℚ) := by exact_mod_cast L.hγ
  constructor
  · rintro ⟨c, _, h1, h2, h3⟩
    constructor
    · have hq : (L.γ : ℚ) * (i : ℚ) = (L.α : ℚ) * ((k * (k - 1) : ℕ) : ℚ) := by
        rw [h2, h1]; ring
      exact_mod_cast hq
    · have hq : (L.γ : ℚ) * (j : ℚ) = (L.β : ℚ) * ((k * (k - 1) : ℕ) : ℚ) := by
        rw [h3, h1]; ring
      exact_mod_cast hq
  · rintro ⟨e1, e2⟩
    have hm0 : 0 < k * (k - 1) := Nat.mul_pos (by omega) (by omega)
    have hm0' : (0 : ℚ) < ((k * (k - 1) : ℕ) : ℚ) := by exact_mod_cast hm0
    have hq1 : (L.γ : ℚ) * (i : ℚ) = (L.α : ℚ) * ((k * (k - 1) : ℕ) : ℚ) := by exact_mod_cast e1
    have hq2 : (L.γ : ℚ) * (j : ℚ) = (L.β : ℚ) * ((k * (k - 1) : ℕ) : ℚ) := by exact_mod_cast e2
    refine ⟨((k * (k - 1) : ℕ) : ℚ) / (L.γ : ℚ), div_pos hm0' hγ0, ?_, ?_, ?_⟩
    · field_simp
    · rw [div_mul_eq_mul_div, eq_div_iff (ne_of_gt hγ0)]
      linarith [hq1]
    · rw [div_mul_eq_mul_div, eq_div_iff (ne_of_gt hγ0)]
      linarith [hq2]

theorem propTo_iff_param (L : Prim) {i j k : ℕ} (hk : 2 ≤ k) :
    L.propTo i j k ↔ (L.γ ∣ L.α * (k * (k - 1)) ∧ L.γ ∣ L.β * (k * (k - 1))
      ∧ i = L.α * (k * (k - 1)) / L.γ ∧ j = L.β * (k * (k - 1)) / L.γ) := by
  rw [propTo_iff_cross L hk]
  constructor
  · rintro ⟨e1, e2⟩
    refine ⟨⟨i, e1.symm⟩, ⟨j, e2.symm⟩, ?_, ?_⟩
    · rw [← e1, Nat.mul_div_cancel_left _ L.hγ]
    · rw [← e2, Nat.mul_div_cancel_left _ L.hγ]
  · rintro ⟨d1, d2, hi, hj⟩
    exact ⟨by rw [hi, Nat.mul_div_cancel' d1], by rw [hj, Nat.mul_div_cancel' d2]⟩

structure EllType (L : Prim) (n i j k : ℕ) : Prop where
  two_le_i : 2 ≤ i
  two_le_j : 2 ≤ j
  k_le_n : k ≤ n
  max_le_k : max i j ≤ k
  k_le_add : k ≤ i + j
  isPropTo : L.propTo i j k

theorem EllType.two_le_k {L : Prim} {n i j k : ℕ} (h : EllType L n i j k) : 2 ≤ k :=
  le_trans h.two_le_i (le_trans (le_max_left i j) h.max_le_k)

theorem EllType.i_le_n {L : Prim} {n i j k : ℕ} (h : EllType L n i j k) : i ≤ n :=
  le_trans (le_trans (le_max_left i j) h.max_le_k) h.k_le_n

theorem EllType.j_le_n {L : Prim} {n i j k : ℕ} (h : EllType L n i j k) : j ≤ n :=
  le_trans (le_trans (le_max_right i j) h.max_le_k) h.k_le_n

def Kwin (L : Prim) (n : ℕ) : Finset ℕ :=
  (Finset.Icc 2 n).filter (fun k =>
    L.γ ∣ Nat.gcd L.α L.β * (k * (k - 1))
      ∧ 2 * L.γ ≤ min L.α L.β * (k * (k - 1))
      ∧ max L.α L.β * (k * (k - 1)) ≤ n * L.γ
      ∧ max L.α L.β * (k - 1) ≤ L.γ
      ∧ L.γ ≤ (L.α + L.β) * (k - 1))

private theorem min_mul_right (x y z : ℕ) : min x y * z = min (x * z) (y * z) :=
  (Nat.mul_min_mul_right x y z).symm

private theorem max_mul_right (x y z : ℕ) : max x y * z = max (x * z) (y * z) :=
  (Nat.mul_max_mul_right x y z).symm

theorem mem_Kwin_iff (L : Prim) (n k : ℕ) :
    k ∈ Kwin L n ↔ ∃ i j, EllType L n i j k := by
  constructor
  · intro hk
    rw [Kwin, Finset.mem_filter, Finset.mem_Icc] at hk
    obtain ⟨⟨hk2, hkn⟩, hdvd, hmin2, _, hmaxg, hgmax⟩ := hk
    have hdA : L.γ ∣ L.α * (k * (k - 1)) :=
      dvd_trans hdvd (mul_dvd_mul_right (Nat.gcd_dvd_left _ _) _)
    have hdB : L.γ ∣ L.β * (k * (k - 1)) :=
      dvd_trans hdvd (mul_dvd_mul_right (Nat.gcd_dvd_right _ _) _)
    refine ⟨L.α * (k * (k - 1)) / L.γ, L.β * (k * (k - 1)) / L.γ, ?_⟩
    set i := L.α * (k * (k - 1)) / L.γ with hidef
    set j := L.β * (k * (k - 1)) / L.γ with hjdef
    have hgi : L.γ * i = L.α * (k * (k - 1)) := Nat.mul_div_cancel' hdA
    have hgj : L.γ * j = L.β * (k * (k - 1)) := Nat.mul_div_cancel' hdB
    have hik : L.γ * i ≤ L.γ * k := by
      have h1 : L.α * (k - 1) ≤ L.γ :=
        le_trans (Nat.mul_le_mul (le_max_left _ _) (le_refl _)) hmaxg
      calc L.γ * i = L.α * (k - 1) * k := by rw [hgi]; ring
        _ ≤ L.γ * k := Nat.mul_le_mul h1 (le_refl k)
    have hjk : L.γ * j ≤ L.γ * k := by
      have h1 : L.β * (k - 1) ≤ L.γ :=
        le_trans (Nat.mul_le_mul (le_max_right _ _) (le_refl _)) hmaxg
      calc L.γ * j = L.β * (k - 1) * k := by rw [hgj]; ring
        _ ≤ L.γ * k := Nat.mul_le_mul h1 (le_refl k)
    have h2i : 2 ≤ i := by
      refine Nat.le_of_mul_le_mul_left ?_ L.hγ
      calc L.γ * 2 = 2 * L.γ := by ring
        _ ≤ min L.α L.β * (k * (k - 1)) := hmin2
        _ ≤ L.α * (k * (k - 1)) := Nat.mul_le_mul (min_le_left _ _) (le_refl _)
        _ = L.γ * i := hgi.symm
    have h2j : 2 ≤ j := by
      refine Nat.le_of_mul_le_mul_left ?_ L.hγ
      calc L.γ * 2 = 2 * L.γ := by ring
        _ ≤ min L.α L.β * (k * (k - 1)) := hmin2
        _ ≤ L.β * (k * (k - 1)) := Nat.mul_le_mul (min_le_right _ _) (le_refl _)
        _ = L.γ * j := hgj.symm
    have hkadd : L.γ * k ≤ L.γ * (i + j) := by
      calc L.γ * k ≤ (L.α + L.β) * (k - 1) * k := Nat.mul_le_mul hgmax (le_refl k)
        _ = L.α * (k * (k - 1)) + L.β * (k * (k - 1)) := by ring
        _ = L.γ * (i + j) := by rw [← hgi, ← hgj]; ring
    exact
      { two_le_i := h2i
        two_le_j := h2j
        k_le_n := hkn
        max_le_k := max_le (Nat.le_of_mul_le_mul_left hik L.hγ)
          (Nat.le_of_mul_le_mul_left hjk L.hγ)
        k_le_add := Nat.le_of_mul_le_mul_left hkadd L.hγ
        isPropTo := (propTo_iff_cross L hk2).mpr ⟨hgi, hgj⟩ }
  · rintro ⟨i, j, h⟩
    have hk2 : 2 ≤ k := h.two_le_k
    obtain ⟨hgi, hgj⟩ := (propTo_iff_cross L hk2).mp h.isPropTo
    have hik : i ≤ k := le_trans (le_max_left i j) h.max_le_k
    have hjk : j ≤ k := le_trans (le_max_right i j) h.max_le_k
    rw [Kwin, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨hk2, h.k_le_n⟩, ?_, ?_, ?_, ?_, ?_⟩
    · have hd : L.γ ∣ Nat.gcd (L.α * (k * (k - 1))) (L.β * (k * (k - 1))) :=
        Nat.dvd_gcd ⟨i, hgi.symm⟩ ⟨j, hgj.symm⟩
      rwa [Nat.gcd_mul_right] at hd
    · rw [min_mul_right, ← hgi, ← hgj]
      refine le_min ?_ ?_
      · calc 2 * L.γ = L.γ * 2 := by ring
          _ ≤ L.γ * i := Nat.mul_le_mul (le_refl _) h.two_le_i
      · calc 2 * L.γ = L.γ * 2 := by ring
          _ ≤ L.γ * j := Nat.mul_le_mul (le_refl _) h.two_le_j
    · rw [max_mul_right, ← hgi, ← hgj]
      refine max_le ?_ ?_
      · calc L.γ * i ≤ L.γ * n := Nat.mul_le_mul (le_refl _) h.i_le_n
          _ = n * L.γ := by ring
      · calc L.γ * j ≤ L.γ * n := Nat.mul_le_mul (le_refl _) h.j_le_n
          _ = n * L.γ := by ring
    · rw [max_mul_right]
      refine max_le ?_ ?_
      · refine Nat.le_of_mul_le_mul_right ?_ (show 0 < k by omega)
        calc L.α * (k - 1) * k = L.γ * i := by rw [hgi]; ring
          _ ≤ L.γ * k := Nat.mul_le_mul (le_refl _) hik
      · refine Nat.le_of_mul_le_mul_right ?_ (show 0 < k by omega)
        calc L.β * (k - 1) * k = L.γ * j := by rw [hgj]; ring
          _ ≤ L.γ * k := Nat.mul_le_mul (le_refl _) hjk
    · refine Nat.le_of_mul_le_mul_right ?_ (show 0 < k by omega)
      calc L.γ * k ≤ L.γ * (i + j) := Nat.mul_le_mul (le_refl _) h.k_le_add
        _ = L.α * (k * (k - 1)) + L.β * (k * (k - 1)) := by rw [← hgi, ← hgj]; ring
        _ = (L.α + L.β) * (k - 1) * k := by ring

theorem le_of_mem_Kwin {L : Prim} {n k : ℕ} (h : k ∈ Kwin L n) : k ≤ n := by
  rw [Kwin, Finset.mem_filter, Finset.mem_Icc] at h
  exact h.1.2

theorem two_le_of_mem_Kwin {L : Prim} {n k : ℕ} (h : k ∈ Kwin L n) : 2 ≤ k := by
  rw [Kwin, Finset.mem_filter, Finset.mem_Icc] at h
  exact h.1.1

theorem Kwin_mono (L : Prim) {m n : ℕ} (h : m ≤ n) : Kwin L m ⊆ Kwin L n := by
  intro k hk
  rw [mem_Kwin_iff] at hk ⊢
  obtain ⟨i, j, ht⟩ := hk
  exact ⟨i, j, { ht with k_le_n := le_trans ht.k_le_n h }⟩

theorem propTo_unique (L : Prim) {i₁ j₁ i₂ j₂ k : ℕ} (hk : 2 ≤ k)
    (h₁ : L.propTo i₁ j₁ k) (h₂ : L.propTo i₂ j₂ k) : i₁ = i₂ ∧ j₁ = j₂ := by
  obtain ⟨e1, e2⟩ := (propTo_iff_cross L hk).mp h₁
  obtain ⟨f1, f2⟩ := (propTo_iff_cross L hk).mp h₂
  exact ⟨Nat.eq_of_mul_eq_mul_left L.hγ (by rw [e1, f1]),
    Nat.eq_of_mul_eq_mul_left L.hγ (by rw [e2, f2])⟩

theorem lt_of_propTo_of_lt (L : Prim) {i₁ j₁ k₁ i₂ j₂ k₂ : ℕ} (hk₁ : 2 ≤ k₁) (hlt : k₁ < k₂)
    (h₁ : L.propTo i₁ j₁ k₁) (h₂ : L.propTo i₂ j₂ k₂) : i₁ < i₂ ∧ j₁ < j₂ := by
  have hk₂ : 2 ≤ k₂ := by omega
  obtain ⟨e1, e2⟩ := (propTo_iff_cross L hk₁).mp h₁
  obtain ⟨f1, f2⟩ := (propTo_iff_cross L hk₂).mp h₂
  obtain ⟨a, rfl⟩ : ∃ a, k₁ = a + 2 := ⟨k₁ - 2, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, k₂ = b + 2 := ⟨k₂ - 2, by omega⟩
  have hab : a < b := by omega
  have hstep : (a + 2) * (a + 2 - 1) < (b + 2) * (b + 2 - 1) := by
    have h1 : a + 2 - 1 = a + 1 := by omega
    have h2 : b + 2 - 1 = b + 1 := by omega
    rw [h1, h2]
    nlinarith
  constructor
  · refine Nat.lt_of_mul_lt_mul_left (a := L.γ) ?_
    rw [e1, f1]
    exact mul_lt_mul_of_pos_left hstep L.hα
  · refine Nat.lt_of_mul_lt_mul_left (a := L.γ) ?_
    rw [e2, f2]
    exact mul_lt_mul_of_pos_left hstep L.hβ

theorem fullyTyped_forces (L : Prim) {k : ℕ} (hk : 2 ≤ k) (h : L.propTo k k k) :
    L.α = 1 ∧ L.β = 1 ∧ L.γ = k - 1 := by
  obtain ⟨e1, e2⟩ := (propTo_iff_cross L hk).mp h
  have hk0 : 0 < k := by omega
  have g1 : L.γ = L.α * (k - 1) := by
    refine Nat.eq_of_mul_eq_mul_right hk0 ?_
    calc L.γ * k = L.α * (k * (k - 1)) := e1
      _ = L.α * (k - 1) * k := by ring
  have g2 : L.γ = L.β * (k - 1) := by
    refine Nat.eq_of_mul_eq_mul_right hk0 ?_
    calc L.γ * k = L.β * (k * (k - 1)) := e2
      _ = L.β * (k - 1) * k := by ring
  have hk1 : 0 < k - 1 := by omega
  have hab : L.α = L.β := Nat.eq_of_mul_eq_mul_right hk1 (by rw [← g1, ← g2])
  have hd : L.α ∣ Nat.gcd (Nat.gcd L.α L.β) L.γ :=
    Nat.dvd_gcd (Nat.dvd_gcd dvd_rfl (hab ▸ dvd_rfl)) ⟨k - 1, g1⟩
  rw [L.hprim] at hd
  have hα1 : L.α = 1 := Nat.dvd_one.mp hd
  exact ⟨hα1, hab ▸ hα1, by rw [g1, hα1, one_mul]⟩

theorem shape_of_succ (L : Prim) {n i₁ j₁ i₂ j₂ k₂ : ℕ}
    (h₁ : EllType L n i₁ j₁ (k₂ + 1)) (h₂ : EllType L n i₂ j₂ k₂) :
    (i₁ = i₂ + 2 ∧ j₁ = j₂ + 2 ∧ L.α = 1 ∧ L.β = 1 ∧ L.γ = k₂ ∧ i₁ = k₂ + 1 ∧ j₁ = k₂ + 1)
      ∨ (i₁ = i₂ + 2 ∧ j₁ = j₂ + 1 ∧ L.α = 2 ∧ L.β = 1 ∧ L.γ = 2 * k₂ ∧ 5 ≤ k₂
          ∧ k₂ % 2 = 1 ∧ i₁ = k₂ + 1 ∧ 2 * j₁ = k₂ + 1)
      ∨ (i₁ = i₂ + 1 ∧ j₁ = j₂ + 2 ∧ L.α = 1 ∧ L.β = 2 ∧ L.γ = 2 * k₂ ∧ 5 ≤ k₂
          ∧ k₂ % 2 = 1 ∧ 2 * i₁ = k₂ + 1 ∧ j₁ = k₂ + 1) := by
  have hk2 : 2 ≤ k₂ := h₂.two_le_k
  obtain ⟨e, rfl⟩ : ∃ e, k₂ = e + 2 := ⟨k₂ - 2, by omega⟩
  obtain ⟨c1, c2⟩ := (propTo_iff_cross L (show 2 ≤ e + 2 + 1 by omega)).mp h₁.isPropTo
  obtain ⟨d1, d2⟩ := (propTo_iff_cross L (show 2 ≤ e + 2 by omega)).mp h₂.isPropTo
  have hs1 : (e + 2 + 1) * (e + 2 + 1 - 1) = (e + 3) * (e + 2) := by
    rw [show e + 2 + 1 - 1 = e + 2 from by omega]
  have hs2 : (e + 2) * (e + 2 - 1) = (e + 2) * (e + 1) := by
    rw [show e + 2 - 1 = e + 1 from by omega]
  rw [hs1] at c1 c2
  rw [hs2] at d1 d2
  obtain ⟨hii, hjj⟩ := lt_of_propTo_of_lt L (show 2 ≤ e + 2 by omega)
    (show e + 2 < e + 2 + 1 by omega) h₂.isPropTo h₁.isPropTo
  have hA : L.α * (e + 2) ≤ L.γ := by
    refine Nat.le_of_mul_le_mul_right ?_ (show 0 < e + 3 by omega)
    calc L.α * (e + 2) * (e + 3) = L.γ * i₁ := by rw [c1]; ring
      _ ≤ L.γ * (e + 3) :=
        Nat.mul_le_mul (le_refl _) (by
          have := le_trans (le_max_left i₁ j₁) h₁.max_le_k
          omega)
  have hB : L.β * (e + 2) ≤ L.γ := by
    refine Nat.le_of_mul_le_mul_right ?_ (show 0 < e + 3 by omega)
    calc L.β * (e + 2) * (e + 3) = L.γ * j₁ := by rw [c2]; ring
      _ ≤ L.γ * (e + 3) :=
        Nat.mul_le_mul (le_refl _) (by
          have := le_trans (le_max_right i₁ j₁) h₁.max_le_k
          omega)
  have hdi : L.γ * i₁ = L.γ * i₂ + 2 * (L.α * (e + 2)) := by rw [c1, d1]; ring
  have hdj : L.γ * j₁ = L.γ * j₂ + 2 * (L.β * (e + 2)) := by rw [c2, d2]; ring
  have hiub : i₁ ≤ i₂ + 2 := by
    refine Nat.le_of_mul_le_mul_left ?_ L.hγ
    calc L.γ * i₁ = L.γ * i₂ + 2 * (L.α * (e + 2)) := hdi
      _ ≤ L.γ * i₂ + 2 * L.γ := by omega
      _ = L.γ * (i₂ + 2) := by ring
  have hjub : j₁ ≤ j₂ + 2 := by
    refine Nat.le_of_mul_le_mul_left ?_ L.hγ
    calc L.γ * j₁ = L.γ * j₂ + 2 * (L.β * (e + 2)) := hdj
      _ ≤ L.γ * j₂ + 2 * L.γ := by omega
      _ = L.γ * (j₂ + 2) := by ring
  have hdi' : L.γ * (i₁ - i₂) = 2 * (L.α * (e + 2)) := by
    have h : L.γ * (i₁ - i₂) + L.γ * i₂ = L.γ * i₁ := by
      rw [← Nat.mul_add, show i₁ - i₂ + i₂ = i₁ from by omega]
    omega
  have hdj' : L.γ * (j₁ - j₂) = 2 * (L.β * (e + 2)) := by
    have h : L.γ * (j₁ - j₂) + L.γ * j₂ = L.γ * j₁ := by
      rw [← Nat.mul_add, show j₁ - j₂ + j₂ = j₁ from by omega]
    omega
  have hdi12 : i₁ - i₂ = 1 ∨ i₁ - i₂ = 2 := by omega
  have hdj12 : j₁ - j₂ = 1 ∨ j₁ - j₂ = 2 := by omega
  rcases hdi12 with hi1 | hi2 <;> rcases hdj12 with hj1 | hj2
  · exfalso
    rw [hi1, mul_one] at hdi'
    rw [hj1, mul_one] at hdj'
    have hab : L.α = L.β := Nat.eq_of_mul_eq_mul_right (show 0 < e + 2 by omega) (by omega)
    have hd : L.α ∣ Nat.gcd (Nat.gcd L.α L.β) L.γ :=
      Nat.dvd_gcd (Nat.dvd_gcd dvd_rfl ⟨1, by omega⟩) ⟨2 * (e + 2), by rw [hdi']; ring⟩
    rw [L.hprim] at hd
    have hα1 : L.α = 1 := Nat.dvd_one.mp hd
    have hβ1 : L.β = 1 := by omega
    have hγ : L.γ = 2 * (e + 2) := by rw [hdi', hα1]; ring
    have hi2v : 2 * i₂ = e + 1 := by
      refine Nat.eq_of_mul_eq_mul_left (show 0 < e + 2 by omega) ?_
      calc (e + 2) * (2 * i₂) = L.γ * i₂ := by rw [hγ]; ring
        _ = L.α * ((e + 2) * (e + 1)) := d1
        _ = (e + 2) * (e + 1) := by rw [hα1]; ring
    have hj2v : 2 * j₂ = e + 1 := by
      refine Nat.eq_of_mul_eq_mul_left (show 0 < e + 2 by omega) ?_
      calc (e + 2) * (2 * j₂) = L.γ * j₂ := by rw [hγ]; ring
        _ = L.β * ((e + 2) * (e + 1)) := d2
        _ = (e + 2) * (e + 1) := by rw [hβ1]; ring
    have hadd := h₂.k_le_add
    omega
  · right; right
    rw [hi1, mul_one] at hdi'
    rw [hj2] at hdj'
    have hba : L.β = 2 * L.α := by
      refine Nat.eq_of_mul_eq_mul_right (show 0 < e + 2 by omega) ?_
      have hx : 2 * L.α * (e + 2) = 2 * (L.α * (e + 2)) := by ring
      omega
    have hd : L.α ∣ Nat.gcd (Nat.gcd L.α L.β) L.γ :=
      Nat.dvd_gcd (Nat.dvd_gcd dvd_rfl ⟨2, by omega⟩) ⟨2 * (e + 2), by rw [hdi']; ring⟩
    rw [L.hprim] at hd
    have hα1 : L.α = 1 := Nat.dvd_one.mp hd
    have hβ2 : L.β = 2 := by omega
    have hγ : L.γ = 2 * (e + 2) := by rw [hdi', hα1]; ring
    have hi1v : 2 * i₁ = e + 3 := by
      refine Nat.eq_of_mul_eq_mul_left (show 0 < e + 2 by omega) ?_
      calc (e + 2) * (2 * i₁) = L.γ * i₁ := by rw [hγ]; ring
        _ = L.α * ((e + 3) * (e + 2)) := c1
        _ = (e + 2) * (e + 3) := by rw [hα1]; ring
    have hj1v : j₁ = e + 3 := by
      refine Nat.eq_of_mul_eq_mul_left (show 0 < 2 * (e + 2) by omega) ?_
      calc 2 * (e + 2) * j₁ = L.γ * j₁ := by rw [hγ]
        _ = L.β * ((e + 3) * (e + 2)) := c2
        _ = 2 * (e + 2) * (e + 3) := by rw [hβ2]; ring
    have hi2v : 2 * i₂ = e + 1 := by
      refine Nat.eq_of_mul_eq_mul_left (show 0 < e + 2 by omega) ?_
      calc (e + 2) * (2 * i₂) = L.γ * i₂ := by rw [hγ]; ring
        _ = L.α * ((e + 2) * (e + 1)) := d1
        _ = (e + 2) * (e + 1) := by rw [hα1]; ring
    have h2i2 : 2 ≤ i₂ := h₂.two_le_i
    exact ⟨by omega, by omega, hα1, hβ2, hγ, by omega, by omega, by omega, by omega⟩
  · right; left
    rw [hi2] at hdi'
    rw [hj1, mul_one] at hdj'
    have hab : L.α = 2 * L.β := by
      refine Nat.eq_of_mul_eq_mul_right (show 0 < e + 2 by omega) ?_
      have hx : 2 * L.β * (e + 2) = 2 * (L.β * (e + 2)) := by ring
      omega
    have hd : L.β ∣ Nat.gcd (Nat.gcd L.α L.β) L.γ :=
      Nat.dvd_gcd (Nat.dvd_gcd ⟨2, by omega⟩ dvd_rfl) ⟨2 * (e + 2), by rw [hdj']; ring⟩
    rw [L.hprim] at hd
    have hβ1 : L.β = 1 := Nat.dvd_one.mp hd
    have hα2 : L.α = 2 := by omega
    have hγ : L.γ = 2 * (e + 2) := by rw [hdj', hβ1]; ring
    have hj1v : 2 * j₁ = e + 3 := by
      refine Nat.eq_of_mul_eq_mul_left (show 0 < e + 2 by omega) ?_
      calc (e + 2) * (2 * j₁) = L.γ * j₁ := by rw [hγ]; ring
        _ = L.β * ((e + 3) * (e + 2)) := c2
        _ = (e + 2) * (e + 3) := by rw [hβ1]; ring
    have hi1v : i₁ = e + 3 := by
      refine Nat.eq_of_mul_eq_mul_left (show 0 < 2 * (e + 2) by omega) ?_
      calc 2 * (e + 2) * i₁ = L.γ * i₁ := by rw [hγ]
        _ = L.α * ((e + 3) * (e + 2)) := c1
        _ = 2 * (e + 2) * (e + 3) := by rw [hα2]; ring
    have hj2v : 2 * j₂ = e + 1 := by
      refine Nat.eq_of_mul_eq_mul_left (show 0 < e + 2 by omega) ?_
      calc (e + 2) * (2 * j₂) = L.γ * j₂ := by rw [hγ]; ring
        _ = L.β * ((e + 2) * (e + 1)) := d2
        _ = (e + 2) * (e + 1) := by rw [hβ1]; ring
    have h2j2 : 2 ≤ j₂ := h₂.two_le_j
    exact ⟨by omega, by omega, hα2, hβ1, hγ, by omega, by omega, by omega, by omega⟩
  · left
    rw [hi2] at hdi'
    rw [hj2] at hdj'
    have hGA : L.γ = L.α * (e + 2) := by omega
    have hGB : L.γ = L.β * (e + 2) := by omega
    have hab : L.α = L.β := Nat.eq_of_mul_eq_mul_right (show 0 < e + 2 by omega) (by omega)
    have hd : L.α ∣ Nat.gcd (Nat.gcd L.α L.β) L.γ :=
      Nat.dvd_gcd (Nat.dvd_gcd dvd_rfl ⟨1, by omega⟩) ⟨e + 2, hGA⟩
    rw [L.hprim] at hd
    have hα1 : L.α = 1 := Nat.dvd_one.mp hd
    have hβ1 : L.β = 1 := by omega
    have hγ : L.γ = e + 2 := by rw [hGA, hα1]; ring
    have hi1v : i₁ = e + 3 := by
      refine Nat.eq_of_mul_eq_mul_left (show 0 < e + 2 by omega) ?_
      calc (e + 2) * i₁ = L.γ * i₁ := by rw [hγ]
        _ = L.α * ((e + 3) * (e + 2)) := c1
        _ = (e + 2) * (e + 3) := by rw [hα1]; ring
    have hj1v : j₁ = e + 3 := by
      refine Nat.eq_of_mul_eq_mul_left (show 0 < e + 2 by omega) ?_
      calc (e + 2) * j₁ = L.γ * j₁ := by rw [hγ]
        _ = L.β * ((e + 3) * (e + 2)) := c2
        _ = (e + 2) * (e + 3) := by rw [hβ1]; ring
    exact ⟨by omega, by omega, hα1, hβ1, hγ, by omega, by omega⟩

theorem blocked_pair_iff (L : Prim) {n i₁ j₁ i₂ j₂ k₂ : ℕ}
    (h₁ : EllType L n i₁ j₁ (k₂ + 1)) (h₂ : EllType L n i₂ j₂ k₂) :
    (i₁ = i₂ + 2 ∧ j₁ = j₂ + 2) ↔ (L.α = 1 ∧ L.β = 1 ∧ L.γ = k₂) := by
  constructor
  · rintro ⟨hi, hj⟩
    rcases shape_of_succ L h₁ h₂ with h | h | h
    · exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩
    · exfalso; omega
    · exfalso; omega
  · rintro ⟨hα, hβ, hγ⟩
    rcases shape_of_succ L h₁ h₂ with h | h | h
    · exact ⟨h.1, h.2.1⟩
    · exfalso; rw [hα] at h; omega
    · exfalso; rw [hβ] at h; omega

theorem blocked_pair_iff_fullyTyped (L : Prim) {n i₁ j₁ i₂ j₂ k₂ : ℕ}
    (h₁ : EllType L n i₁ j₁ (k₂ + 1)) (h₂ : EllType L n i₂ j₂ k₂) :
    (i₁ = i₂ + 2 ∧ j₁ = j₂ + 2) ↔ (i₁ = k₂ + 1 ∧ j₁ = k₂ + 1) := by
  constructor
  · rintro ⟨hi, hj⟩
    rcases shape_of_succ L h₁ h₂ with h | h | h
    · exact ⟨h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩
    · exfalso; omega
    · exfalso; omega
  · rintro ⟨hi, hj⟩
    rcases shape_of_succ L h₁ h₂ with h | h | h
    · exact ⟨h.1, h.2.1⟩
    · exfalso
      have := h.2.2.2.2.2.2.2.2
      omega
    · exfalso
      have := h.2.2.2.2.2.2.2.1
      omega

theorem partner_mem_Kwin_iff (L : Prim) (hα : L.α = 1) (hβ : L.β = 1) {n : ℕ} (hn : L.γ ≤ n) :
    L.γ ∈ Kwin L n ↔ 3 ≤ L.γ := by
  have hγ0 : 0 < L.γ := L.hγ
  constructor
  · intro hmem
    rw [mem_Kwin_iff] at hmem
    obtain ⟨i, j, ht⟩ := hmem
    obtain ⟨e1, _⟩ := (propTo_iff_cross L ht.two_le_k).mp ht.isPropTo
    rw [hα, one_mul] at e1
    have : L.γ * i = L.γ * (L.γ - 1) := by rw [e1]
    have hi : i = L.γ - 1 := Nat.eq_of_mul_eq_mul_left hγ0 this
    have := ht.two_le_i
    omega
  · intro h3
    rw [mem_Kwin_iff]
    refine ⟨L.γ - 1, L.γ - 1, ?_⟩
    have hcross : L.γ * (L.γ - 1) = L.α * (L.γ * (L.γ - 1)) := by rw [hα, one_mul]
    have hcross' : L.γ * (L.γ - 1) = L.β * (L.γ * (L.γ - 1)) := by rw [hβ, one_mul]
    exact
      { two_le_i := by omega
        two_le_j := by omega
        k_le_n := hn
        max_le_k := by simp only [max_self]; omega
        k_le_add := by omega
        isPropTo := (propTo_iff_cross L (by omega)).mpr ⟨hcross, hcross'⟩ }

theorem Kwin_subset_of_gamma_le_two (L : Prim) (hα : L.α = 1) (hβ : L.β = 1) (h2 : L.γ ≤ 2)
    (n : ℕ) : Kwin L n ⊆ {L.γ + 1} := by
  intro k hk
  have hk2 : 2 ≤ k := two_le_of_mem_Kwin hk
  rw [Kwin, Finset.mem_filter] at hk
  obtain ⟨_, _, hmin2, _, hmaxg, hgmax⟩ := hk
  rw [hα, hβ] at hmin2 hmaxg hgmax
  simp only [min_self, max_self, one_mul] at hmin2 hmaxg hgmax
  have hk3 : k ≤ 3 := by omega
  rw [Finset.mem_singleton]
  interval_cases k <;> omega

theorem fullyTyped_mem_Kwin_iff (L : Prim) (hα : L.α = 1) (hβ : L.β = 1) (n : ℕ) :
    L.γ + 1 ∈ Kwin L n ↔ L.γ + 1 ≤ n := by
  constructor
  · exact le_of_mem_Kwin
  · intro hn
    rw [mem_Kwin_iff]
    refine ⟨L.γ + 1, L.γ + 1, ?_⟩
    have hcross : L.γ * (L.γ + 1) = L.α * ((L.γ + 1) * (L.γ + 1 - 1)) := by
      rw [hα, one_mul]
      have : L.γ + 1 - 1 = L.γ := by omega
      rw [this]
      ring
    have hcross' : L.γ * (L.γ + 1) = L.β * ((L.γ + 1) * (L.γ + 1 - 1)) := by
      rw [hβ, one_mul]
      have : L.γ + 1 - 1 = L.γ := by omega
      rw [this]
      ring
    have hγ0 : 0 < L.γ := L.hγ
    exact
      { two_le_i := by omega
        two_le_j := by omega
        k_le_n := hn
        max_le_k := by omega
        k_le_add := by omega
        isPropTo := (propTo_iff_cross L (by omega)).mpr ⟨hcross, hcross'⟩ }

theorem propTo_iff_Proportional (L : Prim) {i₀ j₀ k₀ i j k : ℕ} (hrep : L.propTo i₀ j₀ k₀) :
    L.propTo i j k ↔ ClosedForms.Proportional i j k i₀ j₀ k₀ := by
  obtain ⟨c₀, hc₀, h₀k, h₀i, h₀j⟩ := hrep
  constructor
  · rintro ⟨c, hc, hk, hi, hj⟩
    refine ⟨c / c₀, div_pos hc hc₀, ?_, ?_, ?_⟩
    · rw [hk, h₀k]
      field_simp
    · rw [hi, h₀i]
      field_simp
    · rw [hj, h₀j]
      field_simp
  · rintro ⟨c, hc, hk, hi, hj⟩
    refine ⟨c * c₀, mul_pos hc hc₀, ?_, ?_, ?_⟩
    · rw [hk, h₀k]; ring
    · rw [hi, h₀i]; ring
    · rw [hj, h₀j]; ring

end Rhone.Algebra.RhoZero
