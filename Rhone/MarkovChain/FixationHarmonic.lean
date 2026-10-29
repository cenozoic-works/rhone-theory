/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.Moran
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Field.GeomSum

/-!
# Fixation probability as a harmonic function

Source: kimura1962, p. 714, eq. (3)–(4); ewens2004, sec. 3.4. -/

@[expose] public section

namespace Rhone.MarkovChain

open Finset

theorem harmonic_le_zero_of_absorb {N : ℕ} (P : CountKernel N) (hP : P.IsStochastic)
    (hpos : ∀ i : Fin (N + 1), (i : ℕ) < N → 0 < P i 0) (g : Fin (N + 1) → ℝ)
    (hg : P.IsHarmonic g) (h0 : g 0 = 0) (hN : g (Fin.last N) = 0) (i : Fin (N + 1)) :
    g i ≤ 0 := by
  obtain ⟨i0, -, hmax⟩ := Finset.exists_max_image Finset.univ g ⟨0, Finset.mem_univ _⟩
  refine le_trans (hmax i (Finset.mem_univ _)) ?_
  by_contra hlt
  replace hlt := not_le.mp hlt
  have hi0N : (i0 : ℕ) < N := by
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp i0.2) with h | h
    · exact h
    · exfalso
      have : i0 = Fin.last N := Fin.ext h
      rw [this, hN] at hlt
      exact lt_irrefl _ hlt
  have hexp : ∑ j, P i0 j * g j = g i0 := hg i0
  have hsum : ∑ j, P i0 j * (g i0 - g j) = 0 := by
    have : ∀ j, P i0 j * (g i0 - g j) = g i0 * P i0 j - P i0 j * g j := fun j => by ring
    simp only [this, Finset.sum_sub_distrib, ← Finset.mul_sum, hP.2, mul_one, hexp, sub_self]
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => mul_nonneg (hP.1 i0 j) (sub_nonneg.2 (hmax j (Finset.mem_univ _))))).1 hsum
    0 (Finset.mem_univ _)
  rw [h0, sub_zero] at hterm
  exact (mul_pos (hpos i0 hi0N) hlt).ne' hterm

theorem wf_isHarmonic_freq (N : ℕ) : (wf N).IsHarmonic (fun i => (i : ℝ) / N) := by
  intro i
  have h : (fun j : Fin (N + 1) => (j : ℝ) / N) =
      fun j : Fin (N + 1) => (1 / (N : ℝ)) * (j : ℝ) := by
    funext j; ring
  rw [h, CountKernel.expect_const_mul, wf_expect_id]

private theorem wf_pos_zero (N : ℕ) (i : Fin (N + 1)) (hi : (i : ℕ) < N) : 0 < wf N i 0 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) hi)
  have : (i : ℝ) / N < 1 := by
    rw [div_lt_one hN]; exact_mod_cast hi
  simp only [wf_apply, wfRow, binomRow, Fin.val_zero, Nat.choose_zero_right, Nat.cast_one,
    pow_zero, one_mul, mul_one, Nat.sub_zero]
  exact pow_pos (sub_pos.2 this) _

theorem wf_harmonic_unique {N : ℕ} (hN : 0 < N) (h : Fin (N + 1) → ℝ)
    (hh : (wf N).IsHarmonic h) (h0 : h 0 = 0) (h1 : h (Fin.last N) = 1) (i : Fin (N + 1)) :
    h i = (i : ℝ) / N := by
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hfreq := wf_isHarmonic_freq N
  have hlast : (((Fin.last N : Fin (N + 1)) : ℕ) : ℝ) = N := by simp
  have hdiff : (wf N).IsHarmonic (fun j => h j - (j : ℝ) / N) := by
    intro j
    rw [CountKernel.expect_sub, hh j, hfreq j]
  have z0 : (fun j : Fin (N + 1) => h j - (j : ℝ) / N) 0 = 0 := by simp [h0]
  have zN : (fun j : Fin (N + 1) => h j - (j : ℝ) / N) (Fin.last N) = 0 := by
    simp only [h1, hlast]; field_simp; ring
  have hdiff' : (wf N).IsHarmonic (fun j => -(h j - (j : ℝ) / N)) := by
    intro j
    have := CountKernel.expect_const_mul (wf N) (-1) (fun j => h j - (j : ℝ) / N) j
    have e : (fun j : Fin (N + 1) => -(h j - (j : ℝ) / N)) =
        fun j => -1 * (h j - (j : ℝ) / N) := by funext j; ring
    rw [e, this, hdiff j]
  have a := harmonic_le_zero_of_absorb (wf N) (wf_isStochastic N) (wf_pos_zero N) _ hdiff z0 zN i
  have b := harmonic_le_zero_of_absorb (wf N) (wf_isStochastic N) (wf_pos_zero N) _ hdiff'
    (by simp [h0]) (by simp only [h1, hlast]; field_simp; ring) i
  linarith

noncomputable def moranFixProb (N : ℕ) (r : ℝ) (i : ℕ) : ℝ :=
  (∑ k ∈ range i, (r⁻¹) ^ k) / ∑ k ∈ range N, (r⁻¹) ^ k

theorem moranFixProb_zero (N : ℕ) (r : ℝ) : moranFixProb N r 0 = 0 := by
  simp [moranFixProb]

theorem moranFixProb_self {N : ℕ} (hN : 0 < N) {r : ℝ} (hr : 0 < r) :
    moranFixProb N r N = 1 := by
  have : 0 < ∑ k ∈ range N, (r⁻¹) ^ k := by
    apply Finset.sum_pos (fun k _ => by positivity)
    exact ⟨0, mem_range.2 hN⟩
  rw [moranFixProb, div_self this.ne']

theorem moranFixProb_one (N i : ℕ) : moranFixProb N 1 i = (i : ℝ) / N := by
  simp [moranFixProb]

theorem moranFixProb_of_ne_one {r : ℝ} (hr1 : r ≠ 1) (N i : ℕ) :
    moranFixProb N r i = (1 - (r⁻¹) ^ i) / (1 - (r⁻¹) ^ N) := by
  have hs : r⁻¹ - 1 ≠ 0 := by
    intro h
    have : r⁻¹ = 1 := by linarith
    exact hr1 (inv_eq_one.mp this)
  unfold moranFixProb
  rw [geom_sum_eq (fun h => hs (by rw [h]; ring)) i, geom_sum_eq (fun h => hs (by rw [h]; ring)) N]
  rw [div_div_div_cancel_right₀ hs]
  rw [← neg_div_neg_eq]
  ring

private noncomputable def extFin {N : ℕ} (h : Fin (N + 1) → ℝ) (n : ℕ) : ℝ :=
  if hn : n < N + 1 then h ⟨n, hn⟩ else 0

private theorem extFin_coe {N : ℕ} (h : Fin (N + 1) → ℝ) (j : Fin (N + 1)) :
    extFin h (j : ℕ) = h j := by
  simp [extFin, j.2]

private theorem geom_total_pos {N : ℕ} (hN : 0 < N) {r : ℝ} (hr : 0 < r) :
    0 < ∑ k ∈ range N, (r⁻¹) ^ k := by
  apply Finset.sum_pos (fun k _ => by positivity)
  exact ⟨0, mem_range.2 hN⟩

theorem moran_harmonic_unique {N : ℕ} (hN : 0 < N) {r : ℝ} (hr : 0 < r)
    (h : Fin (N + 1) → ℝ) (hh : (moran N r).IsHarmonic h) (h0 : h 0 = 0)
    (h1 : h (Fin.last N) = 1) (i : Fin (N + 1)) :
    h i = moranFixProb N r i := by
  set s : ℝ := r⁻¹ with hs
  have hrs : r * s = 1 := mul_inv_cancel₀ hr.ne'
  set e : ℕ → ℝ := extFin h with he
  have e0 : e 0 = 0 := by
    have := extFin_coe h 0
    simpa [h0] using this
  have eN : e N = 1 := by
    have := extFin_coe h (Fin.last N)
    simpa [h1] using this
  have hstep : ∀ k, 0 < k → k < N → e (k + 1) - e k = s * (e k - e (k - 1)) := by
    intro k hk0 hkN
    have hk : k < N + 1 := by omega
    have hexp := moran_expect (r := r) e ⟨k, hk⟩
    have hef : (fun j : Fin (N + 1) => e (j : ℕ)) = h := funext (extFin_coe h)
    rw [hef, hh ⟨k, hk⟩] at hexp
    have hek : e k = h ⟨k, hk⟩ := extFin_coe h ⟨k, hk⟩
    rw [← hek] at hexp
    have hd : 0 < moranDown N r k := by
      have : (0 : ℝ) < k := by exact_mod_cast hk0
      have h2 : (0 : ℝ) < (N : ℝ) - k := by
        have : (k : ℝ) < N := by exact_mod_cast hkN
        linarith
      unfold moranDown
      positivity
    rw [moranUp_eq_mul_moranDown] at hexp
    have hz : moranDown N r k * (r * (e (k + 1) - e k) - (e k - e (k - 1))) = 0 := by
      linarith
    have hz' := (mul_eq_zero.1 hz).resolve_left hd.ne'
    have : e (k + 1) - e k = s * (r * (e (k + 1) - e k)) := by
      rw [← mul_assoc, mul_comm s r, hrs, one_mul]
    rw [this]
    congr 1
    linarith
  have hΔ : ∀ k, k < N → e (k + 1) - e k = s ^ k * e 1 := by
    intro k
    induction k with
    | zero => intro _; simp [e0]
    | succ k ih =>
      intro hk
      rw [hstep (k + 1) (by omega) hk, Nat.add_sub_cancel, ih (by omega), pow_succ]
      ring
  have hmain : ∀ n, n ≤ N → e n = e 1 * ∑ k ∈ range n, s ^ k := by
    intro n
    induction n with
    | zero => intro _; simp [e0]
    | succ n ih =>
      intro hn
      have := hΔ n (by omega)
      rw [sum_range_succ, mul_add, ← ih (by omega)]
      linarith
  have hZ := geom_total_pos hN hr
  have hZ' : 0 < ∑ k ∈ range N, s ^ k := hZ
  have he1 : e 1 * ∑ k ∈ range N, s ^ k = 1 := by rw [← hmain N le_rfl, eN]
  have hi : (i : ℕ) ≤ N := Nat.lt_succ_iff.mp i.2
  have hei : e i = h i := extFin_coe h i
  rw [← hei, moranFixProb, ← hs, eq_div_iff hZ'.ne', hmain _ hi]
  calc e 1 * (∑ k ∈ range i, s ^ k) * ∑ k ∈ range N, s ^ k
      = (∑ k ∈ range i, s ^ k) * (e 1 * ∑ k ∈ range N, s ^ k) := by ring
    _ = _ := by rw [he1, mul_one]

private theorem moranFix_step (N : ℕ) {r : ℝ} (hr : 0 < r) (m : ℕ) :
    moranUp N r m * (moranFixProb N r (m + 1) - moranFixProb N r m)
      + moranDown N r m * (moranFixProb N r (m - 1) - moranFixProb N r m) = 0 := by
  rcases m with _ | k
  · simp [moranUp_zero, moranDown_zero]
  · have hrs : r * r⁻¹ = 1 := mul_inv_cancel₀ hr.ne'
    have key : r * (r⁻¹) ^ (k + 1) = (r⁻¹) ^ k := by
      rw [pow_succ, ← mul_assoc, mul_comm r, mul_assoc, hrs, mul_one]
    unfold moranFixProb
    rw [moranUp_eq_mul_moranDown, Nat.add_sub_cancel, sum_range_succ _ (k + 1),
      sum_range_succ _ k]
    calc _ = moranDown N r (k + 1) * (r * (r⁻¹) ^ (k + 1) - (r⁻¹) ^ k)
          / ∑ k ∈ range N, (r⁻¹) ^ k := by ring
      _ = 0 := by rw [key]; simp

theorem moranFixProb_isHarmonic {N : ℕ} {r : ℝ} (hr : 0 < r) :
    (moran N r).IsHarmonic (fun i => moranFixProb N r i) := by
  intro i
  rw [moran_expect (moranFixProb N r) i]
  have := moranFix_step N hr i
  linarith

theorem moran_isHarmonic_freq (N : ℕ) : (moran N 1).IsHarmonic (fun i => (i : ℝ) / N) := by
  have h := moranFixProb_isHarmonic (N := N) (one_pos : (0 : ℝ) < 1)
  simpa only [moranFixProb_one] using h

theorem moran_neutral_harmonic_unique {N : ℕ} (hN : 0 < N) (h : Fin (N + 1) → ℝ)
    (hh : (moran N 1).IsHarmonic h) (h0 : h 0 = 0) (h1 : h (Fin.last N) = 1)
    (i : Fin (N + 1)) : h i = (i : ℝ) / N := by
  rw [moran_harmonic_unique hN one_pos h hh h0 h1 i, moranFixProb_one]

theorem moran_selection_harmonic_unique {N : ℕ} (hN : 0 < N) {r : ℝ} (hr : 0 < r)
    (hr1 : r ≠ 1) (h : Fin (N + 1) → ℝ) (hh : (moran N r).IsHarmonic h) (h0 : h 0 = 0)
    (h1 : h (Fin.last N) = 1) (i : Fin (N + 1)) :
    h i = (1 - (r⁻¹) ^ (i : ℕ)) / (1 - (r⁻¹) ^ N) := by
  rw [moran_harmonic_unique hN hr h hh h0 h1 i, moranFixProb_of_ne_one hr1]

theorem moran_isHarmonic_selection {N : ℕ} {r : ℝ} (hr : 0 < r) (hr1 : r ≠ 1) :
    (moran N r).IsHarmonic (fun i => (1 - (r⁻¹) ^ (i : ℕ)) / (1 - (r⁻¹) ^ N)) := by
  have h := moranFixProb_isHarmonic (N := N) hr
  simpa only [moranFixProb_of_ne_one hr1] using h

end Rhone.MarkovChain
