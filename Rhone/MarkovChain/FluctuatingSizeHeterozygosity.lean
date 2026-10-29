/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.EffectiveSize
public import Mathlib.Analysis.MeanInequalities

/-!
# Heterozygosity under fluctuating population size, and the harmonic mean

Source: wright1931, pp. 110–111; ewens2004, secs. 3.2, 3.7. -/

@[expose] public section

namespace Rhone.MarkovChain

open Finset EffectiveSize

noncomputable def wfResize (M N : ℕ) : Fin (M + 1) → Fin (N + 1) → ℝ :=
  fun i j => binomRow N ((i : ℝ) / M) j

theorem wfResize_self (N : ℕ) : wfResize N N = wf N := rfl

theorem wfResize_nonneg (M N : ℕ) (i : Fin (M + 1)) (j : Fin (N + 1)) :
    0 ≤ wfResize M N i j := by
  have hle : (i : ℝ) ≤ M := by exact_mod_cast Nat.le_of_lt_succ i.isLt
  exact binomRow_nonneg (by positivity) (div_le_one_of_le₀ hle (Nat.cast_nonneg _)) _

theorem wfResize_row_sum (M N : ℕ) (i : Fin (M + 1)) : ∑ j, wfResize M N i j = 1 := by
  unfold wfResize
  rw [sum_fin_eq_range (fun j => binomRow N ((i : ℝ) / M) j), sum_binomRow]

theorem wfResize_expect_het (M : ℕ) {N : ℕ} (hN : 0 < N) (i : Fin (M + 1)) :
    ∑ j, wfResize M N i j * het N j = (1 - 1 / (N : ℝ)) * het M i := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have key : ∀ p : ℝ, ∑ j : Fin (N + 1), binomRow N p j * het N j =
      (1 - 1 / (N : ℝ)) * (2 * p * (1 - p)) := by
    intro p
    have h1 : ∑ j : Fin (N + 1), binomRow N p j * (j : ℝ) = N * p := by
      rw [sum_fin_eq_range (fun j => binomRow N p j * j), sum_binomRow_mul]
    have h2 : ∑ j : Fin (N + 1), binomRow N p j * ((j : ℝ) * j) =
        N * p * (1 - p) + (N * p) ^ 2 := by
      rw [sum_fin_eq_range (fun j => binomRow N p j * (j * j)), sum_binomRow_mul_mul]
    have e : ∀ j : Fin (N + 1), binomRow N p j * het N j =
        (2 / (N : ℝ)) * (binomRow N p j * (j : ℝ)) -
          (2 / (N : ℝ) ^ 2) * (binomRow N p j * ((j : ℝ) * j)) := by
      intro j
      unfold het
      ring
    simp only [e, sum_sub_distrib, ← mul_sum, h1, h2]
    field_simp
    ring
  exact key _

noncomputable def wfVarExpect (n : ℕ → ℕ) :
    (t : ℕ) → (Fin (n t + 1) → ℝ) → Fin (n 0 + 1) → ℝ
  | 0, f => f
  | t + 1, f => wfVarExpect n t (fun i => ∑ j, wfResize (n t) (n (t + 1)) i j * f j)

theorem wfVarExpect_const_mul (n : ℕ → ℕ) (c : ℝ) (t : ℕ) (f : Fin (n t + 1) → ℝ) :
    wfVarExpect n t (fun i => c * f i) = fun i => c * wfVarExpect n t f i := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have h : (fun i => ∑ j, wfResize (n t) (n (t + 1)) i j * (c * f j)) =
        fun i => c * ∑ j, wfResize (n t) (n (t + 1)) i j * f j := by
      funext i
      rw [mul_sum]
      exact sum_congr rfl fun j _ => by ring
    simp only [wfVarExpect]
    rw [h, ih]

theorem countKernel_expectIter_succ' {N : ℕ} (P : CountKernel N) (t : ℕ)
    (f : Fin (N + 1) → ℝ) :
    P.expectIter (t + 1) f = P.expectIter t (P.expect f) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change P.expect (P.expectIter (t + 1) f) = P.expect (P.expectIter t (P.expect f))
    rw [ih]

theorem wfVarExpect_const (N t : ℕ) (f : Fin (N + 1) → ℝ) :
    wfVarExpect (fun _ => N) t f = (wf N).expectIter t f := by
  induction t generalizing f with
  | zero => rfl
  | succ t ih =>
    rw [countKernel_expectIter_succ']
    exact ih ((wf N).expect f)

theorem wfVarExpect_het (n : ℕ → ℕ) (t : ℕ) (hpos : ∀ s, s < t → 0 < n (s + 1))
    (i : Fin (n 0 + 1)) :
    wfVarExpect n t (fun j => het (n t) j) i =
      (∏ s ∈ range t, (1 - 1 / (n (s + 1) : ℝ))) * het (n 0) i := by
  induction t with
  | zero => simp [wfVarExpect]
  | succ t ih =>
    have h : (fun k => ∑ j, wfResize (n t) (n (t + 1)) k j * het (n (t + 1)) j) =
        fun k : Fin (n t + 1) => (1 - 1 / (n (t + 1) : ℝ)) * het (n t) k := by
      funext k
      exact wfResize_expect_het (n t) (hpos t (Nat.lt_succ_self t)) k
    have ih' := ih fun s hs => hpos s (Nat.lt_succ_of_lt hs)
    simp only [wfVarExpect]
    rw [h, wfVarExpect_const_mul]
    beta_reduce
    rw [ih', prod_range_succ]
    ring

theorem sum_inv_eq_div_harmonicSize {T : ℕ} (a : Fin T → ℝ) :
    ∑ t, 1 / a t = T / harmonicSize a := by
  unfold harmonicSize
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · simp
  · have hT' : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne'
    by_cases hS : ∑ t, 1 / a t = 0
    · rw [hS]
      simp
    · field_simp

theorem mean_deficit_eq {T : ℕ} (hT : 0 < T) (a : Fin T → ℝ) :
    ∑ t, 1 / (T : ℝ) * (1 - 1 / a t) = 1 - 1 / harmonicSize a := by
  have hT' : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne'
  unfold harmonicSize
  rw [one_div_div, ← mul_sum, sum_sub_distrib]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  field_simp

theorem deficit_nonneg {T : ℕ} (a : Fin T → ℝ) (ha : ∀ t, 1 ≤ a t) (t : Fin T) :
    0 ≤ 1 - 1 / a t :=
  sub_nonneg.2 ((div_le_one (by linarith [ha t])).2 (ha t))

theorem prod_deficit_rpow {T : ℕ} (a : Fin T → ℝ) (ha : ∀ t, 1 ≤ a t) :
    ∏ t, (1 - 1 / a t) ^ (1 / (T : ℝ)) = (∏ t, (1 - 1 / a t)) ^ (1 / (T : ℝ)) :=
  Real.finsetProd_rpow _ _ (fun t _ => deficit_nonneg a ha t) _

theorem prod_deficit_le_harmonic {T : ℕ} (a : Fin T → ℝ) (ha : ∀ t, 1 ≤ a t) :
    ∏ t, (1 - 1 / a t) ≤ (1 - 1 / harmonicSize a) ^ T := by
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · simp
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hP : 0 ≤ ∏ t, (1 - 1 / a t) := prod_nonneg fun t _ => deficit_nonneg a ha t
  have hgm := Real.geom_mean_le_arith_mean_weighted univ (fun _ => 1 / (T : ℝ))
    (fun t => 1 - 1 / a t) (fun _ _ => by positivity)
    (by simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp)
    (fun t _ => deficit_nonneg a ha t)
  rw [mean_deficit_eq hT a, prod_deficit_rpow a ha] at hgm
  calc ∏ t, (1 - 1 / a t) = ((∏ t, (1 - 1 / a t)) ^ (1 / (T : ℝ))) ^ T := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hP, one_div_mul_cancel hT'.ne',
          Real.rpow_one]
    _ ≤ (1 - 1 / harmonicSize a) ^ T := pow_le_pow_left₀ (Real.rpow_nonneg hP _) hgm T

theorem prod_deficit_eq_harmonic_iff {T : ℕ} (a : Fin T → ℝ) (ha : ∀ t, 1 ≤ a t) :
    ∏ t, (1 - 1 / a t) = (1 - 1 / harmonicSize a) ^ T ↔ ∀ s t, a s = a t := by
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · simp
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hP : 0 ≤ ∏ t, (1 - 1 / a t) := prod_nonneg fun t _ => deficit_nonneg a ha t
  have hm : 0 ≤ 1 - 1 / harmonicSize a := by
    rw [← mean_deficit_eq hT a]
    exact sum_nonneg fun t _ => mul_nonneg (by positivity) (deficit_nonneg a ha t)
  have hiff := Real.geom_mean_eq_arith_mean_weighted_iff_of_pos univ (fun _ => 1 / (T : ℝ))
    (fun t => 1 - 1 / a t) (fun _ _ => by positivity)
    (by simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp)
    (fun t _ => deficit_nonneg a ha t)
  rw [mean_deficit_eq hT a, prod_deficit_rpow a ha] at hiff
  have hroot : ∏ t, (1 - 1 / a t) = (1 - 1 / harmonicSize a) ^ T ↔
      (∏ t, (1 - 1 / a t)) ^ (1 / (T : ℝ)) = 1 - 1 / harmonicSize a := by
    constructor
    · intro h
      rw [h, show (1 / (T : ℝ)) = (T : ℝ)⁻¹ from one_div _,
        Real.pow_rpow_inv_natCast hm hT.ne']
    · intro h
      rw [← h, ← Real.rpow_natCast, ← Real.rpow_mul hP, one_div_mul_cancel hT'.ne',
        Real.rpow_one]
  rw [hroot, hiff]
  have hinj : ∀ s t : Fin T, 1 - 1 / a s = 1 - 1 / a t ↔ a s = a t := by
    intro s t
    constructor
    · intro h
      have h' : (a s)⁻¹ = (a t)⁻¹ := by
        have := sub_right_injective h
        simpa [one_div] using this
      exact inv_injective h'
    · intro h
      rw [h]
  constructor
  · intro h s t
    exact (hinj s t).1 (h s (mem_univ s) t (mem_univ t))
  · intro h s _ t _
    exact (hinj s t).2 (h s t)

theorem one_sub_sum_le_prod_one_sub {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ x i) (h1 : ∀ i ∈ s, x i ≤ 1) :
    1 - ∑ i ∈ s, x i ≤ ∏ i ∈ s, (1 - x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have hxi0 := h0 i (mem_insert_self i s)
    have hxi1 := h1 i (mem_insert_self i s)
    have ih' := ih (fun j hj => h0 j (mem_insert_of_mem hj))
      (fun j hj => h1 j (mem_insert_of_mem hj))
    have hS : 0 ≤ ∑ j ∈ s, x j := sum_nonneg fun j hj => h0 j (mem_insert_of_mem hj)
    rw [sum_insert hi, prod_insert hi]
    have hstep := mul_le_mul_of_nonneg_left ih' (sub_nonneg.2 hxi1)
    have hprod : 0 ≤ x i * ∑ j ∈ s, x j := mul_nonneg hxi0 hS
    calc 1 - (x i + ∑ j ∈ s, x j) ≤ (1 - x i) * (1 - ∑ j ∈ s, x j) := by
          have : (1 - x i) * (1 - ∑ j ∈ s, x j) =
              1 - (x i + ∑ j ∈ s, x j) + x i * ∑ j ∈ s, x j := by ring
          linarith
      _ ≤ (1 - x i) * ∏ j ∈ s, (1 - x j) := hstep

theorem one_sub_pow_le_second_order {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (T : ℕ) :
    (1 - y) ^ T ≤ 1 - T * y + (T : ℝ) * ((T : ℝ) - 1) / 2 * y ^ 2 := by
  induction T with
  | zero => simp
  | succ T ih =>
    have hstep := mul_le_mul_of_nonneg_right ih (sub_nonneg.2 hy1)
    have hTT : 0 ≤ (T : ℝ) * ((T : ℝ) - 1) := by
      rcases Nat.eq_zero_or_pos T with rfl | hT
      · simp
      · have : (1 : ℝ) ≤ T := by exact_mod_cast hT
        exact mul_nonneg (by linarith) (by linarith)
    have h3 : 0 ≤ (T : ℝ) * ((T : ℝ) - 1) / 2 * y ^ 3 := by positivity
    have hid : 1 - ((T + 1 : ℕ) : ℝ) * y +
        ((T + 1 : ℕ) : ℝ) * (((T + 1 : ℕ) : ℝ) - 1) / 2 * y ^ 2 -
        (1 - T * y + (T : ℝ) * ((T : ℝ) - 1) / 2 * y ^ 2) * (1 - y) =
        (T : ℝ) * ((T : ℝ) - 1) / 2 * y ^ 3 := by
      push_cast
      ring
    rw [pow_succ]
    linarith

theorem harmonic_sub_prod_deficit_le {T : ℕ} (a : Fin T → ℝ) (ha : ∀ t, 1 ≤ a t) :
    (1 - 1 / harmonicSize a) ^ T - ∏ t, (1 - 1 / a t) ≤
      ((T : ℝ) - 1) / (2 * T) * (∑ t, 1 / a t) ^ 2 := by
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · simp
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hx0 : ∀ t, 0 ≤ 1 / a t := fun t => by
    have := ha t
    positivity
  have hx1 : ∀ t, 1 / a t ≤ 1 := fun t => (div_le_one (by linarith [ha t])).2 (ha t)
  have hS0 : 0 ≤ ∑ t, 1 / a t := sum_nonneg fun t _ => hx0 t
  have hST : ∑ t, 1 / a t ≤ T := by
    have h := sum_le_sum fun t (_ : t ∈ (univ : Finset (Fin T))) => hx1 t
    simpa using h
  have hy0 : 0 ≤ (∑ t, 1 / a t) / T := div_nonneg hS0 hT'.le
  have hy1 : (∑ t, 1 / a t) / T ≤ 1 := (div_le_one hT').2 hST
  have hmean : 1 - 1 / harmonicSize a = 1 - (∑ t, 1 / a t) / T := by
    unfold harmonicSize
    rw [one_div_div]
  have hpow := one_sub_pow_le_second_order hy0 hy1 T
  have hprod := one_sub_sum_le_prod_one_sub univ (fun t => 1 / a t) (fun t _ => hx0 t)
    (fun t _ => hx1 t)
  have hid : 1 - (T : ℝ) * ((∑ t, 1 / a t) / T) +
      (T : ℝ) * ((T : ℝ) - 1) / 2 * ((∑ t, 1 / a t) / T) ^ 2 =
      1 - ∑ t, 1 / a t + ((T : ℝ) - 1) / (2 * T) * (∑ t, 1 / a t) ^ 2 := by
    field_simp
  rw [hmean]
  linarith

theorem abs_prod_deficit_sub_harmonic_le {T : ℕ} (a : Fin T → ℝ) (ha : ∀ t, 1 ≤ a t) :
    |∏ t, (1 - 1 / a t) - (1 - 1 / harmonicSize a) ^ T| ≤ (∑ t, 1 / a t) ^ 2 / 2 := by
  have hle := prod_deficit_le_harmonic a ha
  have hgap := harmonic_sub_prod_deficit_le a ha
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hle)]
  refine hgap.trans ?_
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · simp
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hc : ((T : ℝ) - 1) / (2 * T) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  calc ((T : ℝ) - 1) / (2 * T) * (∑ t, 1 / a t) ^ 2 ≤ 1 / 2 * (∑ t, 1 / a t) ^ 2 :=
        mul_le_mul_of_nonneg_right hc (sq_nonneg _)
    _ = (∑ t, 1 / a t) ^ 2 / 2 := by ring

theorem het_nonneg (N : ℕ) (i : Fin (N + 1)) : 0 ≤ het N i := by
  have hle : (i : ℝ) ≤ N := by exact_mod_cast Nat.le_of_lt_succ i.isLt
  have h1 : (i : ℝ) / N ≤ 1 := div_le_one_of_le₀ hle (Nat.cast_nonneg _)
  have h0 : 0 ≤ (i : ℝ) / N := by positivity
  unfold het
  exact mul_nonneg (mul_nonneg (by norm_num) h0) (sub_nonneg.2 h1)

theorem wfVarExpect_het_le_harmonic (n : ℕ → ℕ) (t : ℕ) (hpos : ∀ s, s < t → 0 < n (s + 1))
    (i : Fin (n 0 + 1)) :
    wfVarExpect n t (fun j => het (n t) j) i ≤
      (1 - 1 / harmonicSize (fun s : Fin t => (n (s + 1) : ℝ))) ^ t * het (n 0) i := by
  rw [wfVarExpect_het n t hpos i,
    ← Fin.prod_univ_eq_prod_range (fun s => 1 - 1 / (n (s + 1) : ℝ)) t]
  refine mul_le_mul_of_nonneg_right ?_ (het_nonneg (n 0) i)
  exact prod_deficit_le_harmonic (fun s : Fin t => (n (s + 1) : ℝ)) fun s => by
    exact_mod_cast hpos s s.isLt

theorem prod_deficit_two_four :
    ∏ t : Fin 2, (1 - 1 / ((![2, 4] : Fin 2 → ℝ) t)) = 3 / 8 := by
  simp [Fin.prod_univ_two]
  norm_num

theorem harmonicSize_two_four : harmonicSize (![2, 4] : Fin 2 → ℝ) = 8 / 3 := by
  unfold harmonicSize
  simp [Fin.sum_univ_two]
  norm_num

theorem harmonic_power_two_four :
    (1 - 1 / harmonicSize (![2, 4] : Fin 2 → ℝ)) ^ 2 = 25 / 64 := by
  rw [harmonicSize_two_four]
  norm_num

theorem prod_deficit_two_four_ne_harmonic :
    ∏ t : Fin 2, (1 - 1 / ((![2, 4] : Fin 2 → ℝ) t)) ≠
      (1 - 1 / harmonicSize (![2, 4] : Fin 2 → ℝ)) ^ 2 := by
  rw [prod_deficit_two_four, harmonic_power_two_four]
  norm_num

end Rhone.MarkovChain
