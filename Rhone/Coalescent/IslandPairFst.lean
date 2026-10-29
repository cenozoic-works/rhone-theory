/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.IslandPairExpected
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Coalescence-time F_ST for the labelled symmetric island pair

Source: slatkin1991, pp. 169–170, eq. (8), (11)–(14). -/

@[expose] public section
namespace Rhone.Coalescent.IslandPairFst
open Finset IslandPair

/-- Source: slatkin1991, p. 169, eq. (8). -/
noncomputable def fstFromTimes (tWithin tTotal : ℝ) : ℝ := (tTotal - tWithin) / tTotal

noncomputable def randomDemesTime (d : ℕ) (m c : ℝ) (hm : 0 ≤ m) (hc : 0 ≤ c) : ℝ :=
  (1 / (d : ℝ) ^ 2) *
    ∑ a : Fin d, ∑ b : Fin d, (chain d m c hm hc).expectedTime {none} (some (a, b))

noncomputable def fstBetween (d : ℕ) (m c : ℝ) : ℝ :=
  ((d : ℝ) - 1) * c / (2 * m * d + ((d : ℝ) - 1) * c)

noncomputable def fstRandom (d : ℕ) (m c : ℝ) : ℝ :=
  ((d : ℝ) - 1) ^ 2 * c / (2 * m * (d : ℝ) ^ 2 + ((d : ℝ) - 1) ^ 2 * c)

theorem sum_meanTime (d : ℕ) (m c : ℝ) :
    ∑ a : Fin d, ∑ b : Fin d, meanTime d m c (some (a, b)) =
      d * (sameTime d c + ((d : ℝ) - 1) * differentTime d m c) := by
  have h : ∀ a b : Fin d, meanTime d m c (some (a, b)) =
      differentTime d m c + if a = b then sameTime d c - differentTime d m c else 0 := by
    intro a b
    by_cases hab : a = b <;> simp [meanTime, hab]
  simp only [h, sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    sum_ite_eq, mem_univ, ↓reduceIte]
  ring

private theorem cast_pred (d : ℕ) (hd : 2 ≤ d) : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 :=
  Nat.cast_pred (by omega)

theorem randomDemesTime_eq_mixture (d : ℕ) (hd : 2 ≤ d) (m c : ℝ) (hm : 0 < m) (hc : 0 < c)
    (a b : Fin d) (hab : a ≠ b) :
    randomDemesTime d m c hm.le hc.le =
      (1 / (d : ℝ)) * (chain d m c hm.le hc.le).expectedTime {none} (some (a, a)) +
        (((d : ℝ) - 1) / d) * (chain d m c hm.le hc.le).expectedTime {none} (some (a, b)) := by
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold randomDemesTime
  rw [← meanTime_eq_expectedTime d hd m c hm hc, sum_meanTime]
  simp only [meanTime, hab, ↓reduceIte]
  field_simp

theorem randomDemesTime_eq (d : ℕ) (hd : 2 ≤ d) (m c : ℝ) (hm : 0 < m) (hc : 0 < c) :
    randomDemesTime d m c hm.le hc.le = d / c + ((d : ℝ) - 1) ^ 2 / (2 * m * d) := by
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold randomDemesTime
  rw [← meanTime_eq_expectedTime d hd m c hm hc, sum_meanTime]
  simp only [sameTime, differentTime, cast_pred d hd]
  field_simp
  ring

private theorem between_den_pos (d : ℕ) (hd : 2 ≤ d) (m c : ℝ) (hm : 0 < m) (hc : 0 < c) :
    0 < 2 * m * d + ((d : ℝ) - 1) * c := by
  have h2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : 0 < (d : ℝ) - 1 := by linarith
  have h0 : 0 < (d : ℝ) := by linarith
  positivity

private theorem random_den_pos (d : ℕ) (hd : 2 ≤ d) (m c : ℝ) (hm : 0 < m) (hc : 0 < c) :
    0 < 2 * m * (d : ℝ) ^ 2 + ((d : ℝ) - 1) ^ 2 * c := by
  have h2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : 0 < (d : ℝ) - 1 := by linarith
  have h0 : 0 < (d : ℝ) := by linarith
  positivity

theorem fstBetween_eq_delay_ratio (d : ℕ) (hd : 2 ≤ d) (m c : ℝ) (hm : 0 < m) (hc : 0 < c) :
    fstBetween d m c = (((d : ℝ) - 1) / (2 * m)) / (d / c + ((d : ℝ) - 1) / (2 * m)) := by
  have hden := between_den_pos d hd m c hm hc
  have hsum : (d : ℝ) / c + ((d : ℝ) - 1) / (2 * m) =
      (2 * m * d + ((d : ℝ) - 1) * c) / (2 * m * c) := by
    field_simp
  rw [hsum]
  unfold fstBetween
  field_simp

theorem fstRandom_eq_delay_ratio (d : ℕ) (hd : 2 ≤ d) (m c : ℝ) (hm : 0 < m) (hc : 0 < c) :
    fstRandom d m c =
      (((d : ℝ) - 1) ^ 2 / (2 * m * d)) / (d / c + ((d : ℝ) - 1) ^ 2 / (2 * m * d)) := by
  have hden := random_den_pos d hd m c hm hc
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hsum : (d : ℝ) / c + ((d : ℝ) - 1) ^ 2 / (2 * m * d) =
      (2 * m * (d : ℝ) ^ 2 + ((d : ℝ) - 1) ^ 2 * c) / (2 * m * d * c) := by
    field_simp
  rw [hsum]
  unfold fstRandom
  field_simp

theorem fstFromTimes_between (d : ℕ) (hd : 2 ≤ d) (m c : ℝ) (hm : 0 < m) (hc : 0 < c)
    (a b b' : Fin d) (hbb : b ≠ b') :
    fstFromTimes ((chain d m c hm.le hc.le).expectedTime {none} (some (a, a)))
      ((chain d m c hm.le hc.le).expectedTime {none} (some (b, b'))) = fstBetween d m c := by
  rw [expectedTime_same d hd m c hm hc a, expectedTime_different d hd m c hm hc b b' hbb,
    cast_pred d hd, fstBetween_eq_delay_ratio d hd m c hm hc]
  unfold fstFromTimes
  congr 1
  ring

theorem fstFromTimes_random (d : ℕ) (hd : 2 ≤ d) (m c : ℝ) (hm : 0 < m) (hc : 0 < c)
    (a : Fin d) :
    fstFromTimes ((chain d m c hm.le hc.le).expectedTime {none} (some (a, a)))
      (randomDemesTime d m c hm.le hc.le) = fstRandom d m c := by
  rw [expectedTime_same d hd m c hm hc a, randomDemesTime_eq d hd m c hm hc,
    fstRandom_eq_delay_ratio d hd m c hm hc]
  unfold fstFromTimes
  congr 1
  ring

theorem fstBetween_diploid (d : ℕ) (hd : 2 ≤ d) (m N : ℝ) (hm : 0 < m) (hN : 0 < N) :
    fstBetween d m (1 / (2 * N)) = 1 / (1 + 4 * N * m * ((d : ℝ) / ((d : ℝ) - 1))) := by
  have h2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : 0 < (d : ℝ) - 1 := by linarith
  have h0 : 0 < (d : ℝ) := by linarith
  have hc : 0 < 1 / (2 * N) := by positivity
  have hden := between_den_pos d hd m (1 / (2 * N)) hm hc
  have hden' : 0 < 1 + 4 * N * m * ((d : ℝ) / ((d : ℝ) - 1)) := by positivity
  unfold fstBetween
  rw [div_eq_div_iff hden.ne' hden'.ne']
  field_simp
  ring

theorem fstRandom_diploid (d : ℕ) (hd : 2 ≤ d) (m N : ℝ) (hm : 0 < m) (hN : 0 < N) :
    fstRandom d m (1 / (2 * N)) =
      1 / (1 + 4 * N * m * ((d : ℝ) ^ 2 / ((d : ℝ) - 1) ^ 2)) := by
  have h2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : 0 < (d : ℝ) - 1 := by linarith
  have h0 : 0 < (d : ℝ) := by linarith
  have hc : 0 < 1 / (2 * N) := by positivity
  have hden := random_den_pos d hd m (1 / (2 * N)) hm hc
  have hden' : 0 < 1 + 4 * N * m * ((d : ℝ) ^ 2 / ((d : ℝ) - 1) ^ 2) := by positivity
  unfold fstRandom
  rw [div_eq_div_iff hden.ne' hden'.ne']
  field_simp
  ring

theorem fstBetween_two (m c : ℝ) : fstBetween 2 m c = c / (4 * m + c) := by
  unfold fstBetween
  norm_num
  ring_nf

theorem fstRandom_two (m c : ℝ) : fstRandom 2 m c = c / (8 * m + c) := by
  unfold fstRandom
  norm_num
  ring_nf

theorem fstBetween_pos (d : ℕ) (hd : 2 ≤ d) (m c : ℝ) (hm : 0 < m) (hc : 0 < c) :
    0 < fstBetween d m c := by
  have h2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : 0 < (d : ℝ) - 1 := by linarith
  exact div_pos (mul_pos h1 hc) (between_den_pos d hd m c hm hc)

theorem fstBetween_lt_one (d : ℕ) (hd : 2 ≤ d) (m c : ℝ) (hm : 0 < m) (hc : 0 < c) :
    fstBetween d m c < 1 := by
  have h2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have h0 : 0 < (d : ℝ) := by linarith
  unfold fstBetween
  rw [div_lt_one (between_den_pos d hd m c hm hc)]
  have : 0 < 2 * m * d := by positivity
  linarith

theorem fstRandom_pos (d : ℕ) (hd : 2 ≤ d) (m c : ℝ) (hm : 0 < m) (hc : 0 < c) :
    0 < fstRandom d m c := by
  have h2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : 0 < (d : ℝ) - 1 := by linarith
  exact div_pos (by positivity) (random_den_pos d hd m c hm hc)

theorem fstRandom_lt_fstBetween (d : ℕ) (hd : 2 ≤ d) (m c : ℝ) (hm : 0 < m) (hc : 0 < c) :
    fstRandom d m c < fstBetween d m c := by
  have h2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : 0 < (d : ℝ) - 1 := by linarith
  have h0 : 0 < (d : ℝ) := by linarith
  unfold fstRandom fstBetween
  rw [div_lt_div_iff₀ (random_den_pos d hd m c hm hc) (between_den_pos d hd m c hm hc)]
  have hk : 0 < 2 * m * d * c * ((d : ℝ) - 1) := by positivity
  nlinarith [hk]

open Filter Topology

theorem fstBetween_strictAntiOn (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c) :
    StrictAntiOn (fun m : ℝ => fstBetween d m c) (Set.Ioi 0) := by
  intro m₁ h₁ m₂ h₂ h
  have h2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : 0 < (d : ℝ) - 1 := by linarith
  have h0 : 0 < (d : ℝ) := by linarith
  have hk : 0 < ((d : ℝ) - 1) * c := mul_pos h1 hc
  have hlt : m₁ * d < m₂ * d := mul_lt_mul_of_pos_right h h0
  change fstBetween d m₂ c < fstBetween d m₁ c
  unfold fstBetween
  rw [div_lt_div_iff₀ (between_den_pos d hd m₂ c h₂ hc) (between_den_pos d hd m₁ c h₁ hc)]
  nlinarith [mul_pos hk (sub_pos.mpr hlt)]

theorem fstRandom_strictAntiOn (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c) :
    StrictAntiOn (fun m : ℝ => fstRandom d m c) (Set.Ioi 0) := by
  intro m₁ h₁ m₂ h₂ h
  have h2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : 0 < (d : ℝ) - 1 := by linarith
  have h0 : 0 < (d : ℝ) := by linarith
  have hk : 0 < ((d : ℝ) - 1) ^ 2 * c := by positivity
  have hlt : m₁ * (d : ℝ) ^ 2 < m₂ * (d : ℝ) ^ 2 := mul_lt_mul_of_pos_right h (by positivity)
  change fstRandom d m₂ c < fstRandom d m₁ c
  unfold fstRandom
  rw [div_lt_div_iff₀ (random_den_pos d hd m₂ c h₂ hc) (random_den_pos d hd m₁ c h₁ hc)]
  nlinarith [mul_pos hk (sub_pos.mpr hlt)]

theorem tendsto_fstBetween_zero_right (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c) :
    Tendsto (fun m : ℝ => fstBetween d m c) (𝓝[>] 0) (𝓝 1) := by
  have h2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hk : ((d : ℝ) - 1) * c ≠ 0 := (mul_pos (by linarith) hc).ne'
  have hcont : ContinuousAt (fun m : ℝ => fstBetween d m c) 0 := by
    unfold fstBetween
    exact ContinuousAt.div continuousAt_const (by fun_prop) (by simpa using hk)
  have hval : fstBetween d 0 c = 1 := by
    unfold fstBetween
    simp only [mul_zero, zero_mul, zero_add]
    exact div_self hk
  have h := hcont.tendsto
  rw [hval] at h
  exact tendsto_nhdsWithin_of_tendsto_nhds h

theorem tendsto_fstRandom_zero_right (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c) :
    Tendsto (fun m : ℝ => fstRandom d m c) (𝓝[>] 0) (𝓝 1) := by
  have h2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : 0 < (d : ℝ) - 1 := by linarith
  have hk : ((d : ℝ) - 1) ^ 2 * c ≠ 0 := by positivity
  have hcont : ContinuousAt (fun m : ℝ => fstRandom d m c) 0 := by
    unfold fstRandom
    exact ContinuousAt.div continuousAt_const (by fun_prop) (by simpa using hk)
  have hval : fstRandom d 0 c = 1 := by
    unfold fstRandom
    simp only [mul_zero, zero_mul, zero_add]
    exact div_self hk
  have h := hcont.tendsto
  rw [hval] at h
  exact tendsto_nhdsWithin_of_tendsto_nhds h

theorem tendsto_fstBetween_atTop (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (_hc : 0 < c) :
    Tendsto (fun m : ℝ => fstBetween d m c) atTop (𝓝 0) := by
  have h2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have h0 : 0 < (d : ℝ) := by linarith
  have hden : Tendsto (fun m : ℝ => 2 * m * d + ((d : ℝ) - 1) * c) atTop atTop :=
    tendsto_atTop_add_const_right _ _
      ((tendsto_id.const_mul_atTop (two_pos (α := ℝ))).atTop_mul_const h0)
  exact tendsto_const_nhds.div_atTop hden

theorem tendsto_fstRandom_atTop (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (_hc : 0 < c) :
    Tendsto (fun m : ℝ => fstRandom d m c) atTop (𝓝 0) := by
  have h2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have h0 : 0 < (d : ℝ) ^ 2 := by positivity
  have hden : Tendsto (fun m : ℝ => 2 * m * (d : ℝ) ^ 2 + ((d : ℝ) - 1) ^ 2 * c)
      atTop atTop :=
    tendsto_atTop_add_const_right _ _
      ((tendsto_id.const_mul_atTop (two_pos (α := ℝ))).atTop_mul_const h0)
  exact tendsto_const_nhds.div_atTop hden

theorem tendsto_fstBetween_demes (m c : ℝ) (hm : 0 < m) (hc : 0 < c) :
    Tendsto (fun d : ℕ => fstBetween d m c) atTop (𝓝 (c / (2 * m + c))) := by
  have hinv : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hnum : Tendsto (fun n : ℕ => (1 - 1 / (n : ℝ)) * c) atTop (𝓝 c) := by
    simpa using (hinv.const_sub 1).mul_const c
  have hden : Tendsto (fun n : ℕ => 2 * m + (1 - 1 / (n : ℝ)) * c) atTop
      (𝓝 (2 * m + c)) := hnum.const_add _
  have hlim := hnum.div hden (by positivity : (2 * m + c) ≠ 0)
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hrew : (1 - 1 / (n : ℝ)) = ((n : ℝ) - 1) / n := by field_simp
  have hd1 : 0 < 2 * m * n + ((n : ℝ) - 1) * c := by
    have : 0 ≤ ((n : ℝ) - 1) * c := mul_nonneg (by linarith) hc.le
    have : 0 < 2 * m * n := by positivity
    linarith
  have hd2 : 2 * m + ((n : ℝ) - 1) / n * c = (2 * m * n + ((n : ℝ) - 1) * c) / n := by
    field_simp
  change (1 - 1 / (n : ℝ)) * c / (2 * m + (1 - 1 / (n : ℝ)) * c) = fstBetween n m c
  unfold fstBetween
  rw [hrew, hd2]
  field_simp

theorem tendsto_fstRandom_demes (m c : ℝ) (hm : 0 < m) (hc : 0 < c) :
    Tendsto (fun d : ℕ => fstRandom d m c) atTop (𝓝 (c / (2 * m + c))) := by
  have hinv : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hnum : Tendsto (fun n : ℕ => (1 - 1 / (n : ℝ)) ^ 2 * c) atTop (𝓝 c) := by
    simpa using ((hinv.const_sub 1).pow 2).mul_const c
  have hden : Tendsto (fun n : ℕ => 2 * m + (1 - 1 / (n : ℝ)) ^ 2 * c) atTop
      (𝓝 (2 * m + c)) := hnum.const_add _
  have hlim := hnum.div hden (by positivity : (2 * m + c) ≠ 0)
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hrew : (1 - 1 / (n : ℝ)) = ((n : ℝ) - 1) / n := by field_simp
  have hd1 : 0 < 2 * m * (n : ℝ) ^ 2 + ((n : ℝ) - 1) ^ 2 * c := by
    have : 0 ≤ ((n : ℝ) - 1) ^ 2 * c := by positivity
    have : 0 < 2 * m * (n : ℝ) ^ 2 := by positivity
    linarith
  have hd2 : 2 * m + (((n : ℝ) - 1) / n) ^ 2 * c =
      (2 * m * (n : ℝ) ^ 2 + ((n : ℝ) - 1) ^ 2 * c) / (n : ℝ) ^ 2 := by
    field_simp
  change (1 - 1 / (n : ℝ)) ^ 2 * c / (2 * m + (1 - 1 / (n : ℝ)) ^ 2 * c) = fstRandom n m c
  unfold fstRandom
  rw [hrew, hd2]
  field_simp

private theorem diploid_limit_value (m N : ℝ) (hm : 0 < m) (hN : 0 < N) :
    1 / (2 * N) / (2 * m + 1 / (2 * N)) = 1 / (1 + 4 * N * m) := by
  have h1 : 0 < 2 * m + 1 / (2 * N) := by positivity
  have h2 : 0 < 1 + 4 * N * m := by positivity
  rw [div_eq_div_iff h1.ne' h2.ne']
  field_simp
  ring

theorem tendsto_fstBetween_demes_diploid (m N : ℝ) (hm : 0 < m) (hN : 0 < N) :
    Tendsto (fun d : ℕ => fstBetween d m (1 / (2 * N))) atTop
      (𝓝 (1 / (1 + 4 * N * m))) := by
  rw [← diploid_limit_value m N hm hN]
  exact tendsto_fstBetween_demes m (1 / (2 * N)) hm (by positivity)

theorem tendsto_fstRandom_demes_diploid (m N : ℝ) (hm : 0 < m) (hN : 0 < N) :
    Tendsto (fun d : ℕ => fstRandom d m (1 / (2 * N))) atTop
      (𝓝 (1 / (1 + 4 * N * m))) := by
  rw [← diploid_limit_value m N hm hN]
  exact tendsto_fstRandom_demes m (1 / (2 * N)) hm (by positivity)

end Rhone.Coalescent.IslandPairFst
