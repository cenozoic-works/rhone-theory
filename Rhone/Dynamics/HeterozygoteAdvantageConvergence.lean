/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Dynamics.DiploidSelection
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# Global convergence under heterozygote advantage

Source: crow_kimura1970, sec. 6.7, eq. (6.7.2), pp. 270–271. -/

@[expose] public section

namespace Rhone.Dynamics

open Filter Topology

noncomputable def selOrbit (w11 w12 w22 p0 : ℝ) (t : ℕ) : ℝ := (selStep w11 w12 w22)^[t] p0

theorem selOrbit_zero (w11 w12 w22 p0 : ℝ) : selOrbit w11 w12 w22 p0 0 = p0 := rfl

theorem selOrbit_succ (w11 w12 w22 p0 : ℝ) (t : ℕ) :
    selOrbit w11 w12 w22 p0 (t + 1) = selStep w11 w12 w22 (selOrbit w11 w12 w22 p0 t) :=
  Function.iterate_succ_apply' _ _ _

section Basic

variable {w11 w12 w22 : ℝ}

theorem meanFit_pos_Ioo (h11 : 0 ≤ w11) (h22 : 0 ≤ w22) (h12 : 0 < w12) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) : 0 < meanFit w11 w12 w22 p := by
  have hq : 0 < 1 - p := sub_pos.mpr hp1
  unfold meanFit
  positivity

theorem selStep_mem_Ioo (h11 : 0 ≤ w11) (h22 : 0 ≤ w22) (h12 : 0 < w12) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) :
    0 < selStep w11 w12 w22 p ∧ selStep w11 w12 w22 p < 1 := by
  have hq : 0 < 1 - p := sub_pos.mpr hp1
  have hW := meanFit_pos_Ioo h11 h22 h12 hp0 hp1
  unfold selStep
  refine ⟨div_pos ?_ hW, (div_lt_one hW).mpr ?_⟩
  · have : 0 < p * (1 - p) * w12 := by positivity
    nlinarith [mul_nonneg (sq_nonneg p) h11]
  · have h1 : meanFit w11 w12 w22 p - (p ^ 2 * w11 + p * (1 - p) * w12)
        = p * (1 - p) * w12 + (1 - p) ^ 2 * w22 := by
      unfold meanFit; ring
    have : 0 < p * (1 - p) * w12 := by positivity
    nlinarith [mul_nonneg (sq_nonneg (1 - p)) h22]

theorem selOrbit_mem_Ioo (h11 : 0 ≤ w11) (h22 : 0 ≤ w22) (h12 : 0 < w12) {p0 : ℝ}
    (hp0 : 0 < p0) (hp1 : p0 < 1) (t : ℕ) :
    0 < selOrbit w11 w12 w22 p0 t ∧ selOrbit w11 w12 w22 p0 t < 1 := by
  induction t with
  | zero => exact ⟨hp0, hp1⟩
  | succ t ih =>
    rw [selOrbit_succ]
    exact selStep_mem_Ioo h11 h22 h12 ih.1 ih.2

theorem selStepSlope_eq (p : ℝ) (hW : meanFit w11 w12 w22 p ≠ 0) :
    selStepSlope w11 w12 w22 p
      = 1 - p * (1 - p) * (2 * w12 - w11 - w22) / meanFit w11 w12 w22 p := by
  unfold selStepSlope
  have : meanFit w11 w12 w22 p - (p * w11 + (1 - p) * w22)
      = p * (1 - p) * (2 * w12 - w11 - w22) := by unfold meanFit; ring
  field_simp
  linarith

theorem meanFit_le_of_le (h11 : w11 ≤ w12) (h22 : w22 ≤ w12) (p : ℝ) :
    meanFit w11 w12 w22 p ≤ w12 := by
  have : w12 - meanFit w11 w12 w22 p = p ^ 2 * (w12 - w11) + (1 - p) ^ 2 * (w12 - w22) := by
    unfold meanFit; ring
  nlinarith [mul_nonneg (sq_nonneg p) (sub_nonneg.mpr h11),
    mul_nonneg (sq_nonneg (1 - p)) (sub_nonneg.mpr h22)]

theorem selStepSlope_bounds (h11 : 0 ≤ w11) (h22 : 0 ≤ w22) (ho : w11 < w12 ∧ w22 < w12)
    {a b p : ℝ} (ha : 0 < a) (hb : b < 1) (hap : a ≤ p) (hpb : p ≤ b) :
    0 ≤ selStepSlope w11 w12 w22 p ∧
      selStepSlope w11 w12 w22 p ≤ 1 - a * (1 - b) * (2 * w12 - w11 - w22) / w12 := by
  obtain ⟨o1, o2⟩ := ho
  have h12 : 0 < w12 := by linarith
  have hp0 : 0 < p := by linarith
  have hp1 : p < 1 := by linarith
  have hq : 0 < 1 - p := sub_pos.mpr hp1
  have hW := meanFit_pos_Ioo h11 h22 h12 hp0 hp1
  have hD : 0 < 2 * w12 - w11 - w22 := by linarith
  refine ⟨div_nonneg (by positivity) hW.le, ?_⟩
  rw [selStepSlope_eq p hW.ne']
  have hab : a * (1 - b) ≤ p * (1 - p) := by
    have : 1 - b ≤ 1 - p := by linarith
    exact mul_le_mul hap this (by linarith) hp0.le
  have h1 : a * (1 - b) * (2 * w12 - w11 - w22) / w12
      ≤ p * (1 - p) * (2 * w12 - w11 - w22) / w12 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hab hD.le) h12.le
  have h2 : p * (1 - p) * (2 * w12 - w11 - w22) / w12
      ≤ p * (1 - p) * (2 * w12 - w11 - w22) / meanFit w11 w12 w22 p :=
    div_le_div_of_nonneg_left (by positivity) hW (meanFit_le_of_le o1.le o2.le p)
  linarith

theorem selStepSlope_mem_Icc (h11 : 0 ≤ w11) (h22 : 0 ≤ w22) (ho : w11 < w12 ∧ w22 < w12)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    0 ≤ selStepSlope w11 w12 w22 p ∧ selStepSlope w11 w12 w22 p ≤ 1 := by
  obtain ⟨o1, o2⟩ := ho
  have h12 : 0 < w12 := by linarith
  have hq : 0 < 1 - p := sub_pos.mpr hp1
  have hW := meanFit_pos_Ioo h11 h22 h12 hp0 hp1
  have hD : 0 < 2 * w12 - w11 - w22 := by linarith
  refine ⟨div_nonneg (by positivity) hW.le, ?_⟩
  rw [selStepSlope_eq p hW.ne']
  have : 0 ≤ p * (1 - p) * (2 * w12 - w11 - w22) / meanFit w11 w12 w22 p := by positivity
  linarith

end Basic

section Overdominance

variable {w11 w12 w22 p0 : ℝ}

theorem abs_selStep_sub_polyEq_le (h11 : 0 ≤ w11) (h22 : 0 ≤ w22) (ho : w11 < w12 ∧ w22 < w12)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    |selStep w11 w12 w22 p - polyEq w11 w12 w22| ≤ |p - polyEq w11 w12 w22| := by
  have h12 : 0 < w12 := by linarith [ho.1, h11]
  have hD : 2 * w12 - w11 - w22 ≠ 0 := by
    have : 0 < 2 * w12 - w11 - w22 := by linarith [ho.1, ho.2]
    exact this.ne'
  have hW := (meanFit_pos_Ioo h11 h22 h12 hp0 hp1).ne'
  obtain ⟨k0, k1⟩ := selStepSlope_mem_Icc h11 h22 ho hp0 hp1
  rw [selStep_sub_polyEq p hD hW, abs_mul, abs_of_nonneg k0]
  exact mul_le_of_le_one_left (abs_nonneg _) k1

theorem overdominance_orbit_factor (h11 : 0 ≤ w11) (h22 : 0 ≤ w22)
    (ho : w11 < w12 ∧ w22 < w12) (hp0 : 0 < p0) (hp1 : p0 < 1) :
    ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∀ t : ℕ, ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ ≤ c ^ t ∧
      selOrbit w11 w12 w22 p0 t - polyEq w11 w12 w22
        = ρ * (p0 - polyEq w11 w12 w22) := by
  obtain ⟨o1, o2⟩ := ho
  have h12 : 0 < w12 := by linarith
  have hD : 0 < 2 * w12 - w11 - w22 := by linarith
  have hmem := (polyEq_mem_Ioo_iff w11 w12 w22).mpr (Or.inl ⟨o1, o2⟩)
  set ps := polyEq w11 w12 w22 with hps
  set a := min p0 ps with ha
  set b := max p0 ps with hb
  have ha0 : 0 < a := lt_min hp0 hmem.1
  have hb1 : b < 1 := max_lt hp1 hmem.2
  have hab : a ≤ b := (min_le_left _ _).trans (le_max_left _ _)
  set c := 1 - a * (1 - b) * (2 * w12 - w11 - w22) / w12 with hc
  have hpos : 0 < a * (1 - b) * (2 * w12 - w11 - w22) / w12 := by
    have : 0 < 1 - b := sub_pos.mpr hb1
    positivity
  have hcfst := selStepSlope_bounds h11 h22 ⟨o1, o2⟩ ha0 hb1
    (min_le_left p0 ps) (le_max_left p0 ps)
  have hc0 : 0 ≤ c := hcfst.1.trans hcfst.2
  have hc1 : c < 1 := by rw [hc]; linarith
  refine ⟨c, hc0, hc1, fun t => ?_⟩
  induction t with
  | zero => exact ⟨1, zero_le_one, by simp, by simp [selOrbit_zero]⟩
  | succ t ih =>
    obtain ⟨ρ, hρ0, hρc, hρ⟩ := ih
    have hρ1 : ρ ≤ 1 := hρc.trans (pow_le_one₀ hc0 hc1.le)
    have hpt : selOrbit w11 w12 w22 p0 t = ps + ρ * (p0 - ps) := by linarith
    have hlo : a ≤ selOrbit w11 w12 w22 p0 t := by
      rw [hpt]
      have e1 : a ≤ p0 := min_le_left _ _
      have e2 : a ≤ ps := min_le_right _ _
      nlinarith [mul_nonneg (sub_nonneg.mpr hρ1) (sub_nonneg.mpr e2),
        mul_nonneg hρ0 (sub_nonneg.mpr e1)]
    have hhi : selOrbit w11 w12 w22 p0 t ≤ b := by
      rw [hpt]
      have e1 : p0 ≤ b := le_max_left _ _
      have e2 : ps ≤ b := le_max_right _ _
      nlinarith [mul_nonneg (sub_nonneg.mpr hρ1) (sub_nonneg.mpr e2),
        mul_nonneg hρ0 (sub_nonneg.mpr e1)]
    have hbd := selStepSlope_bounds h11 h22 ⟨o1, o2⟩ ha0 hb1 hlo hhi
    have hpm : 0 < selOrbit w11 w12 w22 p0 t ∧ selOrbit w11 w12 w22 p0 t < 1 :=
      ⟨by linarith, by linarith⟩
    have hW := (meanFit_pos_Ioo h11 h22 h12 hpm.1 hpm.2).ne'
    have hD' : 2 * w12 - w11 - w22 ≠ 0 := hD.ne'
    refine ⟨selStepSlope w11 w12 w22 (selOrbit w11 w12 w22 p0 t) * ρ,
      mul_nonneg hbd.1 hρ0, ?_, ?_⟩
    · calc selStepSlope w11 w12 w22 (selOrbit w11 w12 w22 p0 t) * ρ
          ≤ c * c ^ t := mul_le_mul hbd.2 hρc hρ0 hc0
        _ = c ^ (t + 1) := by ring
    · rw [selOrbit_succ, selStep_sub_polyEq _ hD' hW, hρ]
      ring

theorem overdominance_orbit_geometric (h11 : 0 ≤ w11) (h22 : 0 ≤ w22)
    (ho : w11 < w12 ∧ w22 < w12) (hp0 : 0 < p0) (hp1 : p0 < 1) :
    ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∀ t : ℕ,
      |selOrbit w11 w12 w22 p0 t - polyEq w11 w12 w22|
        ≤ c ^ t * |p0 - polyEq w11 w12 w22| := by
  obtain ⟨c, hc0, hc1, h⟩ := overdominance_orbit_factor h11 h22 ho hp0 hp1
  refine ⟨c, hc0, hc1, fun t => ?_⟩
  obtain ⟨ρ, hρ0, hρc, hρ⟩ := h t
  rw [hρ, abs_mul, abs_of_nonneg hρ0]
  exact mul_le_mul_of_nonneg_right hρc (abs_nonneg _)

/-- Source: crow_kimura1970, sec. 6.7, eq. (6.7.2), pp. 270–271; felsenstein_teg2019, sec. II.8, eq.
(II-101)–(II-107), pp. 85–89. -/
theorem overdominance_orbit_monotone (h11 : 0 ≤ w11) (h22 : 0 ≤ w22)
    (ho : w11 < w12 ∧ w22 < w12) (hp0 : 0 < p0) (hp1 : p0 < 1) (t : ℕ) :
    0 ≤ (selOrbit w11 w12 w22 p0 t - polyEq w11 w12 w22) * (p0 - polyEq w11 w12 w22) ∧
      |selOrbit w11 w12 w22 p0 (t + 1) - polyEq w11 w12 w22|
        ≤ |selOrbit w11 w12 w22 p0 t - polyEq w11 w12 w22| := by
  have h12 : 0 < w12 := by linarith [ho.1]
  obtain ⟨c, hc0, hc1, h⟩ := overdominance_orbit_factor h11 h22 ho hp0 hp1
  obtain ⟨ρ, hρ0, hρc, hρ⟩ := h t
  refine ⟨?_, ?_⟩
  · rw [hρ]
    nlinarith [mul_nonneg hρ0 (sq_nonneg (p0 - polyEq w11 w12 w22))]
  · rw [selOrbit_succ]
    have hm := selOrbit_mem_Ioo h11 h22 h12 hp0 hp1 t
    exact abs_selStep_sub_polyEq_le h11 h22 ho hm.1 hm.2

theorem overdominance_orbit_sign_strict (h11 : 0 < w11) (h22 : 0 < w22)
    (ho : w11 < w12 ∧ w22 < w12) (hp0 : 0 < p0) (hp1 : p0 < 1)
    (hne : p0 ≠ polyEq w11 w12 w22) (t : ℕ) :
    0 < (selOrbit w11 w12 w22 p0 t - polyEq w11 w12 w22) * (p0 - polyEq w11 w12 w22) := by
  have h12 : 0 < w12 := by linarith [ho.1]
  have hD : 2 * w12 - w11 - w22 ≠ 0 := by
    have : 0 < 2 * w12 - w11 - w22 := by linarith [ho.1, ho.2]
    exact this.ne'
  induction t with
  | zero =>
    simpa [selOrbit_zero] using mul_self_pos.mpr (sub_ne_zero.mpr hne)
  | succ t ih =>
    have hm := selOrbit_mem_Ioo h11.le h22.le h12 hp0 hp1 t
    have hW := (meanFit_pos_Ioo h11.le h22.le h12 hm.1 hm.2).ne'
    obtain ⟨k0, _⟩ := selStepSlope_mem_Ioo h11 h22 ho hm.1 hm.2
    rw [selOrbit_succ, selStep_sub_polyEq _ hD hW, mul_assoc]
    exact mul_pos k0 ih

/-- Source: crow_kimura1970, sec. 6.7, eq. (6.7.2), pp. 270–271. -/
theorem tendsto_overdominance_orbit (h11 : 0 ≤ w11) (h22 : 0 ≤ w22)
    (ho : w11 < w12 ∧ w22 < w12) (hp0 : 0 < p0) (hp1 : p0 < 1) :
    Tendsto (selOrbit w11 w12 w22 p0) atTop (𝓝 (polyEq w11 w12 w22)) := by
  obtain ⟨c, hc0, hc1, h⟩ := overdominance_orbit_geometric h11 h22 ho hp0 hp1
  rw [tendsto_iff_dist_tendsto_zero]
  have hlim : Tendsto (fun t : ℕ => c ^ t * |p0 - polyEq w11 w12 w22|) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).mul_const
      |p0 - polyEq w11 w12 w22|
  exact squeeze_zero (fun t => dist_nonneg) (fun t => by rw [Real.dist_eq]; exact h t) hlim

theorem polyEq_param {s t : ℝ} :
    polyEq (1 - s) 1 (1 - t) = t / (s + t) := by
  unfold polyEq
  congr 1 <;> ring

theorem tendsto_overdominance_orbit_param {s t : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1)
    (ht0 : 0 < t) (ht1 : t ≤ 1) (hp0 : 0 < p0) (hp1 : p0 < 1) :
    Tendsto (selOrbit (1 - s) 1 (1 - t) p0) atTop (𝓝 (t / (s + t))) := by
  rw [← polyEq_param]
  exact tendsto_overdominance_orbit (by linarith) (by linarith)
    ⟨by linarith, by linarith⟩ hp0 hp1

end Overdominance

section Underdominance

variable {w11 w12 w22 p0 : ℝ}

/-- Source: crow_kimura1970, sec. 6.7, eq. (6.7.2), pp. 270–271. -/
theorem underdominance_orbit_repelling (h12 : 0 < w12) (hu : w12 < w11 ∧ w12 < w22)
    (hp0 : 0 < p0) (hp1 : p0 < 1) (hne : p0 ≠ polyEq w11 w12 w22) (t : ℕ) :
    0 < (selOrbit w11 w12 w22 p0 t - polyEq w11 w12 w22) * (p0 - polyEq w11 w12 w22) ∧
      |selOrbit w11 w12 w22 p0 t - polyEq w11 w12 w22|
        < |selOrbit w11 w12 w22 p0 (t + 1) - polyEq w11 w12 w22| := by
  obtain ⟨u1, u2⟩ := hu
  have h11 : 0 ≤ w11 := by linarith
  have h22 : 0 ≤ w22 := by linarith
  have hD : 2 * w12 - w11 - w22 ≠ 0 := by
    have : 2 * w12 - w11 - w22 < 0 := by linarith
    exact this.ne
  have hDneg : 2 * w12 - w11 - w22 < 0 := by linarith
  have hslope : ∀ p : ℝ, 0 < p → p < 1 → 1 < selStepSlope w11 w12 w22 p := by
    intro p hp0 hp1
    have hq : 0 < 1 - p := sub_pos.mpr hp1
    have hW := meanFit_pos_Ioo h11 h22 h12 hp0 hp1
    rw [selStepSlope_eq p hW.ne']
    have : p * (1 - p) * (2 * w12 - w11 - w22) / meanFit w11 w12 w22 p < 0 :=
      div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by positivity) hDneg) hW
    linarith
  have hsign : ∀ n : ℕ,
      0 < (selOrbit w11 w12 w22 p0 n - polyEq w11 w12 w22) * (p0 - polyEq w11 w12 w22) := by
    intro n
    induction n with
    | zero => simpa [selOrbit_zero] using mul_self_pos.mpr (sub_ne_zero.mpr hne)
    | succ n ih =>
      have hm := selOrbit_mem_Ioo h11 h22 h12 hp0 hp1 n
      have hW := (meanFit_pos_Ioo h11 h22 h12 hm.1 hm.2).ne'
      have k1 := hslope _ hm.1 hm.2
      rw [selOrbit_succ, selStep_sub_polyEq _ hD hW, mul_assoc]
      exact mul_pos (by linarith) ih
  refine ⟨hsign t, ?_⟩
  have hm := selOrbit_mem_Ioo h11 h22 h12 hp0 hp1 t
  have hW := (meanFit_pos_Ioo h11 h22 h12 hm.1 hm.2).ne'
  have k1 := hslope _ hm.1 hm.2
  have hne' : selOrbit w11 w12 w22 p0 t - polyEq w11 w12 w22 ≠ 0 := by
    intro h
    have := hsign t
    rw [h, zero_mul] at this
    exact lt_irrefl _ this
  have hd : 0 < |selOrbit w11 w12 w22 p0 t - polyEq w11 w12 w22| := abs_pos.mpr hne'
  rw [selOrbit_succ, selStep_sub_polyEq _ hD hW, abs_mul, abs_of_pos (lt_trans zero_lt_one k1)]
  nlinarith

theorem underdominance_orbit_not_tendsto (h12 : 0 < w12) (hu : w12 < w11 ∧ w12 < w22)
    (hp0 : 0 < p0) (hp1 : p0 < 1) (hne : p0 ≠ polyEq w11 w12 w22) :
    ¬ Tendsto (selOrbit w11 w12 w22 p0) atTop (𝓝 (polyEq w11 w12 w22)) := by
  intro hT
  have hmono : Monotone (fun t => |selOrbit w11 w12 w22 p0 t - polyEq w11 w12 w22|) :=
    monotone_nat_of_le_succ fun t =>
      (underdominance_orbit_repelling h12 hu hp0 hp1 hne t).2.le
  have hd : 0 < |p0 - polyEq w11 w12 w22| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hev := (tendsto_iff_dist_tendsto_zero.mp hT).eventually (gt_mem_nhds hd)
  obtain ⟨t, ht⟩ := hev.exists
  have := hmono (Nat.zero_le t)
  rw [Real.dist_eq] at ht
  simp only [selOrbit_zero] at this
  linarith

end Underdominance

end Rhone.Dynamics
