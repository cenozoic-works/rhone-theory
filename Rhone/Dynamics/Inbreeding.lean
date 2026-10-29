/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # Exact partial-selfing recurrence -/

@[expose] public section

namespace Rhone.Dynamics.Inbreeding

noncomputable def partialSelfingStep (s F : ℝ) : ℝ := s * (1 + F) / 2

noncomputable def partialSelfingFixed (s : ℝ) : ℝ := s / (2 - s)

theorem partial_selfing_fixed {s : ℝ} (hD : 2 - s ≠ 0) :
    partialSelfingStep s (partialSelfingFixed s) = partialSelfingFixed s := by
  unfold partialSelfingStep partialSelfingFixed
  field_simp
  ring

theorem partial_selfing_iterate {s : ℝ} (hD : 2 - s ≠ 0)
    (F0 : ℝ) (t : ℕ) :
    ((partialSelfingStep s)^[t]) F0 = partialSelfingFixed s +
      (s / 2)^t * (F0 - partialSelfingFixed s) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih]
    have hfix := partial_selfing_fixed hD
    unfold partialSelfingStep at hfix ⊢
    rw [pow_succ]
    nlinarith [hfix]

theorem partial_selfing_mem_Icc {s F : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hF0 : 0 ≤ F) (hF1 : F ≤ 1) :
    0 ≤ partialSelfingStep s F ∧ partialSelfingStep s F ≤ 1 := by
  unfold partialSelfingStep
  constructor
  · positivity
  · have hprod : 0 ≤ (1 - s) * (1 + F) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [hprod]

theorem tendsto_partial_selfing {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (F0 : ℝ) :
    Filter.Tendsto (fun t : ℕ => ((partialSelfingStep s)^[t]) F0)
      Filter.atTop (nhds (partialSelfingFixed s)) := by
  have hD : 2 - s ≠ 0 := by linarith
  have hq0 : 0 ≤ s / 2 := by positivity
  have hq1 : s / 2 < 1 := by linarith
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have hlim := (hpow.mul_const (F0 - partialSelfingFixed s)).const_add
    (partialSelfingFixed s)
  simpa only [zero_mul, add_zero, ← partial_selfing_iterate hD F0] using hlim

/-- Source: wright1931, p. 110. -/
theorem selfing_iterate (F0 : ℝ) (t : ℕ) :
    ((partialSelfingStep 1)^[t]) F0 = 1 - (1-F0) / (2:ℝ)^t := by
  rw [partial_selfing_iterate (by norm_num : (2:ℝ) - 1 ≠ 0)]
  norm_num [partialSelfingFixed, div_pow]
  ring

/-- Source: wright1931, p. 110. -/
theorem tendsto_selfing (F0 : ℝ) :
    Filter.Tendsto (fun t : ℕ => ((partialSelfingStep 1)^[t]) F0)
      Filter.atTop (nhds (1:ℝ)) := by
  simpa only [partialSelfingFixed, sub_self, show (2:ℝ) - 1 = 1 by norm_num, div_one]
    using tendsto_partial_selfing (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (1:ℝ) ≤ 1) F0

/-- Source: wright1931, pp. 108–109. -/
noncomputable def fullSibStep (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.2, (1 + 2 * z.2 + z.1) / 4)

theorem full_sib_fixed : fullSibStep (1, 1) = (1, 1) := by
  norm_num [fullSibStep]

theorem full_sib_fixed_iff (z : ℝ × ℝ) : fullSibStep z = z ↔ z = (1, 1) := by
  constructor
  · intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    change z.2 = z.1 at h1
    change (1 + 2 * z.2 + z.1) / 4 = z.2 at h2
    apply Prod.ext <;> change _ = 1 <;> linarith
  · rintro rfl
    exact full_sib_fixed

theorem full_sib_mem_Icc (z : ℝ × ℝ)
    (h10 : 0 ≤ z.1) (h11 : z.1 ≤ 1) (h20 : 0 ≤ z.2) (h21 : z.2 ≤ 1) :
    0 ≤ (fullSibStep z).1 ∧ (fullSibStep z).1 ≤ 1 ∧
      0 ≤ (fullSibStep z).2 ∧ (fullSibStep z).2 ≤ 1 := by
  change 0 ≤ z.2 ∧ z.2 ≤ 1 ∧ 0 ≤ (1 + 2 * z.2 + z.1) / 4 ∧
    (1 + 2 * z.2 + z.1) / 4 ≤ 1
  exact ⟨h20, h21, by linarith, by linarith⟩

/-- Source: wright1931, pp. 108–109. -/
theorem full_sib_deficit_recursion (z : ℝ × ℝ) :
    1 - (fullSibStep z).2 = (1 - z.2) / 2 + (1 - z.1) / 4 := by
  unfold fullSibStep
  ring

/-- Source: wright1931, pp. 108–109. -/
theorem full_sib_from_unrelated_two : ((fullSibStep^[1]) (0, 0)).2 = 1 / 4 := by
  norm_num [fullSibStep]

/-- Source: wright1931, pp. 108–109. -/
theorem full_sib_from_unrelated_three : ((fullSibStep^[2]) (0, 0)).2 = 3 / 8 := by
  norm_num [Function.iterate_succ_apply', fullSibStep]

private noncomputable def sibError (z : ℝ × ℝ) : ℝ := |1 - z.1| + 2 * |1 - z.2|

private theorem sibError_step (z : ℝ × ℝ) : sibError (fullSibStep z) ≤ sibError z := by
  have h := abs_add_le ((1 - z.2) / 2) ((1 - z.1) / 4)
  rw [abs_div, abs_div] at h
  norm_num at h
  have he := full_sib_deficit_recursion z
  unfold sibError
  change |1 - z.2| + 2 * |1 - (fullSibStep z).2| ≤ _
  rw [he]
  linarith [abs_nonneg (1 - z.1)]

private theorem sibError_two_steps (z : ℝ × ℝ) :
    sibError (fullSibStep (fullSibStep z)) ≤ (3 / 4 : ℝ) * sibError z := by
  have hfirst : 1 - (fullSibStep (fullSibStep z)).1 =
      (1 - z.1) / 4 + (1 - z.2) / 2 := by simp [fullSibStep]; ring
  have hsecond : 1 - (fullSibStep (fullSibStep z)).2 =
      (1 - z.1) / 8 + (1 - z.2) / 2 := by simp [fullSibStep]; ring
  have h1 := abs_add_le ((1 - z.1) / 4) ((1 - z.2) / 2)
  have h2 := abs_add_le ((1 - z.1) / 8) ((1 - z.2) / 2)
  rw [abs_div, abs_div] at h1 h2
  norm_num at h1 h2
  unfold sibError
  rw [hfirst, hsecond]
  linarith [abs_nonneg (1 - z.1)]

private theorem sibError_iterate (z : ℝ × ℝ) (t : ℕ) :
    sibError ((fullSibStep^[t]) z) ≤ (3 / 4 : ℝ) ^ (t / 2) * sibError z := by
  induction t using Nat.twoStepInduction with
  | zero => simp
  | one => simpa using sibError_step z
  | more t ih _ =>
    have ht : (t + 2) / 2 = t / 2 + 1 := by omega
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ht, pow_succ]
    calc
      sibError (fullSibStep (fullSibStep ((fullSibStep^[t]) z))) ≤
          (3 / 4 : ℝ) * sibError ((fullSibStep^[t]) z) := sibError_two_steps _
      _ ≤ (3 / 4 : ℝ) * ((3 / 4 : ℝ) ^ (t / 2) * sibError z) := by
        exact mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = _ := by ring

/-- Source: wright1931, pp. 108–109. -/
theorem tendsto_full_sib (z : ℝ × ℝ) :
    Filter.Tendsto (fun t : ℕ => (fullSibStep^[t]) z)
      Filter.atTop (nhds ((1, 1) : ℝ × ℝ)) := by
  have hdiv : Filter.Tendsto (fun t : ℕ => t / 2) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 fun b => ?_
    filter_upwards [Filter.eventually_ge_atTop (2 * b)] with t ht
    omega
  have hupper := ((tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 3 / 4) (by norm_num : (3 / 4 : ℝ) < 1)).comp hdiv).mul_const
      (sibError z)
  simp only [zero_mul] at hupper
  have herr : Filter.Tendsto (fun t : ℕ => sibError ((fullSibStep^[t]) z))
      Filter.atTop (nhds (0 : ℝ)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun _ => by unfold sibError; positivity) (sibError_iterate z)
  have h1 : Filter.Tendsto (fun t : ℕ => ((fullSibStep^[t]) z).1)
      Filter.atTop (nhds (1 : ℝ)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.2
    simp only [Real.norm_eq_abs]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds herr
      (fun _ => abs_nonneg _) (fun t => by
        unfold sibError
        rw [abs_sub_comm (((fullSibStep^[t]) z).1) 1]
        linarith [abs_nonneg (1 - ((fullSibStep^[t]) z).2)])
  have h2 : Filter.Tendsto (fun t : ℕ => ((fullSibStep^[t]) z).2)
      Filter.atTop (nhds (1 : ℝ)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.2
    simp only [Real.norm_eq_abs]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds herr
      (fun _ => abs_nonneg _) (fun t => by
        unfold sibError
        rw [abs_sub_comm (((fullSibStep^[t]) z).2) 1]
        have ha := abs_nonneg (1 - ((fullSibStep^[t]) z).1)
        have hb := abs_nonneg (1 - ((fullSibStep^[t]) z).2)
        linarith)
  exact h1.prodMk_nhds h2

end Rhone.Dynamics.Inbreeding
