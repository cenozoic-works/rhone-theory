/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.FullARGTwoSampleCounts
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.IntervalCases

/-!
# Two-locus outcome function and carrier-count changes at coalescence and split steps

Source: wilton_carmi_hobolth2015, eq. (5), Figure S1. -/
@[expose] public section

namespace Rhone.Coalescent.IntervalProcess
open SmcSupport MeasureTheory

noncomputable def twoLocusValue (ρ : ℝ) : ℕ → ℝ
  | 0 => 4 / (ρ ^ 2 + 13 * ρ + 18)
  | 1 => 6 / (ρ ^ 2 + 13 * ρ + 18)
  | 2 => (ρ + 18) / (ρ ^ 2 + 13 * ρ + 18)
  | _ => 0

noncomputable def twoLocusOutcome (ρ : ℝ) (cx cy cb : ℕ) : ℝ :=
  if cx = 2 ∧ cy = 2 then twoLocusValue ρ cb else if cx ≤ 1 ∧ cy ≤ 1 then 1 else 0

noncomputable def pairOutcome (ρ : ℝ) (cb : ℕ) (t t' : Bool × Bool) : ℝ :=
  twoLocusOutcome ρ (2 - (t.1 && t'.1).toNat) (2 - (t.2 && t'.2).toNat)
      (cb + ((t.1 || t'.1) && (t.2 || t'.2)).toNat - (t.1 && t.2).toNat -
        (t'.1 && t'.2).toNat) -
    twoLocusValue ρ cb

theorem twoLocusValue_nonneg (ρ : ℝ) (hρ : 0 ≤ ρ) (n : ℕ) : 0 ≤ twoLocusValue ρ n := by
  have hD : 0 < ρ ^ 2 + 13 * ρ + 18 := by positivity
  match n with
  | 0 => exact div_nonneg (by norm_num) hD.le
  | 1 => exact div_nonneg (by norm_num) hD.le
  | 2 => exact div_nonneg (by linarith) hD.le
  | _ + 3 => exact le_rfl

theorem twoLocusValue_le_one (ρ : ℝ) (hρ : 0 ≤ ρ) (n : ℕ) : twoLocusValue ρ n ≤ 1 := by
  have hD : 0 < ρ ^ 2 + 13 * ρ + 18 := by positivity
  match n with
  | 0 => exact (div_le_one hD).mpr (by nlinarith)
  | 1 => exact (div_le_one hD).mpr (by nlinarith)
  | 2 => exact (div_le_one hD).mpr (by nlinarith)
  | _ + 3 => exact zero_le_one

theorem pairOutcome_symm (ρ : ℝ) (cb : ℕ) (t t' : Bool × Bool) :
    pairOutcome ρ cb t t' = pairOutcome ρ cb t' t := by
  unfold pairOutcome
  rw [Bool.and_comm t.1 t'.1, Bool.and_comm t.2 t'.2, Bool.or_comm t.1 t'.1,
    Bool.or_comm t.2 t'.2]
  congr 2
  omega

theorem pairOutcome_sum_value (ρ : ℝ) (hρ : 0 ≤ ρ) (cb : ℕ) (hcb : cb ≤ 2)
    (N : Bool × Bool → ℝ) (h11 : N (true, true) = cb) (h10 : N (true, false) = 2 - cb)
    (h01 : N (false, true) = 2 - cb) :
    (∑ t, ∑ t', N t * N t' * pairOutcome ρ cb t t' - ∑ t, N t * pairOutcome ρ cb t t) / 2 =
      -((cb : ℝ) * (ρ / 2) * (twoLocusValue ρ (cb - 1) - twoLocusValue ρ cb)) := by
  have hD : ρ ^ 2 + 13 * ρ + 18 ≠ 0 := by positivity
  interval_cases cb
  · simp only [Fintype.sum_prod_type, Fintype.sum_bool, h11, h10, h01, pairOutcome,
      twoLocusOutcome, twoLocusValue]
    norm_num
    field_simp
    ring
  · simp only [Fintype.sum_prod_type, Fintype.sum_bool, h11, h10, h01, pairOutcome,
      twoLocusOutcome, twoLocusValue]
    norm_num
    field_simp
    ring
  · simp only [Fintype.sum_prod_type, Fintype.sum_bool, h11, h10, h01, pairOutcome,
      twoLocusOutcome, twoLocusValue]
    norm_num
    field_simp
    ring

open scoped Classical in
noncomputable def carrierType (x y : ℝ) (a : Material) : Bool × Bool :=
  (decide (materialContains a x), decide (materialContains a y))

theorem carrierCount_coalSuccessor (q r : ℝ) (s : State) (i j : Fin s.2.2.1)
    (hij : i.val < j.val) :
    carrierCount q (coalSuccessor s i j) +
        ((carrierType q r (s.2.2.2 i).2).1 && (carrierType q r (s.2.2.2 j).2).1).toNat =
      carrierCount q s := by
  classical
  have h := materialCount_coalSuccessor (fun a => materialContains a q) s i j hij
  simp only [materialContains_merge] at h
  unfold carrierCount carrierType
  by_cases h1 : materialContains (s.2.2.2 i).2 q <;>
    by_cases h2 : materialContains (s.2.2.2 j).2 q <;>
    simp only [h1, h2, or_self, or_true, true_or, ite_true, ite_false, decide_true,
      decide_false, Bool.and_self, Bool.and_false, Bool.false_and, Bool.toNat_true,
      Bool.toNat_false] at h ⊢ <;> omega

theorem jointCarrierCount_coalSuccessor (x y : ℝ) (s : State) (i j : Fin s.2.2.1)
    (hij : i.val < j.val) :
    jointCarrierCount x y (coalSuccessor s i j) +
        ((carrierType x y (s.2.2.2 i).2).1 && (carrierType x y (s.2.2.2 i).2).2).toNat +
        ((carrierType x y (s.2.2.2 j).2).1 && (carrierType x y (s.2.2.2 j).2).2).toNat =
      jointCarrierCount x y s +
        (((carrierType x y (s.2.2.2 i).2).1 || (carrierType x y (s.2.2.2 j).2).1) &&
          ((carrierType x y (s.2.2.2 i).2).2 || (carrierType x y (s.2.2.2 j).2).2)).toNat := by
  classical
  have h := materialCount_coalSuccessor
    (fun a => materialContains a x ∧ materialContains a y) s i j hij
  simp only [materialContains_merge] at h
  unfold jointCarrierCount carrierType
  by_cases h1 : materialContains (s.2.2.2 i).2 x <;>
    by_cases h2 : materialContains (s.2.2.2 j).2 x <;>
    by_cases h3 : materialContains (s.2.2.2 i).2 y <;>
    by_cases h4 : materialContains (s.2.2.2 j).2 y <;>
    simp only [h1, h2, h3, h4, or_self, or_true, or_false, and_self,
      and_true, and_false, ite_true, ite_false, decide_true,
      decide_false, Bool.and_self, Bool.and_false, Bool.and_true,
      Bool.or_self, Bool.or_true, Bool.or_false,
      Bool.toNat_true, Bool.toNat_false] at h ⊢ <;> omega

theorem carrierCount_splitSuccessor (q : ℝ) (s : State) (i : Fin s.2.2.1) (c : ℝ) :
    carrierCount q (splitSuccessor s i c) = carrierCount q s := by
  classical
  have h := materialCount_splitSuccessor (fun a => materialContains a q) s i c
  simp only [materialContains_split_left, materialContains_split_right] at h
  unfold carrierCount
  by_cases h1 : materialContains (s.2.2.2 i).2 q
  · by_cases h2 : q < c
    · simp only [h1, h2, not_le.mpr h2, and_self, and_false, ite_true, ite_false] at h
      omega
    · simp only [h1, h2, not_lt.mp h2, and_self, and_false, ite_true, ite_false] at h
      omega
  · simp only [h1, false_and, ite_false] at h
    omega

open scoped Classical in
theorem jointCarrierCount_splitSuccessor (x y : ℝ) (hxy : x < y) (s : State)
    (i : Fin s.2.2.1) (c : ℝ) :
    jointCarrierCount x y (splitSuccessor s i c) +
        (if (materialContains (s.2.2.2 i).2 x ∧ materialContains (s.2.2.2 i).2 y) ∧
          x < c ∧ c ≤ y then 1 else 0) =
      jointCarrierCount x y s := by
  have h := materialCount_splitSuccessor
    (fun a => materialContains a x ∧ materialContains a y) s i c
  simp only [materialContains_split_left, materialContains_split_right] at h
  unfold jointCarrierCount
  by_cases hb : materialContains (s.2.2.2 i).2 x ∧ materialContains (s.2.2.2 i).2 y
  · obtain ⟨hbx, hby⟩ := hb
    rcases le_or_gt c x with hc1 | hc1
    · have hc2 : c ≤ y := hc1.trans hxy.le
      simp only [hbx, hby, hc1, hc2, not_lt.mpr hc1, not_lt.mpr hc2, and_self, and_false,
        false_and, ite_true, ite_false] at h ⊢
      omega
    · rcases le_or_gt c y with hc2 | hc2
      · simp only [hbx, hby, hc1, hc2, not_le.mpr hc1, not_lt.mpr hc2, and_self, and_false,
          false_and, ite_true, ite_false] at h ⊢
        omega
      · simp only [hbx, hby, hc1, hc2, not_le.mpr hc1, not_le.mpr hc2, and_self, and_false,
          ite_true, ite_false] at h ⊢
        omega
  · have hl : ¬((materialContains (s.2.2.2 i).2 x ∧ x < c) ∧
        materialContains (s.2.2.2 i).2 y ∧ y < c) := fun hh => hb ⟨hh.1.1, hh.2.1⟩
    have hr : ¬((materialContains (s.2.2.2 i).2 x ∧ c ≤ x) ∧
        materialContains (s.2.2.2 i).2 y ∧ c ≤ y) := fun hh => hb ⟨hh.1.1, hh.2.1⟩
    simp only [hb, hl, hr, false_and, ite_false] at h ⊢
    omega

end Rhone.Coalescent.IntervalProcess
