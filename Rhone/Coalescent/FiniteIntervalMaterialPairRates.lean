/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Basic.NNReal.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Rhone.Coalescent.FiniteIntervalMaterialMarked
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # Unordered pair intensity derived from the concrete candidate enumeration -/
@[expose] public section

namespace Rhone.Coalescent.IntervalProcess
open scoped BigOperators
open Finset
open scoped ENNReal NNReal

theorem unordered_pair_rate (m : ℕ) :
    (∑ i : Fin m, ∑ j : Fin m, (if i.val < j.val then 1 else 0 : ℝ)) =
      (m : ℝ) * ((m : ℝ) - 1) / 2 := by
  let S : ℝ := ∑ i : Fin m, ∑ j : Fin m, (if i.val < j.val then 1 else 0 : ℝ)
  have hrow (i : Fin m) :
      (∑ j : Fin m, (if i = j then 0 else 1 : ℝ)) = (m : ℝ) - 1 := by
    calc
      _ = ∑ j : Fin m, (1 - (if i = j then 1 else 0 : ℝ)) := by
        apply sum_congr rfl
        intro j _
        split_ifs <;> ring
      _ = _ := by simp [sum_sub_distrib]
  have hdiag : (∑ i : Fin m, ∑ j : Fin m, (if i = j then 0 else 1 : ℝ)) =
      (m : ℝ) * ((m : ℝ) - 1) := by
    simp_rw [hrow]
    simp
    ring
  have hswap : (∑ i : Fin m, ∑ j : Fin m, (if j.val < i.val then 1 else 0 : ℝ)) = S := by
    exact sum_comm
  have heq (i j : Fin m) :
      (if i.val < j.val then 1 else 0 : ℝ) +
      (if j.val < i.val then 1 else 0 : ℝ) = (if i = j then 0 else 1 : ℝ) := by
    split_ifs <;> simp_all [Fin.ext_iff] <;> omega
  have htwice : 2*S = (m : ℝ) * ((m : ℝ) - 1) := by
    calc
      2*S = S+S := by ring
      _ = ∑ i : Fin m, ∑ j : Fin m,
          ((if i.val < j.val then 1 else 0 : ℝ) +
           (if j.val < i.val then 1 else 0 : ℝ)) := by
        simp_rw [sum_add_distrib]
        rw [hswap]
      _ = ∑ i : Fin m, ∑ j : Fin m, (if i = j then 0 else 1 : ℝ) := by
        apply sum_congr rfl
        intro i _
        apply sum_congr rfl
        intro j _
        exact heq i j
      _ = _ := hdiag
  change S = _
  linarith

theorem coalRate_unrestricted (s : State) :
    (coalRate false s : ℝ) =
      (s.2.2.1 : ℝ) * ((s.2.2.1 : ℝ) - 1) / 2 := by
  have hr (ij : Fin s.2.2.1 × Fin s.2.2.1) :
      (candidateRate false 0 s (.inl ij) : ℝ) =
        (if ij.1.val < ij.2.val then 1 else 0 : ℝ) := by
    classical
    simp only [candidateRate, true_or, and_true]
    split_ifs <;> simp
  simp only [coalRate, NNReal.coe_sum]
  simp_rw [hr]
  rw [Fintype.sum_prod_type]
  exact unordered_pair_rate s.2.2.1

theorem pairAtom_measurable (i j : ℕ) :
    MeasurableSet ({Sum.inr (Sum.inl (i,j))} : Set Event) := by
  have heq : ({Sum.inr (Sum.inl (i,j))} : Set Event) =
      Sum.inr '' (Sum.inl '' ({(i,j)} : Set (ℕ × ℕ))) := by simp
  rw [heq]
  exact (measurableSet_singleton (i,j)).inl_image.inr_image

theorem candidateLaw_pair_mass (s : State) (a : ActionIndex s)
    (ij : Fin s.2.2.1 × Fin s.2.2.1) :
    candidateLaw s a {Sum.inr (Sum.inl (ij.1.val, ij.2.val))} =
      match a with | .inl kl => if kl = ij then 1 else 0 | .inr _ => 0 := by
  classical
  cases a with
  | inl kl =>
    rw [candidateLaw, MeasureTheory.Measure.dirac_apply' _ (pairAtom_measurable _ _)]
    simp [Set.indicator, Prod.ext_iff, Fin.ext_iff]
  | inr i =>
    rw [candidateLaw, MeasureTheory.Measure.map_apply (by fun_prop)
      (pairAtom_measurable _ _)]
    have heq : (fun u : ℝ => Sum.inr (Sum.inr
        (i.val, hullLo (s.2.2.2 i).2 + hullLength (s.2.2.2 i).2 * u)) : ℝ → Event) ⁻¹'
        {Sum.inr (Sum.inl (ij.1.val, ij.2.val))} = ∅ := by
      ext u
      simp
    rw [heq]
    exact MeasureTheory.measure_empty

theorem rawMarkedLaw_pair_mass (mode : Mode) (R : ℝ) (s : State)
    (ij : Fin s.2.2.1 × Fin s.2.2.1) :
    rawMarkedLaw mode R s {Sum.inr (Sum.inl (ij.1.val, ij.2.val))} =
      (candidateRate mode R s (.inl ij) : ℝ≥0∞) := by
  simp [rawMarkedLaw, candidateLaw_pair_mass, Fintype.sum_sum_type]

theorem markedLaw_pair_mass (R : ℝ) (s : State)
    (hm : 1 < s.2.2.1) (hr : totalRate false R s ≠ 0)
    (ij : Fin s.2.2.1 × Fin s.2.2.1) (hij : ij.1.val < ij.2.val) :
    markedLaw false R s {Sum.inr (Sum.inl (ij.1.val, ij.2.val))} =
      (totalRate false R s : ℝ≥0∞)⁻¹ := by
  rw [markedLaw, ite_eq_right (not_or.mpr ⟨Nat.not_le.mpr hm, hr⟩),
    MeasureTheory.Measure.smul_apply,
    rawMarkedLaw_pair_mass, smul_eq_mul]
  simp [candidateRate, hij]

end Rhone.Coalescent.IntervalProcess
