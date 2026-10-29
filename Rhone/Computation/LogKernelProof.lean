/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.LogKernel
public import Rhone.Computation.GenericKernelProof
public import Rhone.Computation.Float64KernelProof
public import Rhone.Computation.RationalLogBounds

/-! # The core-library logarithm checks equal the Mathlib ones -/

@[expose] public section
namespace Rhone.Computation.LogKernel
open Float64Kernel

theorem powRat_eq (x : Rat) (n : Nat) : powRat x n = x ^ n := by
  induction n with
  | zero => simp [powRat]
  | succ n ih => rw [powRat, ih, pow_succ]

theorem series_eq (x : Rat) (n : Nat) : series x n = RationalLogBounds.series x n := by
  simp only [series, RationalLogBounds.series, GenericKernel.lsum_eq, powRat_eq, argument,
    RationalLogBounds.argument]
  congr 1
  rw [Finset.sum_range (fun i => ((x - 1) / (x + 1)) ^ (2 * i + 1) / (2 * i + 1 : Rat))]
  push_cast
  rfl

theorem errorBound_eq (x : Rat) (n : Nat) :
    errorBound x n = RationalLogBounds.errorBound x n := by
  simp only [errorBound, RationalLogBounds.errorBound, powRat_eq, absRat_eq, argument,
    RationalLogBounds.argument]

theorem checkNormalized_eq (x claimed budget : Rat) (e : Int) (n : Nat) :
    checkNormalized x claimed budget e n =
      RationalLogBounds.checkNormalized x claimed budget e n := by
  simp only [checkNormalized, RationalLogBounds.checkNormalized, normalizedSeries,
    RationalLogBounds.normalizedSeries, normalizedError, RationalLogBounds.normalizedError,
    series_eq, errorBound_eq, absRat_eq, pow2_eq]
  exact Bool.eq_iff_iff.mpr (decide_eq_true_iff.trans decide_eq_true_iff.symm)

theorem bracketCheck_sound {x claimed budget : Rat} (h : bracketCheck x claimed budget = true) :
    |(claimed : Real) - Real.log (x : Real)| ≤ (budget : Real) := by
  simp only [bracketCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨ha0, hax, hxb⟩, hA⟩, hB⟩ := h
  rw [checkNormalized_eq] at hA hB
  have hA' := RationalLogBounds.checkNormalized_sound hA
  have hB' := RationalLogBounds.checkNormalized_sound hB
  set a := pow2 (binade x - 64) * ((x / pow2 (binade x - 64)).floor : Rat)
  set b := a + pow2 (binade x - 64)
  have ha0' : (0 : Real) < (a : Real) := by exact_mod_cast ha0
  have hax' : (a : Real) ≤ (x : Real) := by exact_mod_cast hax
  have hxb' : (x : Real) ≤ (b : Real) := by exact_mod_cast hxb
  have hlo : Real.log (a : Real) ≤ Real.log (x : Real) := Real.log_le_log ha0' hax'
  have hhi : Real.log (x : Real) ≤ Real.log (b : Real) :=
    Real.log_le_log (lt_of_lt_of_le ha0' hax') hxb'
  rw [abs_le] at hA' hB' ⊢
  constructor <;> linarith [hA'.1, hA'.2, hB'.1, hB'.2]

end Rhone.Computation.LogKernel
