/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.GenotypeHW
public import Rhone.Dynamics.HardyWeinberg
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Cast.Lemmas

/-!
# Executable random mating equals the specification

Source: hardy1908, p. 49; weinberg1908, p. 380; ewens2004, sec. 1.2. -/

@[expose] public section
namespace Rhone.Computation.GenotypeHW
open Finset

theorem cast_sumRange (f : Nat → Rat) (n : Nat) :
    ((sumRange f n : Rat) : ℝ) = ∑ i ∈ range n, ((f i : Rat) : ℝ) := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih => rw [sumRange, Rat.cast_add, ih, Finset.sum_range_succ]

def toReal (K : Nat) (g : Nat → Nat → Rat) : Fin K × Fin K → ℝ :=
  fun ab => ((g ab.1.val ab.2.val : Rat) : ℝ)

theorem alleleFreq_eq (K : Nat) (g : Nat → Nat → Rat) (c : Fin K) :
    ((alleleFreq K g c.val : Rat) : ℝ) = Rhone.Dynamics.alleleFreq (toReal K g) c := by
  unfold alleleFreq Rhone.Dynamics.alleleFreq toReal
  rw [Rat.cast_mul, cast_sumRange, Fintype.sum_prod_type]
  simp only [cast_sumRange]
  congr 1
  · push_cast; norm_num
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases h1 : a = c <;> by_cases h2 : b = c <;> simp [h1, h2, Fin.val_inj]

theorem randomMating_eq (K : Nat) (g : Nat → Nat → Rat) (c d : Fin K) :
    ((randomMating K g c.val d.val : Rat) : ℝ) =
      Rhone.Dynamics.randomMating (toReal K g) (c, d) := by
  unfold randomMating Rhone.Dynamics.randomMating
  rw [Rat.cast_mul, alleleFreq_eq, alleleFreq_eq]

theorem total_eq (K : Nat) (g : Nat → Nat → Rat) :
    ((total K g : Rat) : ℝ) = ∑ ab, toReal K g ab := by
  unfold total toReal
  rw [cast_sumRange, Fintype.sum_prod_type, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [cast_sumRange, ← Fin.sum_univ_eq_sum_range (fun b => ((g a.val b : Rat) : ℝ))]

theorem randomMating_idempotent (K : Nat) (g : Nat → Nat → Rat) (hg : total K g = 1)
    (c d : Nat) (hc : c < K) (hd : d < K) :
    randomMating K (randomMating K g) c d = randomMating K g c d := by
  have hg' : ∑ ab, toReal K g ab = 1 := by
    rw [← total_eq, hg]; simp
  have key := congrFun (Rhone.Dynamics.randomMating_idempotent (toReal K g) hg') (⟨c, hc⟩, ⟨d, hd⟩)
  apply Rat.cast_injective (α := ℝ)
  have h2 : ((randomMating K (randomMating K g) c d : Rat) : ℝ) =
      Rhone.Dynamics.randomMating (toReal K (randomMating K g)) (⟨c, hc⟩, ⟨d, hd⟩) :=
    randomMating_eq K (randomMating K g) ⟨c, hc⟩ ⟨d, hd⟩
  have h3 : toReal K (randomMating K g) = Rhone.Dynamics.randomMating (toReal K g) := by
    funext ab
    exact randomMating_eq K g ab.1 ab.2
  rw [h2, h3, key]
  exact (randomMating_eq K g ⟨c, hc⟩ ⟨d, hd⟩).symm

theorem alleleFreq_randomMating (K : Nat) (g : Nat → Nat → Rat) (hg : total K g = 1)
    (e : Nat) (he : e < K) :
    alleleFreq K (randomMating K g) e = alleleFreq K g e := by
  have hg' : ∑ ab, toReal K g ab = 1 := by
    rw [← total_eq, hg]; simp
  have key := Rhone.Dynamics.alleleFreq_randomMating (toReal K g) hg' ⟨e, he⟩
  apply Rat.cast_injective (α := ℝ)
  have h3 : toReal K (randomMating K g) = Rhone.Dynamics.randomMating (toReal K g) := by
    funext ab
    exact randomMating_eq K g ab.1 ab.2
  rw [alleleFreq_eq K (randomMating K g) ⟨e, he⟩, h3, key]
  exact (alleleFreq_eq K g ⟨e, he⟩).symm

theorem hwProportions_eq (g : Nat → Nat → Rat) (hg : total 2 g = 1) :
    hwProportions g = ((g 0 0 + (g 0 1 + g 1 0) / 2) ^ 2,
      2 * (g 0 0 + (g 0 1 + g 1 0) / 2) * (1 - (g 0 0 + (g 0 1 + g 1 0) / 2)),
      (1 - (g 0 0 + (g 0 1 + g 1 0) / 2)) ^ 2) := by
  have hg' : ∑ ab, toReal 2 g ab = 1 := by
    rw [← total_eq, hg]; simp
  obtain ⟨-, -, h00, h01, h11⟩ := Rhone.Dynamics.hw_two_allele (toReal 2 g) hg'
    (((g 0 0 + (g 0 1 + g 1 0) / 2 : Rat)) : ℝ) (by simp [toReal])
  have e00 := randomMating_eq 2 g 0 0
  have e01 := randomMating_eq 2 g 0 1
  have e10 := randomMating_eq 2 g 1 0
  have e11 := randomMating_eq 2 g 1 1
  simp only [Fin.val_zero, Fin.val_one] at e00 e01 e10 e11
  unfold hwProportions
  simp only [Prod.mk.injEq]
  push_cast at h00 h01 h11
  refine ⟨?_, ?_, ?_⟩ <;> apply Rat.cast_injective (α := ℝ) <;> push_cast
  · rw [e00, h00]
  · rw [e01, e10, h01]
  · rw [e11, h11]

end Rhone.Computation.GenotypeHW
