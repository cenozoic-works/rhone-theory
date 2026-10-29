/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.FixationHarmonic
public import Rhone.MarkovChain.MoranAbsorptionSupport

/-!
# Explicit neutral Moran absorption Poisson solution

Source: ewens2004, sec. 3.4. -/

@[expose] public section

namespace Rhone.MarkovChain

open Finset MoranAbsorptionSupport

/-- Source: ewens2004, sec. 3.4. -/
noncomputable def moranAbsorptionTime (N i : ℕ) : ℝ :=
  (N : ℝ) * (((N : ℝ) - i) *
    (∑ j ∈ Icc 1 (i - 1), 1 / ((N : ℝ) - j)) +
    (i : ℝ) * (∑ j ∈ Icc i (N - 1), 1 / (j : ℝ)))

/-- Source: ewens2004, sec. 3.4. -/
theorem moranAbsorptionTime_zero (N : ℕ) : moranAbsorptionTime N 0 = 0 := by
  simp [moranAbsorptionTime]

/-- Source: ewens2004, sec. 3.4. -/
theorem moranAbsorptionTime_self (N : ℕ) : moranAbsorptionTime N N = 0 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [moranAbsorptionTime]
  · have he : Icc N (N - 1) = ∅ := Icc_eq_empty_of_lt (by omega)
    simp [moranAbsorptionTime, he]

/-- Source: ewens2004, sec. 3.4. -/
theorem moranAbsorptionTime_eq_green {N i : ℕ} (hi : i ≤ N) :
    moranAbsorptionTime N i = ∑ j ∈ Icc 1 (N - 1), green N i j := by
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · simp [moranAbsorptionTime_zero, green_zero]
  have hu : Icc 1 (N - 1) = Icc 1 (i - 1) ∪ Icc i (N - 1) := by
    ext j
    simp only [mem_Icc, mem_union]
    omega
  have hd : Disjoint (Icc 1 (i - 1)) (Icc i (N - 1)) := by
    apply disjoint_left.mpr
    intro j hj hk
    simp only [mem_Icc] at hj hk
    omega
  rw [hu, sum_union hd]
  have hl : (∑ j ∈ Icc 1 (i - 1), green N i j) =
      (N : ℝ) * ((N : ℝ) - i) * ∑ j ∈ Icc 1 (i - 1), 1 / ((N : ℝ) - j) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j hj
    simp only [mem_Icc] at hj
    exact green_of_lt (by omega) (by omega) (by omega)
  have hr : (∑ j ∈ Icc i (N - 1), green N i j) =
      (N : ℝ) * i * ∑ j ∈ Icc i (N - 1), 1 / (j : ℝ) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j hj
    simp only [mem_Icc] at hj
    exact green_of_le (by omega) (by omega) hj.1
  rw [hl, hr]
  unfold moranAbsorptionTime
  ring

/-- Source: ewens2004, sec. 3.4. -/
theorem moranAbsorptionTime_poisson (N : ℕ) (i : Fin (N + 1)) :
    (moran N 1).expect (fun j => moranAbsorptionTime N j) i =
      moranAbsorptionTime N i -
        (if 0 < (i : ℕ) ∧ (i : ℕ) < N then 1 else 0) := by
  rw [moran_expect (moranAbsorptionTime N) i]
  by_cases hi0 : (i : ℕ) = 0
  · simp [hi0, moranUp_zero, moranDown_zero]
  by_cases hiN : (i : ℕ) = N
  · simp [hiN, moranUp_self, moranDown_self]
  have hi : 0 < (i : ℕ) ∧ (i : ℕ) < N := by
    have := i.2
    omega
  have hm : (i : ℕ) ∈ Icc 1 (N - 1) := by simp only [mem_Icc]; omega
  have hsum : moranUp N 1 i *
      ((∑ j ∈ Icc 1 (N - 1), green N (i + 1) j) +
       (∑ j ∈ Icc 1 (N - 1), green N (i - 1) j) -
       2 * ∑ j ∈ Icc 1 (N - 1), green N i j) = -1 := by
    calc
      _ = ∑ j ∈ Icc 1 (N - 1), moranUp N 1 i *
          (green N (i + 1) j + green N (i - 1) j - 2 * green N i j) := by
        simp only [mul_add, mul_sub, mul_sum, sum_add_distrib, sum_sub_distrib,
          ← mul_assoc]
      _ = ∑ j ∈ Icc 1 (N - 1), if j = (i : ℕ) then (-1 : ℝ) else 0 := by
        apply sum_congr rfl
        intro j hj
        simp only [mem_Icc] at hj
        exact green_poisson hi.1 hi.2 (by omega) (by omega)
      _ = -1 := by simp [hm]
  have he0 := moranAbsorptionTime_eq_green (N := N) (i := (i : ℕ)) (by omega)
  have hep := moranAbsorptionTime_eq_green (N := N) (i := (i : ℕ) + 1) (by omega)
  have hem := moranAbsorptionTime_eq_green (N := N) (i := (i : ℕ) - 1) (by omega)
  rw [← he0, ← hep, ← hem] at hsum
  rw [ite_eq_left hi, moranDown_one, ← moranUp_one]
  nlinarith

/-- Source: ewens2004, sec. 3.4. -/
theorem moranAbsorptionTime_unique {N : ℕ} (hN : 0 < N)
    (t : Fin (N + 1) → ℝ) (h0 : t 0 = 0) (h1 : t (Fin.last N) = 0)
    (ht : ∀ i, (moran N 1).expect t i = t i -
      (if 0 < (i : ℕ) ∧ (i : ℕ) < N then 1 else 0))
    (i : Fin (N + 1)) : t i = moranAbsorptionTime N i := by
  let g : Fin (N + 1) → ℝ := fun j =>
    t j - moranAbsorptionTime N j + moranFixProb N 1 j
  have hg : (moran N 1).IsHarmonic g := by
    intro j
    have hf := moranFixProb_isHarmonic (N := N) (one_pos : (0 : ℝ) < 1) j
    have hp := moranAbsorptionTime_poisson N j
    change (moran N 1).expect (fun k => t k - moranAbsorptionTime N k + moranFixProb N 1 k) j = _
    simp only [CountKernel.expect, mul_add, mul_sub, sum_add_distrib, sum_sub_distrib]
    change (moran N 1).expect t j -
      (moran N 1).expect (fun k => moranAbsorptionTime N k) j +
      (moran N 1).expect (fun k => moranFixProb N 1 k) j = g j
    rw [ht, hp, hf]
    dsimp [g]
    ring
  have gz : g 0 = 0 := by simp [g, h0, moranAbsorptionTime_zero, moranFixProb_zero]
  have gn : g (Fin.last N) = 1 := by
    simp [g, h1, moranAbsorptionTime_self, moranFixProb_self hN one_pos]
  have he := moran_harmonic_unique hN one_pos g hg gz gn i
  dsimp [g] at he
  linarith

/-- Source: ewens2004, sec. 3.4. -/
private theorem iterate_sub {N : ℕ} (P : CountKernel N)
    (f g : Fin (N + 1) → ℝ) (T : ℕ) (i : Fin (N + 1)) :
    P.expectIter T (fun j => f j - g j) i = P.expectIter T f i - P.expectIter T g i := by
  induction T generalizing i with
  | zero => rfl
  | succ T ih =>
    have he : P.expectIter T (fun j => f j - g j) =
        fun j => P.expectIter T f j - P.expectIter T g j := funext ih
    simp only [CountKernel.expectIter, he, CountKernel.expect_sub]

/-- Source: ewens2004, sec. 3.4. -/
private theorem iterate_expect {N : ℕ} (P : CountKernel N)
    (f : Fin (N + 1) → ℝ) (T : ℕ) (i : Fin (N + 1)) :
    P.expectIter T (P.expect f) i = P.expectIter (T + 1) f i := by
  induction T generalizing i with
  | zero => rfl
  | succ T ih =>
    have he : P.expectIter T (P.expect f) = P.expectIter (T + 1) f := funext ih
    simp only [CountKernel.expectIter, he]

/-- Source: ewens2004, sec. 3.4. -/
theorem moranAbsorptionTime_finite_horizon (N T : ℕ) (i : Fin (N + 1)) :
    (∑ s ∈ range T,
      (moran N 1).expectIter s
        (fun j => if 0 < (j : ℕ) ∧ (j : ℕ) < N then 1 else 0) i) =
      moranAbsorptionTime N i -
        (moran N 1).expectIter T (fun j => moranAbsorptionTime N j) i := by
  induction T with
  | zero => simp [CountKernel.expectIter]
  | succ T ih =>
    rw [sum_range_succ, ih]
    have he : (fun j : Fin (N + 1) =>
        if 0 < (j : ℕ) ∧ (j : ℕ) < N then (1 : ℝ) else 0) =
        fun j : Fin (N + 1) => moranAbsorptionTime N j -
          (moran N 1).expect (fun k => moranAbsorptionTime N k) j := by
      funext j
      rw [moranAbsorptionTime_poisson]
      ring
    rw [he, iterate_sub, iterate_expect]
    ring

end Rhone.MarkovChain
