/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.MoranAbsorption
public import Rhone.MarkovChain.MoranSelectionSums

/-!
# Selected Moran absorption Poisson solution

Source: ewens2004, sec. 3.4; altrock_traulsen2009, eq. (14). -/

@[expose] public section
namespace Rhone.MarkovChain

open Finset MoranSelectionSupport

/-- Source: altrock_traulsen2009, eq. (14). -/
noncomputable def moranSelectionTime (N : ℕ) (r : ℝ) (i : ℕ) : ℝ :=
  ∑ j ∈ Icc 1 (N - 1), moranSelectionGreen N r i j

/-- Source: ewens2004, sec. 3.4. -/
theorem moranSelectionTime_zero (N : ℕ) (r : ℝ) : moranSelectionTime N r 0 = 0 := by
  simp [moranSelectionTime, moranSelectionGreen, moranFixProb_zero]

/-- Source: ewens2004, sec. 3.4. -/
theorem moranSelectionTime_self (N : ℕ) (r : ℝ) : moranSelectionTime N r N = 0 := by
  unfold moranSelectionTime
  apply sum_eq_zero
  intro j hj
  simp only [mem_Icc] at hj
  have hjN : j ≤ N := by omega
  simp [moranSelectionGreen, max_eq_left hjN]

/-- Source: ewens2004, sec. 3.4. -/
theorem moranSelectionTime_poisson (N : ℕ) {r : ℝ} (hr : 0 < r) (i : Fin (N + 1)) :
    (moran N r).expect (fun j => moranSelectionTime N r j) i =
      moranSelectionTime N r i -
        (if 0 < (i : ℕ) ∧ (i : ℕ) < N then 1 else 0) := by
  rw [moran_expect (moranSelectionTime N r) i]
  by_cases hi0 : (i : ℕ) = 0
  · simp [hi0, moranUp_zero, moranDown_zero]
  by_cases hiN : (i : ℕ) = N
  · simp [hiN, moranUp_self, moranDown_self]
  have hi : 0 < (i : ℕ) ∧ (i : ℕ) < N := by have := i.2; omega
  have hm : (i : ℕ) ∈ Icc 1 (N - 1) := by simp only [mem_Icc]; omega
  have hsum :
      moranUp N r i * (moranSelectionTime N r (i + 1) - moranSelectionTime N r i) +
      moranDown N r i * (moranSelectionTime N r (i - 1) - moranSelectionTime N r i) = -1 := by
    unfold moranSelectionTime
    calc
      _ = ∑ j ∈ Icc 1 (N - 1),
          (moranUp N r i * (moranSelectionGreen N r (i + 1) j - moranSelectionGreen N r i j) +
          moranDown N r i * (moranSelectionGreen N r (i - 1) j - moranSelectionGreen N r i j)) := by
        simp only [mul_sub, mul_sum, sum_add_distrib, sum_sub_distrib]
      _ = ∑ j ∈ Icc 1 (N - 1), if j = (i : ℕ) then (-1 : ℝ) else 0 := by
        apply sum_congr rfl
        intro j hj
        simp only [mem_Icc] at hj
        exact green_poisson hr hi.1 hi.2 (by omega) (by omega)
      _ = -1 := by simp [hm]
  rw [ite_eq_left hi]
  linarith

/-- Source: ewens2004, sec. 3.4. -/
theorem moranSelectionTime_unique {N : ℕ} (hN : 0 < N) {r : ℝ} (hr : 0 < r)
    (t : Fin (N + 1) → ℝ) (h0 : t 0 = 0) (h1 : t (Fin.last N) = 0)
    (ht : ∀ i, (moran N r).expect t i = t i -
      (if 0 < (i : ℕ) ∧ (i : ℕ) < N then 1 else 0))
    (i : Fin (N + 1)) : t i = moranSelectionTime N r i := by
  let g : Fin (N + 1) → ℝ := fun j =>
    t j - moranSelectionTime N r j + moranFixProb N r j
  have hg : (moran N r).IsHarmonic g := by
    intro j
    have hf := moranFixProb_isHarmonic (N := N) hr j
    have hp := moranSelectionTime_poisson N hr j
    change (moran N r).expect (fun k => t k - moranSelectionTime N r k + moranFixProb N r k) j = _
    simp only [CountKernel.expect, mul_add, mul_sub, sum_add_distrib, sum_sub_distrib]
    change (moran N r).expect t j -
      (moran N r).expect (fun k => moranSelectionTime N r k) j +
      (moran N r).expect (fun k => moranFixProb N r k) j = g j
    rw [ht, hp, hf]
    dsimp [g]
    ring
  have gz : g 0 = 0 := by simp [g, h0, moranSelectionTime_zero, moranFixProb_zero]
  have gn : g (Fin.last N) = 1 := by
    simp [g, h1, moranSelectionTime_self, moranFixProb_self hN hr]
  have he := moran_harmonic_unique hN hr g hg gz gn i
  dsimp [g] at he
  linarith

/-- Source: ewens2004, sec. 3.4. -/
theorem moranSelectionTime_one (N : ℕ) (i : Fin (N + 1)) :
    moranSelectionTime N 1 i = moranAbsorptionTime N i := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [moranSelectionTime_zero, moranAbsorptionTime_zero]
  · exact moranAbsorptionTime_unique hN (fun j => moranSelectionTime N 1 j)
      (moranSelectionTime_zero N 1) (by simpa using moranSelectionTime_self N 1)
      (moranSelectionTime_poisson N one_pos) i

/-- Source: altrock_traulsen2009, eq. (14). -/
theorem moranSelectionTime_single_mutant (N : ℕ) {r : ℝ} (hr : 0 < r) :
    moranSelectionTime N r 1 = moranFixProb N r 1 *
      (∑ k ∈ Icc 1 (N - 1), ∑ l ∈ Icc 1 k,
        (r⁻¹) ^ (k - l) / moranUp N r l) := green_single_mutant N hr

end Rhone.MarkovChain
