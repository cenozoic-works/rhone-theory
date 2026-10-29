/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.SlotDeletion.BiallelicDenominator
public import Rhone.Probability.SamplingNumerators.PhiCleared
public import Rhone.Probability.SamplingNumerators.Numerator
public import Rhone.LinearAlgebra.GaloisDegreeSeven.Positive
public import Mathlib.Data.Nat.Choose.Sum

/-! # The sampling probability at the separated `(3,3)` configuration -/

@[expose] public section

namespace Rhone.Probability.SamplingNumerators

open Finset LinearAlgebra.Recursion LinearAlgebra.Multilinear Multilinear LinearAlgebra.SlotDeletion
    SlotDeletion

def piThird {F : Type*} [Field F] : Fin 2 → F := ![1 / 3, 2 / 3]

@[simp] theorem piThird_zero {F : Type*} [Field F] :
    (piThird : Fin 2 → F) 0 = 1 / 3 := rfl

def sampling33 : Config 2 2 := ⟨![3, 0], ![3, 0], 0⟩

theorem xi_empty_sampling33 :
    xi (∅ : Finset (Fin 3 × Fin 3)) (fun _ => (0 : Fin 2))
      (fun _ => (0 : Fin 2)) = sampling33 := by
  apply Config.ext
  · funext i
    fin_cases i <;> simp [xi, freeA, domA, sampling33]
  · funext j
    fin_cases j <;> simp [xi, freeB, domB, sampling33]
  · funext i j
    simp [xi, sampling33]

private theorem sum_finset_fin_three_card {F : Type*} [Field F] (g : ℕ → F) :
    (∑ S : Finset (Fin 3), g S.card) = g 0 + 3 * g 1 + 3 * g 2 + g 3 := by
  have hu : (univ : Finset (Fin 3)).powerset = univ := by
    ext S
    simp
  rw [← hu, sum_powerset_apply_card]
  norm_num [sum_range_succ, nsmul_eq_mul, Nat.choose]

section Assembly

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {a b ρ : F} {q : Config 2 2 → F}
variable (ha : 0 < a) (hb : 0 < b) (hr : 0 ≤ ρ)
variable (hq : IsSolution a b ρ piThird piThird q)

theorem piThird_sum : (piThird : Fin 2 → F) 0 + piThird 1 = 1 := by
  norm_num [piThird]

include ha hb hr hq

theorem sampling33_expansion :
    q sampling33 = 1 / 729 + (1 / 27) *
      (Phi q piThird piThird 2 0 0 + Phi q piThird piThird 3 0 0 +
       Phi q piThird piThird 0 2 0 + Phi q piThird piThird 0 3 0) +
      Phi q piThird piThird 2 2 0 + Phi q piThird piThird 2 3 0 +
      Phi q piThird piThird 3 2 0 + Phi q piThird piThird 3 3 0 := by
  have h := q_xi_eq_sum_Phi ha hb hr hq piThird_sum piThird_sum
    (∅ : Finset (Fin 3 × Fin 3)) ⟨by simp, by simp⟩
    (fun _ => (0 : Fin 2)) (fun _ => (0 : Fin 2))
  rw [xi_empty_sampling33] at h
  simp only [piThird_zero, eps_zero, prod_const, one_pow, mul_one, card_compl,
    Fintype.card_fin, pairsIn, filter_empty, card_empty] at h
  have hzA := Phi_i_one ha hb hr hq piThird_sum
  have hzB := Phi_j_one ha hb hr hq piThird_sum piThird_sum
  have hz0 := Phi_zero_zero hq 0
  let g : ℕ → ℕ → F := fun i j =>
    (1 / 3) ^ (3 - i) * (1 / 3) ^ (3 - j) * Phi q piThird piThird i j 0
  change q sampling33 = ∑ S : Finset (Fin 3), ∑ T : Finset (Fin 3), g S.card T.card at h
  rw [sum_finset_fin_three_card (fun i => ∑ T : Finset (Fin 3), g i T.card)] at h
  rw [sum_finset_fin_three_card (g 0), sum_finset_fin_three_card (g 1),
    sum_finset_fin_three_card (g 2), sum_finset_fin_three_card (g 3)] at h
  dsimp [g] at h
  norm_num [hzA, hzB, hz0] at h
  linear_combination h

theorem sampling33_cleared :
    d33 a b ρ * q sampling33 = samplingNumerator a b ρ := by
  have hexp := sampling33_expansion ha hb hr hq
  have h20 := phi20_cleared ha hb hr hq piThird_sum piThird_sum 0
  have h30 := phi30_cleared ha hb hr hq piThird_sum piThird_sum 0
  have h02 := phi02_cleared ha hb hr hq piThird_sum piThird_sum 0
  have h03 := phi03_cleared ha hb hr hq piThird_sum piThird_sum 0
  have h22 := phi22_cleared ha hb hr hq piThird_sum piThird_sum 0
  have h23 := phi23_cleared ha hb hr hq piThird_sum piThird_sum 0
  have h32 := phi32_cleared ha hb hr hq piThird_sum piThird_sum 0
  have h33 := phi33_cleared ha hb hr hq piThird_sum piThird_sum 0
  norm_num [kap, gam, piThird] at h20 h30 h02 h03 h22 h23 h32 h33
  simp only [piThird] at hexp
  simp only [d22, c22] at h22
  simp only [d23, c23] at h23
  simp only [d32, c32] at h32
  simp only [d33, c33] at h33 ⊢
  norm_num [samplingNumerator, lowerNumerator, c33]
  linear_combination
    ((a + 1) * (a + 2) * (b + 1) * (b + 2) * LinearAlgebra.Tridiag.E F 2 2 a b ρ *
      LinearAlgebra.Tridiag.E F 2 3 a b ρ * LinearAlgebra.Tridiag.E F 3 2 a b ρ *
          LinearAlgebra.Tridiag.E F 3 3 a b ρ) * hexp +
    ((1 / 27) * (a + 2) * (b + 1) * (b + 2) * LinearAlgebra.Tridiag.E F 2 2 a b ρ *
      LinearAlgebra.Tridiag.E F 2 3 a b ρ * LinearAlgebra.Tridiag.E F 3 2 a b ρ *
          LinearAlgebra.Tridiag.E F 3 3 a b ρ) * h20 +
    ((1 / 27) * (b + 1) * (b + 2) * LinearAlgebra.Tridiag.E F 2 2 a b ρ *
      LinearAlgebra.Tridiag.E F 2 3 a b ρ * LinearAlgebra.Tridiag.E F 3 2 a b ρ *
          LinearAlgebra.Tridiag.E F 3 3 a b ρ) * h30 +
    ((1 / 27) * (a + 1) * (a + 2) * (b + 2) * LinearAlgebra.Tridiag.E F 2 2 a b ρ *
      LinearAlgebra.Tridiag.E F 2 3 a b ρ * LinearAlgebra.Tridiag.E F 3 2 a b ρ *
          LinearAlgebra.Tridiag.E F 3 3 a b ρ) * h02 +
    ((1 / 27) * (a + 1) * (a + 2) * LinearAlgebra.Tridiag.E F 2 2 a b ρ *
      LinearAlgebra.Tridiag.E F 2 3 a b ρ * LinearAlgebra.Tridiag.E F 3 2 a b ρ *
          LinearAlgebra.Tridiag.E F 3 3 a b ρ) * h03 +
    ((a + 2) * (b + 2) * LinearAlgebra.Tridiag.E F 2 3 a b ρ * LinearAlgebra.Tridiag.E F 3 2 a b ρ *
      LinearAlgebra.Tridiag.E F 3 3 a b ρ) * h22 +
    ((a + 2) * LinearAlgebra.Tridiag.E F 3 2 a b ρ * LinearAlgebra.Tridiag.E F 3 3 a b ρ) * h23 +
    ((b + 2) * LinearAlgebra.Tridiag.E F 2 3 a b ρ * LinearAlgebra.Tridiag.E F 3 3 a b ρ) * h32 +
        h33

theorem Dfull_sampling33 :
    Dfull a b ρ 3 3 * q sampling33 = samplingNumerator a b ρ := by
  rw [← d33_eq_Dfull]
  exact sampling33_cleared ha hb hr hq

omit hq in
theorem d33_pos : 0 < d33 a b ρ := by
  have h22 := LinearAlgebra.GaloisDegreeSeven.E_pos (i := 2) (j := 2)
      (by omega) (by omega) ha.le hb.le hr
  have h23 := LinearAlgebra.GaloisDegreeSeven.E_pos (i := 2) (j := 3)
      (by omega) (by omega) ha.le hb.le hr
  have h32 := LinearAlgebra.GaloisDegreeSeven.E_pos (i := 3) (j := 2)
      (by omega) (by omega) ha.le hb.le hr
  have h33 := LinearAlgebra.GaloisDegreeSeven.E_pos (i := 3) (j := 3)
      (by omega) (by omega) ha.le hb.le hr
  dsimp [d33, c33]
  positivity

theorem sampling33_eq_quotient :
    q sampling33 = samplingNumerator a b ρ / d33 a b ρ := by
  apply (eq_div_iff (d33_pos ha hb hr).ne').2
  simpa only [mul_comm] using sampling33_cleared ha hb hr hq

end Assembly

end Rhone.Probability.SamplingNumerators
