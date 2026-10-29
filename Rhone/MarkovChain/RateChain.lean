/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.AbsorptionProb

/-! # Finite-state Markov chains in continuous time -/

@[expose] public section

namespace Rhone.MarkovChain

open Finset

structure RateChain (S : Type*) [Fintype S] where
  Q : Matrix S S ℝ
  off_diag_nonneg : ∀ x y, x ≠ y → 0 ≤ Q x y
  row_sum : ∀ x, ∑ y, Q x y = 0

namespace RateChain

variable {S : Type*} [Fintype S] [DecidableEq S] (R : RateChain S)

omit [DecidableEq S] in
def rate (x : S) : ℝ := -R.Q x x

theorem rate_eq_sum (x : S) : R.rate x = ∑ y ∈ univ.erase x, R.Q x y := by
  have h := R.row_sum x
  rw [← Finset.add_sum_erase univ _ (mem_univ x)] at h
  rw [rate]
  linarith

omit [DecidableEq S] in
theorem rate_nonneg (x : S) : 0 ≤ R.rate x := by
  classical
  rw [rate_eq_sum]
  exact Finset.sum_nonneg fun y hy => R.off_diag_nonneg x y (Finset.ne_of_mem_erase hy).symm

noncomputable def jumpMatrix : Matrix S S ℝ := fun x y =>
  if R.rate x = 0 then (if x = y then 1 else 0) else (if x = y then 0 else R.Q x y / R.rate x)

theorem sum_jumpMatrix_mul {x : S} (hx : R.rate x ≠ 0) (u : S → ℝ) :
    ∑ y, R.jumpMatrix x y * u y = u x + (∑ y, R.Q x y * u y) / R.rate x := by
  have hterm : ∀ y, R.jumpMatrix x y * u y =
      (if x = y then u y else 0) + R.Q x y * u y / R.rate x := by
    intro y
    by_cases hxy : x = y
    · subst hxy
      have hq : R.Q x x = -R.rate x := by simp [rate]
      simp only [jumpMatrix, hx, ↓reduceIte, zero_mul, hq]
      field_simp
      ring
    · simp only [jumpMatrix, hx, hxy, ↓reduceIte]
      ring
  simp only [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq, ← Finset.sum_div]
  simp

noncomputable def jumpChain : FinChain S where
  P := R.jumpMatrix
  nonneg x y := by
    unfold jumpMatrix
    split_ifs with h1 h2 h2
    · exact zero_le_one
    · exact le_rfl
    · exact le_rfl
    · exact div_nonneg (R.off_diag_nonneg x y h2) (R.rate_nonneg x)
  row_sum x := by
    by_cases hx : R.rate x = 0
    · simp [jumpMatrix, hx]
    · have h := R.sum_jumpMatrix_mul hx (fun _ => 1)
      simp only [mul_one, R.row_sum x, zero_div, add_zero] at h
      exact h

theorem jumpChain_P : R.jumpChain.P = R.jumpMatrix := rfl

variable {R}

theorem jumpChain_isAbsorbing {a : S} (ha : R.rate a = 0) : R.jumpChain.IsAbsorbing a := by
  simp [FinChain.IsAbsorbing, jumpChain_P, jumpMatrix, ha]

theorem jumpChain_isAbsorbingSet {A : Finset S} (hA : ∀ a ∈ A, R.rate a = 0) :
    R.jumpChain.IsAbsorbingSet A := fun a ha => jumpChain_isAbsorbing (hA a ha)

theorem jumpChain_P_of_ne {x y : S} (hx : R.rate x ≠ 0) (hxy : x ≠ y) :
    R.jumpChain.P x y = R.Q x y / R.rate x := by
  simp [jumpChain_P, jumpMatrix, hx, hxy]

variable (R)

noncomputable def expectedCost (A : Finset S) (c : S → ℝ) (x : S) : ℝ :=
  R.jumpChain.potential A (fun y => c y / R.rate y) x

noncomputable def expectedTime (A : Finset S) (x : S) : ℝ := R.expectedCost A (fun _ => 1) x

variable {R} {A : Finset S}

theorem expectedCost_of_mem (hA : R.jumpChain.IsAbsorbingSet A) {a : S} (ha : a ∈ A)
    (c : S → ℝ) : R.expectedCost A c a = 0 :=
  FinChain.potential_of_mem hA ha _

theorem expectedCost_nonneg (R : RateChain S) (A : Finset S) {c : S → ℝ} (hc : ∀ y, 0 ≤ c y)
    (x : S) : 0 ≤ R.expectedCost A c x :=
  FinChain.potential_nonneg _ A (fun y => div_nonneg (hc y) (R.rate_nonneg y)) x

theorem expectedCost_generator (hA : R.jumpChain.IsAbsorbingSet A) (hR : R.jumpChain.Reaches A)
    (c : S → ℝ) {x : S} (hx : x ∉ A) (hq : R.rate x ≠ 0) :
    ∑ y, R.Q x y * R.expectedCost A c y = -c x := by
  have h := FinChain.potential_step hA hR (fun y => c y / R.rate y) x
  rw [ite_eq_right hx, jumpChain_P, R.sum_jumpMatrix_mul hq] at h
  change R.expectedCost A c x = c x / R.rate x +
    (R.expectedCost A c x + (∑ y, R.Q x y * R.expectedCost A c y) / R.rate x) at h
  have h2 : (c x + ∑ y, R.Q x y * R.expectedCost A c y) / R.rate x = 0 := by
    rw [add_div]
    linarith
  rcases div_eq_zero_iff.1 h2 with h3 | h3
  · linarith
  · exact absurd h3 hq

theorem eq_expectedCost_of_generator (hA : R.jumpChain.IsAbsorbingSet A)
    (hR : R.jumpChain.Reaches A) (hq : ∀ x, x ∉ A → R.rate x ≠ 0) {c u : S → ℝ}
    (h0 : ∀ a ∈ A, u a = 0) (hgen : ∀ x, x ∉ A → ∑ y, R.Q x y * u y = -c x) :
    u = R.expectedCost A c := by
  refine funext fun z => congrFun (FinChain.eq_potential_of_step hA hR h0 fun x hx => ?_) z
  rw [jumpChain_P, R.sum_jumpMatrix_mul (hq x hx), hgen x hx]
  ring

end RateChain

end Rhone.MarkovChain
