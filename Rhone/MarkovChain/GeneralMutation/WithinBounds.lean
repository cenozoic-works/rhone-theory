/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.GeneralMutation.Bounds

/-! # Six weighted within-block event-family bounds from the existing uniqueness proof -/

@[expose] public section

namespace Rhone.MarkovChain.GeneralMutation

open Finset LinearAlgebra.Recursion

variable {KA KB : ℕ} {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {νA : Fin KA → F} {νB : Fin KB → F}
variable {PA : Fin KA → Fin KA → F} {PB : Fin KB → Fin KB → F}

theorem coalAB_sum_bound
    {h : Config KA KB → F} (ζ : Config KA KB) (M : F)
    (hmax : ∀ η : Config KA KB, η.nA + η.nB = ζ.nA + ζ.nB →
      |h η| ≤ M * wtC νA νB η)
    (hn2 : 2 ≤ ζ.n)
    (hbd : ∀ η : Config KA KB, η.n ≤ 1 → η.nA + η.nB = ζ.nA + ζ.nB → h η = 0) :
    |∑ i, ∑ j, ((ζ.coalAB i j : ℕ) : F) * h (ζ.mergeAB i j)|
    ≤ ((cab ζ : ℕ) : F) * (M * wtC νA νB ζ) := by
  rw [cab]
  split_ifs with hlt
  · calc |∑ i, ∑ j, ((ζ.coalAB i j : ℕ) : F) * h (ζ.mergeAB i j)|
        ≤ ∑ i, ∑ j, ((ζ.coalAB i j : ℕ) : F) * (M * wtC νA νB ζ) := by
          refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i _ => ?_)
          refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
          rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
          by_cases ha : ζ.a i = 0
          · rw [ζ.coalAB_eq_zero_left j ha]; simp
          by_cases hbj : ζ.b j = 0
          · rw [ζ.coalAB_eq_zero_right i hbj]; simp
          obtain ⟨e1, e2⟩ := ζ.mergeAB_same ha hbj
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          have hle := hmax (ζ.mergeAB i j) (by omega)
          rwa [wtC_mergeAB ζ i j ha hbj] at hle
      _ = ((2 * (ζ.sumA * ζ.sumB) : ℕ) : F) * (M * wtC νA νB ζ) := by
          rw [← ζ.sum_coalAB]
          push_cast
          simp [Finset.sum_mul]
  · have hnn : ζ.n = ζ.sumA + ζ.sumB + ζ.t := rfl
    have hle := ζ.two_mul_sumA_mul_sumB_le
    rw [hnn] at hle hlt
    obtain ⟨ht0, hs1, hr1⟩ :=
      nat_degenerate (u := ζ.sumA) (v := ζ.sumB) (t := ζ.t) (by omega)
        (le_antisymm hle (not_lt.mp hlt))
    have hall : (∑ i, ∑ j, ((ζ.coalAB i j : ℕ) : F) * h (ζ.mergeAB i j)) = 0 := by
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      by_cases ha : ζ.a i = 0
      · rw [ζ.coalAB_eq_zero_left j ha]; simp
      by_cases hbj : ζ.b j = 0
      · rw [ζ.coalAB_eq_zero_right i hbj]; simp
      obtain ⟨e1, e2⟩ := ζ.mergeAB_same ha hbj
      have hmn := ζ.n_mergeAB i j ha hbj
      rw [hbd (ζ.mergeAB i j) (by omega) (by omega), mul_zero]
    rw [hall]
    simp

theorem mutA_sum_bound (hPA : ∀ k i, 0 ≤ PA k i) (hνA : ∀ i, 0 < νA i)
    (hstA : ∀ i, ∑ k, νA k * PA k i = νA i)
    {h : Config KA KB → F} (ζ : Config KA KB) (M : F)
    (hmax : ∀ η : Config KA KB, η.nA + η.nB = ζ.nA + ζ.nB →
      |h η| ≤ M * wtC νA νB η) :
    |∑ i, ∑ k, PA k i * ((ζ.a i : ℕ) : F) * h (mutA ζ i k)|
    ≤ ((ζ.sumA : ℕ) : F) * (M * wtC νA νB ζ) := by
  calc |∑ i, ∑ k, PA k i * ((ζ.a i : ℕ) : F) * h (mutA ζ i k)|
      ≤ ∑ i, ((ζ.a i : ℕ) : F) * (M * wtC νA νB ζ) := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i _ => ?_)
        refine mut_cell_bound hPA hνA hstA i (ζ.a i) ?_
        intro hai k
        obtain ⟨e1, e2⟩ := mutA_same ζ i k hai
        have hle := hmax (mutA ζ i k) (by omega)
        calc |h (mutA ζ i k)| * νA i ≤ (M * wtC νA νB (mutA ζ i k)) * νA i :=
              mul_le_mul_of_nonneg_right hle (hνA i).le
          _ = M * (wtC νA νB (mutA ζ i k) * νA i) := by ring
          _ = M * (wtC νA νB ζ * νA k) := by rw [wtC_mutA ζ i k hai]
    _ = ((ζ.sumA : ℕ) : F) * (M * wtC νA νB ζ) := by
        rw [← Finset.sum_mul, ← Nat.cast_sum]
        rfl

theorem mutCA_sum_bound (hPA : ∀ k i, 0 ≤ PA k i) (hνA : ∀ i, 0 < νA i)
    (hstA : ∀ i, ∑ k, νA k * PA k i = νA i)
    {h : Config KA KB → F} (ζ : Config KA KB) (M : F)
    (hmax : ∀ η : Config KA KB, η.nA + η.nB = ζ.nA + ζ.nB →
      |h η| ≤ M * wtC νA νB η) :
    |∑ i, ∑ j, ∑ k, PA k i * ((ζ.c i j : ℕ) : F) * h (mutCA ζ i j k)|
    ≤ ((ζ.t : ℕ) : F) * (M * wtC νA νB ζ) := by
  calc |∑ i, ∑ j, ∑ k, PA k i * ((ζ.c i j : ℕ) : F) * h (mutCA ζ i j k)|
      ≤ ∑ i, ∑ j, ((ζ.c i j : ℕ) : F) * (M * wtC νA νB ζ) := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i _ => ?_)
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
        refine mut_cell_bound hPA hνA hstA i (ζ.c i j) ?_
        intro hc k
        obtain ⟨e1, e2⟩ := mutCA_same ζ i j k hc
        have hle := hmax (mutCA ζ i j k) (by omega)
        calc |h (mutCA ζ i j k)| * νA i ≤ (M * wtC νA νB (mutCA ζ i j k)) * νA i :=
              mul_le_mul_of_nonneg_right hle (hνA i).le
          _ = M * (wtC νA νB (mutCA ζ i j k) * νA i) := by ring
          _ = M * (wtC νA νB ζ * νA k) := by rw [wtC_mutCA ζ i j k hc]
    _ = ((ζ.t : ℕ) : F) * (M * wtC νA νB ζ) := by
        rw [← ζ.sum_c]
        push_cast
        simp [Finset.sum_mul]

theorem mutB_sum_bound (hPB : ∀ l j, 0 ≤ PB l j) (hνB : ∀ j, 0 < νB j)
    (hstB : ∀ j, ∑ l, νB l * PB l j = νB j)
    {h : Config KA KB → F} (ζ : Config KA KB) (M : F)
    (hmax : ∀ η : Config KA KB, η.nA + η.nB = ζ.nA + ζ.nB →
      |h η| ≤ M * wtC νA νB η) :
    |∑ j, ∑ l, PB l j * ((ζ.b j : ℕ) : F) * h (mutB ζ j l)|
    ≤ ((ζ.sumB : ℕ) : F) * (M * wtC νA νB ζ) := by
  calc |∑ j, ∑ l, PB l j * ((ζ.b j : ℕ) : F) * h (mutB ζ j l)|
      ≤ ∑ j, ((ζ.b j : ℕ) : F) * (M * wtC νA νB ζ) := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
        refine mut_cell_bound hPB hνB hstB j (ζ.b j) ?_
        intro hbj l
        obtain ⟨e1, e2⟩ := mutB_same ζ j l hbj
        have hle := hmax (mutB ζ j l) (by omega)
        calc |h (mutB ζ j l)| * νB j ≤ (M * wtC νA νB (mutB ζ j l)) * νB j :=
              mul_le_mul_of_nonneg_right hle (hνB j).le
          _ = M * (wtC νA νB (mutB ζ j l) * νB j) := by ring
          _ = M * (wtC νA νB ζ * νB l) := by rw [wtC_mutB ζ j l hbj]
    _ = ((ζ.sumB : ℕ) : F) * (M * wtC νA νB ζ) := by
        rw [← Finset.sum_mul, ← Nat.cast_sum]
        rfl

theorem mutCB_sum_bound (hPB : ∀ l j, 0 ≤ PB l j) (hνB : ∀ j, 0 < νB j)
    (hstB : ∀ j, ∑ l, νB l * PB l j = νB j)
    {h : Config KA KB → F} (ζ : Config KA KB) (M : F)
    (hmax : ∀ η : Config KA KB, η.nA + η.nB = ζ.nA + ζ.nB →
      |h η| ≤ M * wtC νA νB η) :
    |∑ i, ∑ j, ∑ l, PB l j * ((ζ.c i j : ℕ) : F) * h (mutCB ζ i j l)|
    ≤ ((ζ.t : ℕ) : F) * (M * wtC νA νB ζ) := by
  calc |∑ i, ∑ j, ∑ l, PB l j * ((ζ.c i j : ℕ) : F) * h (mutCB ζ i j l)|
      ≤ ∑ i, ∑ j, ((ζ.c i j : ℕ) : F) * (M * wtC νA νB ζ) := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i _ => ?_)
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
        refine mut_cell_bound hPB hνB hstB j (ζ.c i j) ?_
        intro hc l
        obtain ⟨e1, e2⟩ := mutCB_same ζ i j l hc
        have hle := hmax (mutCB ζ i j l) (by omega)
        calc |h (mutCB ζ i j l)| * νB j ≤ (M * wtC νA νB (mutCB ζ i j l)) * νB j :=
              mul_le_mul_of_nonneg_right hle (hνB j).le
          _ = M * (wtC νA νB (mutCB ζ i j l) * νB j) := by ring
          _ = M * (wtC νA νB ζ * νB l) := by rw [wtC_mutCB ζ i j l hc]
    _ = ((ζ.t : ℕ) : F) * (M * wtC νA νB ζ) := by
        rw [← ζ.sum_c]
        push_cast
        simp [Finset.sum_mul]

theorem split_sum_bound
    {h : Config KA KB → F} (ζ : Config KA KB) (M : F)
    (hmax : ∀ η : Config KA KB, η.nA + η.nB = ζ.nA + ζ.nB →
      |h η| ≤ M * wtC νA νB η) :
    |∑ i, ∑ j, ((ζ.c i j : ℕ) : F) * h (ζ.split i j)|
    ≤ ((ζ.t : ℕ) : F) * (M * wtC νA νB ζ) := by
  calc |∑ i, ∑ j, ((ζ.c i j : ℕ) : F) * h (ζ.split i j)|
      ≤ ∑ i, ∑ j, ((ζ.c i j : ℕ) : F) * (M * wtC νA νB ζ) := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i _ => ?_)
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
        by_cases hc : ζ.c i j = 0
        · rw [hc]; simp
        obtain ⟨e1, e2⟩ := ζ.split_same hc
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        have hle := hmax (ζ.split i j) (by omega)
        rwa [wtC_split ζ i j hc] at hle
    _ = ((ζ.t : ℕ) : F) * (M * wtC νA νB ζ) := by
        rw [← ζ.sum_c]
        push_cast
        simp [Finset.sum_mul]

end Rhone.MarkovChain.GeneralMutation
