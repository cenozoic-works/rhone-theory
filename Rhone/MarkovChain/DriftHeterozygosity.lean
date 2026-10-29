/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.Moran

/-!
# Heterozygosity decay under drift

Source: wright1931, pp. 108–110; ewens2004, secs. 3.2, 3.3. -/

@[expose] public section

namespace Rhone.MarkovChain

open Finset

noncomputable def het (N i : ℕ) : ℝ := 2 * ((i : ℝ) / N) * (1 - (i : ℝ) / N)

theorem wf_expect_het (N : ℕ) (i : Fin (N + 1)) :
    (wf N).expect (fun j => het N j) i = (1 - 1 / (N : ℝ)) * het N i := by
  rcases Nat.eq_zero_or_pos N with h0 | hN
  · have : (i : ℕ) = 0 := by omega
    subst h0
    simp [CountKernel.expect, het, wf_apply]
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have h1 := wf_expect_id N i
  have h2 := wf_expect_sq N i
  unfold CountKernel.expect at h1 h2 ⊢
  have key : ∀ j : Fin (N + 1), wf N i j * het N j =
      (2 / (N : ℝ)) * (wf N i j * j) - (2 / (N : ℝ) ^ 2) * (wf N i j * (j * j)) := by
    intro j
    unfold het
    ring
  simp only [key, sum_sub_distrib, ← mul_sum, h1, h2]
  unfold het
  field_simp
  ring

theorem wf_expectIter_het (N t : ℕ) (i : Fin (N + 1)) :
    (wf N).expectIter t (fun j => het N j) i = (1 - 1 / (N : ℝ)) ^ t * het N i :=
  CountKernel.expectIter_eigen (wf N) _ _ (wf_expect_het N) t i

theorem moran_expect_het (N : ℕ) (i : Fin (N + 1)) :
    (moran N 1).expect (fun j => het N j) i = (1 - 2 / (N : ℝ) ^ 2) * het N i := by
  rw [moran_expect (fun n => het N n) i, moranUp_one, moranDown_one]
  rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | hpos
  · simp [h0, het]
  · have hc : (((i : ℕ) - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    have hN : 0 < N := by omega
    have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    simp only [het, Nat.cast_add, hc, Nat.cast_one]
    field_simp
    ring

theorem moran_expectIter_het (N t : ℕ) (i : Fin (N + 1)) :
    (moran N 1).expectIter t (fun j => het N j) i = (1 - 2 / (N : ℝ) ^ 2) ^ t * het N i :=
  CountKernel.expectIter_eigen (moran N 1) _ _ (moran_expect_het N) t i

end Rhone.MarkovChain
