/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.PositiveForcing
public import Rhone.Statistics.Identifiability.TwoParameterMarkovFlow

/-! # Positive accumulated edge exposure transfers mass in a continuous finite row flow -/

@[expose] public section

open Set Filter MeasureTheory
open scoped BigOperators Topology Matrix
namespace Rhone.Statistics.Identifiability
variable {ι : Type*} [Fintype ι]

theorem inhomogeneous_row_positive_of_edge_exposure
    (Q : ℝ → Matrix ι ι ℝ) (v : ℝ → ι → ℝ)
    (hQ : ∀ i j, Continuous (fun t => Q t i j))
    (hQn : ∀ u, 0 ≤ u → ∀ i j, i ≠ j → 0 ≤ Q u i j)
    (he : ∀ u j, HasDerivAt (fun s => v s j) (∑ i, v u i * Q u i j) u)
    (hvn : ∀ u, 0 ≤ u → ∀ i, 0 ≤ v u i)
    (i j : ι) (hij : i ≠ j) (hvi : 0 < v 0 i) {t : ℝ} (ht : 0 ≤ t)
    (hexp : 0 < ∫ u in (0 : ℝ)..t, Q u i j) : 0 < v t j := by
  classical
  have hvc (l : ι) : Continuous (fun u => v u l) :=
    continuous_iff_continuousAt.mpr fun u => (he u l).continuousAt
  have hvip (u : ℝ) (hu : 0 ≤ u) : 0 < v u i :=
    inhomogeneous_row_coordinate_positive Q v i (hQ i i)
      (fun s hs l hli => hQn s hs l i hli) (fun s _ => he s i) hvn hvi hu
  let b : ℝ → ℝ := fun u => ∑ l ∈ Finset.univ.erase j, v u l * Q u l j
  have hbc : Continuous b := by
    apply continuous_finsetSum
    intro l _
    exact (hvc l).mul (hQ l j)
  have hbn (u : ℝ) (hu : 0 ≤ u) : 0 ≤ b u := by
    apply Finset.sum_nonneg
    intro l hl
    exact mul_nonneg (hvn u hu l) (hQn u hu l j (Finset.mem_erase.mp hl).1)
  have hle (u : ℝ) (hu : 0 ≤ u) : v u i * Q u i j ≤ b u := by
    change v u i * Q u i j ≤ ∑ l ∈ Finset.univ.erase j, v u l * Q u l j
    apply Finset.single_le_sum (s := Finset.univ.erase j)
      (f := fun l => v u l * Q u l j) (a := i)
    · intro l hl
      exact mul_nonneg (hvn u hu l) (hQn u hu l j (Finset.mem_erase.mp hl).1)
    · exact Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩
  have hforced := intervalIntegral_positive_weight (fun u => Q u i j) (fun u => v u i)
    (hQ i j) (hvc i) ht (fun u hu => hQn u hu.1 i j hij)
    (fun u hu => hvip u hu.1) hexp
  have hbint : 0 < ∫ u in (0 : ℝ)..t, b u := hforced.trans_le
    (intervalIntegral.integral_mono_on ht (((hvc i).mul (hQ i j)).intervalIntegrable 0 t)
      (hbc.intervalIntegrable 0 t) (fun u hu => hle u hu.1))
  apply linear_forcing_positive (fun u => Q u j j) b (fun u => v u j)
    (hQ j j) hbc _ ht (hvn 0 le_rfl j) (fun u hu => hbn u hu.1) hbint
  intro u
  convert he u j using 1
  rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ j)]
  change Q u j j * v u j + b u = b u + v u j * Q u j j
  ring

end Rhone.Statistics.Identifiability
