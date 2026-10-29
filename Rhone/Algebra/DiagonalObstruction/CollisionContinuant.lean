/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.RecombinationExpansion.Usmani

/-! # A division-free identity for two marked tridiagonal indices -/

@[expose] public section

namespace Rhone.Algebra.DiagonalObstruction
open LinearAlgebra.Tridiag LinearAlgebra.RecombinationExpansion
variable {R : Type*} [CommRing R]

def intervalContinuant (d b c : ℕ → R) (s k : ℕ) : R :=
  cont (fun t => d (s + t)) (fun t => b (s + t)) (fun t => c (s + t)) k

private theorem intervalContinuant_step (d b c : ℕ → R) (s k : ℕ) :
    intervalContinuant d b c s (k + 2) =
      d (s + k + 1) * intervalContinuant d b c s (k + 1) -
        b (s + k) * c (s + k) * intervalContinuant d b c s k := by
  simp only [intervalContinuant, cont, Nat.add_assoc]

private theorem collision_continuant_offset (d b c : ℕ → R) (n i : ℕ) :
    ∀ k, i + k + 1 < n →
      cont d b c n * intervalContinuant d b c (i + 1) k =
        cont d b c (i + k + 1) * Qc d b c n (i + 1) -
          runProd (fun t => b t * c t) i (i + k + 1) * cont d b c i *
            Qc d b c n (i + k + 2) := by
  intro k
  induction k using Nat.twoStepInduction with
  | zero =>
    intro hn
    simp only [Nat.add_zero, intervalContinuant, cont, mul_one]
    rw [runProd_succ_right _ (le_refl i), runProd_self, one_mul]
    exact (cont_mul_Qc' d b c (by omega : i < n)).symm
  | one =>
    intro hn
    have h0 := (cont_mul_Qc' d b c (by omega : i < n)).symm
    have hq := Qc_rec d b c (by omega : i + 1 < n)
    have hp : runProd (fun t => b t * c t) i (i + 1 + 1) =
        (b i * c i) * (b (i + 1) * c (i + 1)) := by
      rw [runProd_succ_right _ (by omega : i ≤ i + 1),
        runProd_succ_right _ (le_refl i), runProd_self, one_mul]
    simp only [intervalContinuant, cont, Nat.add_zero]
    rw [hp]
    simp only [Nat.add_assoc, Nat.reduceAdd] at hq ⊢
    linear_combination d (i + 1) * h0 + (b i * c i * cont d b c i) * hq
  | more k ih0 ih1 =>
    intro hn
    have h0 := ih0 (by omega)
    have h1 := ih1 (by omega)
    have hq := Qc_rec d b c (by omega : i + k + 2 < n)
    have hp0 : runProd (fun t => b t * c t) i (i + (k + 1) + 1) =
        runProd (fun t => b t * c t) i (i + k + 1) *
          (b (i + k + 1) * c (i + k + 1)) := by
      convert runProd_succ_right (fun t => b t * c t) (by omega : i ≤ i + k + 1) using 1
    have hp1 : runProd (fun t => b t * c t) i (i + (k + 2) + 1) =
        runProd (fun t => b t * c t) i (i + k + 2) *
          (b (i + k + 2) * c (i + k + 2)) := by
      convert runProd_succ_right (fun t => b t * c t) (by omega : i ≤ i + k + 2) using 1
    have hL : cont d b c (i + (k + 2) + 1) =
        d (i + k + 2) * cont d b c (i + k + 2) -
          b (i + k + 1) * c (i + k + 1) * cont d b c (i + k + 1) := by
      convert (show cont d b c ((i + k + 1) + 2) =
        d ((i + k + 1) + 1) * cont d b c ((i + k + 1) + 1) -
          b (i + k + 1) * c (i + k + 1) * cont d b c (i + k + 1) from rfl) using 1
    rw [intervalContinuant_step, hL, hp1]
    rw [show i + 1 + k + 1 = i + k + 2 from by omega,
      show i + 1 + k = i + k + 1 from by omega]
    simp only [Nat.add_assoc, Nat.reduceAdd] at h0 h1 hq hp0 ⊢
    rw [hp0] at h1 ⊢
    linear_combination d (i + (k + 2)) * h1 -
      (b (i + (k + 1)) * c (i + (k + 1))) * h0 +
      (runProd (fun t => b t * c t) i (i + (k + 1)) *
        (b (i + (k + 1)) * c (i + (k + 1))) * cont d b c i) * hq

theorem cont_mul_interval_eq (d b c : ℕ → R) {n i j : ℕ} (hij : i < j) (hjn : j < n) :
    cont d b c n * intervalContinuant d b c (i + 1) (j - i - 1) =
      cont d b c j * Qc d b c n (i + 1) -
        runProd (fun t => b t * c t) i j * cont d b c i * Qc d b c n (j + 1) := by
  have h := collision_continuant_offset d b c n i (j - i - 1) (by omega)
  simpa only [show i + (j - i - 1) + 1 = j from by omega,
    show i + (j - i - 1) + 2 = j + 1 from by omega] using h

end Rhone.Algebra.DiagonalObstruction
