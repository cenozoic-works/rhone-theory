/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.GeneratorValid

/-! # Nonnegativity of the proposed first-event and two-event densities -/

@[expose] public section

open scoped Matrix Matrix.Norms.Operator
open Finset
namespace Rhone.Statistics.Identifiability

theorem matrix_mul_nonneg {a b d : Nat}
    (A : Matrix (Fin a) (Fin b) ℝ) (B : Matrix (Fin b) (Fin d) ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j) :
    ∀ i j, 0 ≤ (A * B) i j := by
  intro i j
  simp only [Matrix.mul_apply]
  exact sum_nonneg (fun k _ => mul_nonneg (hA i k) (hB k j))

theorem matrix_mulVec_nonneg {a b : Nat}
    (A : Matrix (Fin a) (Fin b) ℝ) (v : Fin b → ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hv : ∀ i, 0 ≤ v i) :
    ∀ i, 0 ≤ (A *ᵥ v) i := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact sum_nonneg (fun j _ => mul_nonneg (hA i j) (hv j))

theorem pairDensity_nonneg {c : ℝ} (hc : 0 ≤ c) : ∀ i, 0 ≤ MarkovChain.Identifiability.pairDensity c
    i := by
  intro i
  fin_cases i
  · exact hc
  · exact le_refl 0

theorem upperDensity_nonneg (k : Nat) {c q r s t : ℝ}
    (hc : 0 ≤ c) (hq : 0 ≤ q) (hr : 0 ≤ r) (hs : 0 ≤ s) (hst : s ≤ t) :
    0 ≤ upperDensity k c q r s t := by
  apply matrix_mulVec_nonneg _ _ _ (pairDensity_nonneg hc) 0
  apply matrix_mul_nonneg
  · exact matrix_mul_nonneg _ _
      (exp_generator_nonneg _ (generator_metzler k hc hq hr) hs)
      (firstAKernel_nonneg hc)
  · exact exp_generator_nonneg _ (pairGenerator_metzler k hq) (sub_nonneg.mpr hst)

theorem firstAJet_nonneg (k : Nat) {c q r t : ℝ}
    (hc : 0 ≤ c) (hq : 0 ≤ q) (hr : 0 ≤ r) (ht : 0 ≤ t) :
    0 ≤ firstAJet k c q r 0 t := by
  change 0 ≤ ((MarkovChain.Identifiability.generator k c q r ^ 0 * NormedSpace.exp
      (t • MarkovChain.Identifiability.generator k c q r)) *ᵥ MarkovChain.Identifiability.firstA c)
      0
  rw [pow_zero, Matrix.one_mul]
  exact matrix_mulVec_nonneg _ _
    (exp_generator_nonneg _ (generator_metzler k hc hq hr) ht)
    (fun i => mul_nonneg hc (Nat.cast_nonneg _)) 0

end Rhone.Statistics.Identifiability
