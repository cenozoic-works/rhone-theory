/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeARGCoordinateWeights

/-! # Flat-coordinate integral over finite event words with a pair step -/

@[expose] public section

namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport MeasureTheory
open scoped ENNReal

theorem argPairWord_flat_lintegral (R : ℝ) (hR : 0 ≤ R) (z : AugmentedState)
    (w : ℕ → Action) (n : ℕ) (hw : ∀ j < n, ∃ ij, w j = .inl ij)
    (f : ARGPrefix n → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ h, f h ∂argWordPrefixLaw R z n w) =
      ∫⁻ τ : Fin n → ℝ, argWordWeight R z w n τ 0 * f (argWordRebuild z w n τ 0) := by
  induction n with
  | zero =>
    have hz (τ : Fin 0 → ℝ) : argWordRebuild z w 0 τ 0 = fun _ => z := by
      funext k
      have hk : k.val = 0 := by have := Finset.mem_Iic.mp k.property; omega
      simp only [argWordRebuild, hk, argFlatRun]
    rw [argWordPrefixLaw_zero, lintegral_dirac' _ hf]
    simp only [argWordWeight, Fin.prod_univ_zero, one_mul, hz]
    rw [Measure.volume_pi_eq_dirac, lintegral_dirac' _ measurable_const]
  | succ n ih =>
    have hw' : ∀ j < n, ∃ ij, w j = .inl ij := fun j hj => hw j (by omega)
    obtain ⟨ij, hij⟩ := hw n (Nat.lt_succ_self n)
    let g : ARGPrefix n → ℝ≥0∞ := fun h => ∫⁻ y, f (argPrefixJoin n (h, y))
      ∂argNaturalTransition R (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩) (w n)
    have hg : Measurable g := argWordNextIntegral_measurable R hR n (w n) f hf
    rw [argWordPrefixLaw_lintegral_succ R hR z n w f hf, ih hw' g hg]
    rw [argClocks_lintegral_snoc n
      (fun τ => argWordWeight R z w (n + 1) τ 0 * f (argWordRebuild z w (n + 1) τ 0))
      (argPairWordIntegrand_measurable R z w (n + 1) f hf)]
    apply lintegral_congr
    intro τ
    change argWordWeight R z w n τ 0 * (∫⁻ y, f (argPrefixJoin n (_, y))
      ∂argNaturalTransition R _ (w n)) = _
    rw [hij, argNaturalPair_flat_lintegral R _ ij
      (fun y => f (argPrefixJoin n (argWordRebuild z w n τ 0, y)))
      (argPrefixJoin_observe_measurable n (argWordRebuild z w n τ 0) f hf),
      ← lintegral_const_mul' _ _ (argWordWeight_ne_top R z w n τ 0)]
    apply lintegral_congr
    intro t
    rw [argWordWeight_snoc, argWordRebuild_snoc, hij]
    simp only [argFlatActionWeight]
    rw [mul_assoc]
end Rhone.Coalescent.SmcPrime
