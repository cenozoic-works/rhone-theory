/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeARGPairWordLaw
public import Rhone.Coalescent.SmcPrimeARGClockAppend

/-! # Flat-coordinate integral over one-split finite event words -/

@[expose] public section

namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport MeasureTheory
open scoped ENNReal

def argWordOneSplit (n : ℕ) (w : ℕ → Action) : Prop :=
  ∃ j, j < n ∧ (∃ i, w j = .inr i) ∧ ∀ k < n, k ≠ j → ∃ ij, w k = .inl ij

theorem argOneWord_flat_lintegral (R : ℝ) (hR : 0 ≤ R) (z : AugmentedState)
    (w : ℕ → Action) (n : ℕ) (hw : argWordOneSplit n w)
    (f : ARGPrefix n → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ h, f h ∂argWordPrefixLaw R z n w) =
      ∫⁻ p : (Fin n → ℝ) × ℝ,
        argWordWeight R z w n p.1 p.2 * f (argWordRebuild z w n p.1 p.2) := by
  induction n with
  | zero => obtain ⟨j, hj, _⟩ := hw; omega
  | succ n ih =>
    obtain ⟨j, hj, ⟨i, hi⟩, hp⟩ := hw
    let g : ARGPrefix n → ℝ≥0∞ := fun h => ∫⁻ y, f (argPrefixJoin n (h, y))
      ∂argNaturalTransition R (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩) (w n)
    have hg : Measurable g := argWordNextIntegral_measurable R hR n (w n) f hf
    rw [argWordPrefixLaw_lintegral_succ R hR z n w f hf]
    by_cases hjn : j < n
    · have hw' : argWordOneSplit n w :=
        ⟨j, hjn, ⟨i, hi⟩, fun k hk hkj => hp k (by omega) hkj⟩
      obtain ⟨ij, hij⟩ := hp n (Nat.lt_succ_self n) (by omega)
      rw [ih hw' g hg, argMarkedClocks_lintegral_snoc_pair n
        (fun p => argWordWeight R z w (n + 1) p.1 p.2 * f (argWordRebuild z w (n + 1) p.1 p.2))
        (argWordIntegrand_measurable R z w (n + 1) f hf)]
      apply lintegral_congr
      intro p
      change argWordWeight R z w n p.1 p.2 * (∫⁻ y, f (argPrefixJoin n (_, y))
        ∂argNaturalTransition R _ (w n)) = _
      rw [hij, argNaturalPair_flat_lintegral R _ ij
        (fun y => f (argPrefixJoin n (argWordRebuild z w n p.1 p.2, y)))
        (argPrefixJoin_observe_measurable n (argWordRebuild z w n p.1 p.2) f hf),
        ← lintegral_const_mul' _ _ (argWordWeight_ne_top R z w n p.1 p.2)]
      apply lintegral_congr
      intro t
      rw [argWordWeight_snoc, argWordRebuild_snoc, hij]
      simp only [argFlatActionWeight, argFlatActionStep]
      rw [mul_assoc]
    · have hje : j = n := by omega
      have hwi : w n = .inr i := hje ▸ hi
      have hw' : ∀ k < n, ∃ ij, w k = .inl ij :=
        fun k hk => hp k (by omega) (by omega)
      rw [argPairWord_flat_lintegral R hR z w n hw' g hg,
        argMarkedClocks_lintegral_snoc n
          (fun p => argWordWeight R z w (n + 1) p.1 p.2 * f (argWordRebuild z w (n + 1) p.1 p.2))
          (argWordIntegrand_measurable R z w (n + 1) f hf)]
      apply lintegral_congr
      intro τ
      change argWordWeight R z w n τ 0 * (∫⁻ y, f (argPrefixJoin n (_, y))
        ∂argNaturalTransition R _ (w n)) = _
      rw [hwi, argNaturalSplit_flat_lintegral R _ i
        (fun y => f (argPrefixJoin n (argWordRebuild z w n τ 0, y)))
        (argPrefixJoin_observe_measurable n (argWordRebuild z w n τ 0) f hf),
        ← lintegral_const_mul' _ _ (argWordWeight_ne_top R z w n τ 0)]
      apply lintegral_congr
      intro p
      rw [argWordWeight_snoc, argWordRebuild_snoc,
        argWordWeight_pair_cut_eq R z w n hw' τ p.2 0,
        argWordRebuild_pair_cut_eq z w n hw' τ p.2 0, hwi]
      simp only [argFlatActionWeight]
      rw [mul_assoc]
end Rhone.Coalescent.SmcPrime
