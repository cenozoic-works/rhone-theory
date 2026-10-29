/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeARGFlatRun
public import Rhone.Coalescent.SmcSupport.ARGWordIntegral

/-! # Appending an event to a flat ARG run and the reconstruction of event words -/

@[expose] public section

namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport MeasureTheory
open scoped ENNReal

noncomputable def argWordRebuild (z : AugmentedState) (w : ℕ → Action) (n : ℕ)
    (τ : Fin n → ℝ) (x : ℝ) : ARGPrefix n :=
  fun k => argFlatRun z (fun j => w j.val) τ x k.val

theorem argWordRebuild_measurable (z : AugmentedState) (w : ℕ → Action) (n : ℕ) :
    Measurable (fun p : (Fin n → ℝ) × ℝ => argWordRebuild z w n p.1 p.2) :=
  measurable_pi_iff.mpr fun k => argFlatRun_eval_measurable z (fun j => w j.val) k.val

theorem argFlatRun_snoc (z : AugmentedState) (w : ℕ → Action) (n : ℕ)
    (τ : Fin n → ℝ) (t x : ℝ) (k : ℕ) (hk : k ≤ n) :
    argFlatRun z (fun j : Fin (n + 1) => w j.val) (Fin.snoc τ t) x k =
      argFlatRun z (fun j : Fin n => w j.val) τ x k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hkn : k < n := by omega
    have hkn' : k < n + 1 := by omega
    rw [argFlatRun, dite_eq_left hkn', argFlatRun, dite_eq_left hkn]
    rw [ih (by omega)]
    have he : (⟨k, hkn'⟩ : Fin (n + 1)) = (⟨k, hkn⟩ : Fin n).castSucc := rfl
    rw [he, Fin.snoc_castSucc]
    rfl

theorem argWordRebuild_snoc (z : AugmentedState) (w : ℕ → Action) (n : ℕ)
    (τ : Fin n → ℝ) (t x : ℝ) :
    argWordRebuild z w (n + 1) (Fin.snoc τ t) x =
      argPrefixJoin n (argWordRebuild z w n τ x,
        argFlatActionStep ((argWordRebuild z w n τ x) ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
          (w n) t x) := by
  funext k
  by_cases hk : k.val ≤ n
  · simpa only [argWordRebuild, argPrefixJoin, dite_eq_left hk] using
      argFlatRun_snoc z w n τ t x k.val hk
  · have he : k.val = n + 1 := by have := Finset.mem_Iic.mp k.property; omega
    simp only [argPrefixJoin, dite_eq_right hk, argWordRebuild, he]
    rw [argFlatRun, dite_eq_left (Nat.lt_succ_self n),
      argFlatRun_snoc z w n τ t x n le_rfl]
    simp [Fin.snoc]

theorem argFlatRun_pair_cut_eq (z : AugmentedState) (w : ℕ → Action) (n : ℕ)
    (hw : ∀ j < n, ∃ ij, w j = .inl ij) (τ : Fin n → ℝ) (x y : ℝ)
    (k : ℕ) :
    argFlatRun z (fun j => w j.val) τ x k =
      argFlatRun z (fun j => w j.val) τ y k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    by_cases hk : k < n
    · obtain ⟨ij, hij⟩ := hw k hk
      simp only [argFlatRun, dite_eq_left hk, ih, hij, argFlatActionStep]
    · simp only [argFlatRun, dite_eq_right hk, ih]

theorem argWordRebuild_pair_cut_eq (z : AugmentedState) (w : ℕ → Action) (n : ℕ)
    (hw : ∀ j < n, ∃ ij, w j = .inl ij) (τ : Fin n → ℝ) (x y : ℝ) :
    argWordRebuild z w n τ x = argWordRebuild z w n τ y := by
  funext k
  exact argFlatRun_pair_cut_eq z w n hw τ x y k.val

theorem argClocks_lintegral_snoc (n : ℕ) (f : (Fin (n + 1) → ℝ) → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ τ, f τ) = ∫⁻ τ : Fin n → ℝ, ∫⁻ t : ℝ, f (Fin.snoc τ t) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)
  have he (p : ℝ × (Fin n → ℝ)) : e.symm p = Fin.snoc p.2 p.1 := by
    apply e.injective
    simp [e, MeasurableEquiv.piFinSuccAbove]
  rw [(volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ)
    (Fin.last n)).symm.lintegral_map_equiv (f := f)]
  change (∫⁻ p : ℝ × (Fin n → ℝ), f (e.symm p)) = _
  simp only [he]
  rw [Measure.volume_eq_prod, lintegral_prod _ (by
    simpa only [Function.comp_def, Function.uncurry_def, he] using
      (hf.comp e.symm.measurable).aemeasurable)]
  exact lintegral_lintegral_swap (by
    simpa only [Function.comp_def, Function.uncurry_def, he] using
      (hf.comp e.symm.measurable).aemeasurable)
end Rhone.Coalescent.SmcPrime
