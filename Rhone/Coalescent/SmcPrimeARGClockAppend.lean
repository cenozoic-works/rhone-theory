/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeARGWordRebuild

/-! # Appending a clock coordinate to the marked-clock integral of the ARG recursion -/

@[expose] public section

namespace Rhone.Coalescent.SmcPrime
open MeasureTheory
open scoped ENNReal

theorem argClocks_snoc_measurable (n : ℕ) :
    Measurable (fun p : (Fin n → ℝ) × ℝ => (Fin.snoc p.1 p.2 : Fin (n + 1) → ℝ)) := by
  apply measurable_pi_iff.mpr
  intro k
  by_cases hk : k.val < n
  · simpa only [Fin.snoc, dite_eq_left hk, cast_eq, Function.comp_def] using
      (measurable_pi_apply (Fin.castLT k hk)).comp measurable_fst
  · simpa only [Fin.snoc, dite_eq_right hk, cast_eq] using
      (measurable_snd : Measurable (fun p : (Fin n → ℝ) × ℝ => p.2))

theorem argMarkedClocks_lintegral_snoc (n : ℕ)
    (f : ((Fin (n + 1) → ℝ) × ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ p, f p) = ∫⁻ τ : Fin n → ℝ, ∫⁻ p : ℝ × ℝ, f (Fin.snoc τ p.1, p.2) := by
  rw [Measure.volume_eq_prod, lintegral_prod _ hf.aemeasurable,
    argClocks_lintegral_snoc n _ hf.lintegral_prod_right']
  apply lintegral_congr
  intro τ
  rw [Measure.volume_eq_prod, lintegral_prod _]
  exact (hf.comp (((argClocks_snoc_measurable n).comp
    (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)).aemeasurable

theorem argMarkedClocks_lintegral_snoc_pair (n : ℕ)
    (f : ((Fin (n + 1) → ℝ) × ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ p, f p) = ∫⁻ p : (Fin n → ℝ) × ℝ, ∫⁻ t : ℝ, f (Fin.snoc p.1 t, p.2) := by
  have hg : Measurable (fun p : ((Fin n → ℝ) × ℝ) × ℝ =>
      f (Fin.snoc p.1.1 p.2, p.1.2)) :=
    hf.comp (((argClocks_snoc_measurable n).comp
      (measurable_fst.fst.prodMk measurable_snd)).prodMk measurable_fst.snd)
  rw [argMarkedClocks_lintegral_snoc n f hf]
  conv_rhs => rw [Measure.volume_eq_prod, lintegral_prod _ hg.lintegral_prod_right'.aemeasurable]
  apply lintegral_congr
  intro τ
  have hm : Measurable (fun p : ℝ × ℝ => f (Fin.snoc τ p.1, p.2)) :=
    hf.comp (((argClocks_snoc_measurable n).comp
      (measurable_const.prodMk measurable_fst)).prodMk measurable_snd)
  rw [Measure.volume_eq_prod, lintegral_prod _ hm.aemeasurable]
  exact lintegral_lintegral_swap hm.aemeasurable

end Rhone.Coalescent.SmcPrime
