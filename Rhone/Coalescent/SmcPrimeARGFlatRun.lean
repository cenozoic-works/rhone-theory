/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitPrefixSupport
public import Rhone.Coalescent.SmcSupport.ARGClockProduct
public import Rhone.Coalescent.SmcSupport.ARGCoordinateDensity

/-! # Flat coordinates of finite ARG event words: step, run, validity, and density -/

@[expose] public section

namespace Rhone.Coalescent.SmcPrime
open MeasureTheory IntervalProcess SmcSupport
open scoped ENNReal

abbrev ARGFlatCoordinate (N : ℕ) :=
  (Fin (N + 1) → Action) × ((Fin (N + 1) → ℝ) × ℝ)

noncomputable def argFlatActionStep (z : AugmentedState) (a : Action)
    (t x : ℝ) : AugmentedState :=
  match a with
  | .inl ij => (atTime t (coalSuccessorNat z.1 ij), (t, .inr (.inl ij)))
  | .inr i => (atTime t (splitSuccessorNat z.1 i x), (t, .inr (.inr (i, x))))

noncomputable def argFlatRun {n : ℕ} (z : AugmentedState) (w : Fin n → Action)
    (τ : Fin n → ℝ) (x : ℝ) : ℕ → AugmentedState
  | 0 => z
  | k + 1 => if hk : k < n then
      argFlatActionStep (argFlatRun z w τ x k) (w ⟨k, hk⟩) (τ ⟨k, hk⟩) x
    else argFlatRun z w τ x k

noncomputable def argFlatRebuild (N : ℕ) (p : ARGFlatCoordinate N) : ARGPrefix (N + 1) :=
  fun k => argFlatRun (initialState N, (0, .inl ())) p.1 p.2.1 p.2.2 k.val

def argFlatActionValid (s : State) : Action → Prop
  | .inl ij => ij.1 < ij.2 ∧ ij.2 < s.2.2.1
  | .inr i => i < s.2.2.1

def argFlatWordOneSplit {n : ℕ} (w : Fin n → Action) : Prop :=
  ∃ j : Fin n, (∃ i, w j = .inr i) ∧
    ∀ k : Fin n, k ≠ j → ∃ ij, w k = .inl ij

noncomputable def argFlatValid (N : ℕ) (p : ARGFlatCoordinate N) : Prop :=
  let h := argFlatRebuild N p
  argFlatWordOneSplit p.1 ∧ p.2.2 ∈ Set.Ioo 0 1 ∧
    (∀ j : Fin (N + 1),
      let z := h ⟨j.val, Finset.mem_Iic.mpr (by have := j.isLt; omega)⟩
      1 < z.1.2.2.1 ∧ argFlatActionValid z.1 (p.1 j) ∧ z.1.1 < p.2.1 j) ∧
    (h ⟨N + 1, Finset.mem_Iic.mpr le_rfl⟩).1.2.2.1 = 1

noncomputable def argFlatDensity (N : ℕ) (R : ℝ) (p : ARGFlatCoordinate N) : ℝ≥0∞ := by
  classical
  let h := argFlatRebuild N p
  let s := fun j : Fin (N + 1) =>
    (h ⟨j.val, Finset.mem_Iic.mpr (by have := j.isLt; omega)⟩).1
  let δ := fun j : Fin (N + 1) => p.2.1 j - (s j).1
  exact if argFlatValid N p then
    ENNReal.ofReal (R / 2 * Real.exp
      (-argCoalExposure s δ - R / 2 * argHullExposure s δ))
  else 0

theorem argFlatActionStep_fixed_measurable (a : Action) :
    Measurable (fun p : AugmentedState × (ℝ × ℝ) => argFlatActionStep p.1 a p.2.1 p.2.2) := by
  cases a with
  | inl ij =>
    have hs : Measurable (fun p : AugmentedState × (ℝ × ℝ) =>
        coalSuccessorNat p.1.1 ij) :=
      (coalSuccessorNat_fixed_measurable ij).comp measurable_fst.fst
    exact (measurable_snd.fst.prodMk hs.snd).prodMk
      (measurable_snd.fst.prodMk measurable_const)
  | inr i =>
    have hs : Measurable (fun p : AugmentedState × (ℝ × ℝ) =>
        splitSuccessorNat p.1.1 i p.2.2) := (splitSuccessorNat_fixed_measurable i).comp
      (measurable_fst.fst.prodMk measurable_snd.snd)
    exact (measurable_snd.fst.prodMk hs.snd).prodMk
      (measurable_snd.fst.prodMk (measurable_inr.comp
        (measurable_inr.comp (measurable_const.prodMk measurable_snd.snd))))

theorem argFlatRun_eval_measurable {n : ℕ} (z : AugmentedState) (w : Fin n → Action) (k : ℕ) :
    Measurable (fun p : (Fin n → ℝ) × ℝ => argFlatRun z w p.1 p.2 k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    by_cases hk : k < n
    · simpa only [argFlatRun, dite_eq_left hk, Function.comp_def] using
        (argFlatActionStep_fixed_measurable (w ⟨k, hk⟩)).comp
          (ih.prodMk (((measurable_pi_apply ⟨k, hk⟩).comp measurable_fst).prodMk measurable_snd))
    · simpa only [argFlatRun, dite_eq_right hk] using ih

theorem argFlatRebuild_measurable (N : ℕ) : Measurable (argFlatRebuild N) := by
  apply measurable_from_prod_countable_right
  intro w
  exact measurable_pi_iff.mpr fun k =>
    argFlatRun_eval_measurable (initialState N, (0, .inl ())) w k.val
end Rhone.Coalescent.SmcPrime
