/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeARGActionCoordinates
public import Rhone.Coalescent.SmcPrimeARGWordRebuild

/-! # Weights and measurability of finite event words in flat ARG coordinates -/

@[expose] public section

namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport MeasureTheory
open scoped ENNReal

theorem argTotalRate_measurable (R : ℝ) :
    Measurable (fun s : State => (totalRate false R s : ℝ)) := by
  let f (p : LiveState × (ℝ × ℕ)) := (totalRate false R (p.2.1, p.2.2, p.1) : ℝ)
  have hg (m : ℕ) : Measurable (fun p : (Fin m → ℕ × Material) × (ℝ × ℕ) =>
      f (⟨m, p.1⟩, p.2)) := by
    change Measurable ((fun q : FiberState m => (totalRate false R (stateOfFiber m q) : ℝ)) ∘
      fun p : (Fin m → ℕ × Material) × (ℝ × ℕ) => (p.2.1, p.2.2, p.1))
    exact (totalRateFiber_coe_measurable false R m).comp
      (measurable_snd.fst.prodMk (measurable_snd.snd.prodMk measurable_fst))
  have hf : Measurable f := measurable_prod_sigma_of_fibers f hg
  change Measurable (f ∘ fun s : State => (s.2.2, (s.1, s.2.1)))
  exact hf.comp (measurable_snd.snd.prodMk (measurable_fst.prodMk measurable_snd.fst))

noncomputable def argFlatActionWeight (R : ℝ) (z : AugmentedState) (a : Action)
    (t x : ℝ) : ℝ≥0∞ :=
  match a with
  | .inl ij => argFlatPairWeight R z ij t
  | .inr i => argFlatSplitWeight R z i (t, x)

noncomputable def argWordWeight (R : ℝ) (z : AugmentedState) (w : ℕ → Action)
    (n : ℕ) (τ : Fin n → ℝ) (x : ℝ) : ℝ≥0∞ :=
  ∏ j : Fin n, argFlatActionWeight R
    (argFlatRun z (fun k => w k.val) τ x j.val) (w j.val) (τ j) x

theorem argFlatPairWeight_measurable (R : ℝ) (ij : ℕ × ℕ) :
    Measurable (fun p : AugmentedState × ℝ => argFlatPairWeight R p.1 ij p.2) := by
  classical
  unfold argFlatPairWeight
  apply Measurable.ite _ _ measurable_const
  · have hc : Measurable (fun p : AugmentedState × ℝ => p.1.1.2.2.1) :=
      IntervalProcess.liveCount_measurable.comp measurable_fst.fst
    have ht : Measurable (fun p : AugmentedState × ℝ => p.1.1.1) :=
      measurable_fst.fst.fst
    exact (measurableSet_lt (measurable_const (a := (1 : ℕ))) hc).inter
      ((MeasurableSet.const (ij.1 < ij.2)).inter
        ((measurableSet_lt (measurable_const (a := ij.2)) hc).inter
          (measurableSet_lt ht measurable_snd)))
  · exact ENNReal.measurable_ofReal.comp
      (((argTotalRate_measurable R).comp measurable_fst.fst).neg.mul
        (measurable_snd.sub measurable_fst.fst.fst)).exp

theorem argFlatSplitWeight_measurable (R : ℝ) (i : ℕ) :
    Measurable (fun p : AugmentedState × (ℝ × ℝ) => argFlatSplitWeight R p.1 i p.2) := by
  classical
  unfold argFlatSplitWeight
  apply Measurable.ite _ _ measurable_const
  · have hc : Measurable (fun p : AugmentedState × (ℝ × ℝ) => p.1.1.2.2.1) :=
      IntervalProcess.liveCount_measurable.comp measurable_fst.fst
    have ht : Measurable (fun p : AugmentedState × (ℝ × ℝ) => p.1.1.1) :=
      measurable_fst.fst.fst
    have hlo : Measurable (fun p : AugmentedState × (ℝ × ℝ) =>
        lineageHullEndpoint false p.1.1 i) :=
      (lineageHullEndpoint_fixed_measurable false i).comp measurable_fst.fst
    have hhi : Measurable (fun p : AugmentedState × (ℝ × ℝ) =>
        lineageHullEndpoint true p.1.1 i) :=
      (lineageHullEndpoint_fixed_measurable true i).comp measurable_fst.fst
    exact (measurableSet_lt (measurable_const (a := (1 : ℕ))) hc).inter
      ((measurableSet_lt (measurable_const (a := i)) hc).inter
        ((measurableSet_lt ht measurable_snd.fst).inter
          ((measurableSet_lt hlo measurable_snd.snd).inter
            (measurableSet_lt measurable_snd.snd hhi))))
  · exact ENNReal.measurable_ofReal.comp
      (measurable_const.mul
        (((argTotalRate_measurable R).comp measurable_fst.fst).neg.mul
          (measurable_snd.fst.sub measurable_fst.fst.fst)).exp)

theorem argFlatActionWeight_measurable (R : ℝ) (a : Action) :
    Measurable (fun p : AugmentedState × (ℝ × ℝ) =>
      argFlatActionWeight R p.1 a p.2.1 p.2.2) := by
  cases a with
  | inl ij =>
      exact (argFlatPairWeight_measurable R ij).comp
        (measurable_fst.prodMk measurable_snd.fst)
  | inr i => exact argFlatSplitWeight_measurable R i

theorem argWordWeight_measurable (R : ℝ) (z : AugmentedState) (w : ℕ → Action) (n : ℕ) :
    Measurable (fun p : (Fin n → ℝ) × ℝ => argWordWeight R z w n p.1 p.2) := by
  apply Finset.measurable_prod
  intro j _
  exact (argFlatActionWeight_measurable R (w j.val)).comp
    ((argFlatRun_eval_measurable z (fun k => w k.val) j.val).prodMk
      (((measurable_pi_apply j).comp measurable_fst).prodMk measurable_snd))

theorem argFlatActionWeight_ne_top (R : ℝ) (z : AugmentedState) (a : Action) (t x : ℝ) :
    argFlatActionWeight R z a t x ≠ ⊤ := by
  cases a with
  | inl ij =>
      simp only [argFlatActionWeight, argFlatPairWeight]
      split_ifs <;> simp
  | inr i =>
      simp only [argFlatActionWeight, argFlatSplitWeight]
      split_ifs <;> simp

theorem argWordWeight_ne_top (R : ℝ) (z : AugmentedState) (w : ℕ → Action)
    (n : ℕ) (τ : Fin n → ℝ) (x : ℝ) : argWordWeight R z w n τ x ≠ ⊤ :=
  ENNReal.prod_ne_top fun _ _ => argFlatActionWeight_ne_top R _ _ _ _

theorem argWordWeight_snoc (R : ℝ) (z : AugmentedState) (w : ℕ → Action) (n : ℕ)
    (τ : Fin n → ℝ) (t x : ℝ) :
    argWordWeight R z w (n + 1) (Fin.snoc τ t) x = argWordWeight R z w n τ x *
      argFlatActionWeight R ((argWordRebuild z w n τ x) ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
        (w n) t x := by
  unfold argWordWeight
  rw [Fin.prod_univ_castSucc]
  congr 1
  · apply Finset.prod_congr rfl
    intro j _
    simp only [Fin.val_castSucc]
    rw [argFlatRun_snoc z w n τ t x j.val (Nat.le_of_lt j.isLt), Fin.snoc_castSucc]
  · simp only [Fin.val_last]
    rw [argFlatRun_snoc z w n τ t x n le_rfl, Fin.snoc_last]
    rfl

theorem argWordWeight_pair_cut_eq (R : ℝ) (z : AugmentedState) (w : ℕ → Action)
    (n : ℕ) (hw : ∀ j < n, ∃ ij, w j = .inl ij) (τ : Fin n → ℝ) (x y : ℝ) :
    argWordWeight R z w n τ x = argWordWeight R z w n τ y := by
  apply Finset.prod_congr rfl
  intro j _
  obtain ⟨ij, hij⟩ := hw j.val j.isLt
  rw [argFlatRun_pair_cut_eq z w n hw τ x y j.val, hij]
  rfl
theorem argWordIntegrand_measurable (R : ℝ) (z : AugmentedState) (w : ℕ → Action)
    (n : ℕ) (f : ARGPrefix n → ℝ≥0∞) (hf : Measurable f) :
    Measurable (fun p : (Fin n → ℝ) × ℝ =>
      argWordWeight R z w n p.1 p.2 * f (argWordRebuild z w n p.1 p.2)) := by
  have hg : Measurable (fun p : (Fin n → ℝ) × ℝ =>
      f (argWordRebuild z w n p.1 p.2)) := hf.comp (argWordRebuild_measurable z w n)
  exact (argWordWeight_measurable R z w n).mul hg

theorem argPairWordIntegrand_measurable (R : ℝ) (z : AugmentedState) (w : ℕ → Action)
    (n : ℕ) (f : ARGPrefix n → ℝ≥0∞) (hf : Measurable f) :
    Measurable (fun τ : Fin n → ℝ =>
      argWordWeight R z w n τ 0 * f (argWordRebuild z w n τ 0)) := by
  simpa only [Function.comp_def, id_eq] using
    (argWordIntegrand_measurable R z w n f hf).comp
      (measurable_id.prodMk (measurable_const (a := (0 : ℝ))))
end Rhone.Coalescent.SmcPrime
