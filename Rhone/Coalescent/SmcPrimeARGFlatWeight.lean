/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeARGWordSectors
public import Rhone.Coalescent.SmcPrimeARGPreSplitMaterial

/-! # Flat weight of finite ARG event words, vanishing on invalid coordinates -/

@[expose] public section

namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport MeasureTheory
open scoped ENNReal

noncomputable def argFlatWeight (N : ℕ) (R : ℝ) (p : ARGFlatCoordinate N) : ℝ≥0∞ :=
  ∏ j : Fin (N + 1), argFlatActionWeight R
    (argFlatRun (initialState N, (0, .inl ())) p.1 p.2.1 p.2.2 j.val)
      (p.1 j) (p.2.1 j) p.2.2

theorem argFiniteWord_function {n : ℕ} (w : Fin n → Action) :
    (fun j : Fin n => argFiniteWord w j.val) = w :=
  funext (argFiniteWord_eval w)

theorem argFlatWeight_eq_word (N : ℕ) (R : ℝ) (p : ARGFlatCoordinate N) :
    argFlatWeight N R p =
      argWordWeight R (initialState N, (0, .inl ())) (argFiniteWord p.1) (N + 1) p.2.1 p.2.2 := by
  unfold argWordWeight argFlatWeight
  rw [argFiniteWord_function]
  simp only [argFiniteWord_eval]

theorem argFlatRebuild_eq_word (N : ℕ) (p : ARGFlatCoordinate N) :
    argFlatRebuild N p =
      argWordRebuild (initialState N, (0, .inl ())) (argFiniteWord p.1) (N + 1) p.2.1 p.2.2 := by
  unfold argWordRebuild argFlatRebuild
  rw [argFiniteWord_function]

theorem argFlatActionWeight_invalid (R : ℝ) (z : AugmentedState) (a : Action) (t x : ℝ)
    (hv : ¬(1 < z.1.2.2.1 ∧ argFlatActionValid z.1 a ∧ z.1.1 < t)) :
    argFlatActionWeight R z a t x = 0 := by
  cases a with
  | inl ij =>
    simp only [argFlatActionWeight, argFlatPairWeight]
    apply ite_eq_right
    intro h
    exact hv ⟨h.1, ⟨h.2.1, h.2.2.1⟩, h.2.2.2⟩
  | inr i =>
    simp only [argFlatActionWeight, argFlatSplitWeight]
    apply ite_eq_right
    intro h
    exact hv ⟨h.1, h.2.1, h.2.2.1⟩

theorem argFlatWeight_cut_zero (N : ℕ) (R : ℝ) (p : ARGFlatCoordinate N)
    (hw : argFlatWordOneSplit p.1) (hx : p.2.2 ∉ Set.Ioo 0 1) :
    argFlatWeight N R p = 0 := by
  classical
  obtain ⟨s, ⟨i, hi⟩, hp⟩ := hw
  apply Finset.prod_eq_zero (Finset.mem_univ s)
  rw [hi]
  simp only [argFlatActionWeight, argFlatSplitWeight]
  apply ite_eq_right
  intro h
  obtain ⟨hlo, hhi⟩ := argFlatRun_split_hull N p.1 p.2.1 p.2.2 s hp i h.2.1
  exact hx ⟨hlo ▸ h.2.2.2.1, hhi ▸ h.2.2.2.2⟩

theorem argFlatWeight_event_zero (N : ℕ) (R : ℝ) (p : ARGFlatCoordinate N)
    (j : Fin (N + 1))
    (hv : ¬(1 < (argFlatRebuild N p
        ⟨j.val, Finset.mem_Iic.mpr (by have := j.isLt; omega)⟩).1.2.2.1 ∧
      argFlatActionValid
        (argFlatRebuild N p ⟨j.val, Finset.mem_Iic.mpr (by have := j.isLt; omega)⟩).1
        (p.1 j) ∧
      (argFlatRebuild N p ⟨j.val, Finset.mem_Iic.mpr (by have := j.isLt; omega)⟩).1.1 < p.2.1 j)) :
    argFlatWeight N R p = 0 := by
  classical
  exact Finset.prod_eq_zero (Finset.mem_univ j)
    (argFlatActionWeight_invalid R _ _ _ _ hv)

theorem argFlatWeight_valid (N : ℕ) (R : ℝ) (hR : 0 ≤ R) (p : ARGFlatCoordinate N)
    (hv : argFlatValid N p) :
    argFlatWeight N R p = argFlatDensity N R p := by
  classical
  obtain ⟨s, ⟨i, hi⟩, hp⟩ := hv.1
  let z : Fin (N + 1) → AugmentedState := fun j =>
    argFlatRun (initialState N, (0, .inl ())) p.1 p.2.1 p.2.2 j.val
  have he (j : Fin (N + 1)) : argFlatActionWeight R (z j) (p.1 j) (p.2.1 j) p.2.2 =
      (if j = s then ENNReal.ofReal (R / 2) else 1) *
        ENNReal.ofReal (Real.exp (-(totalRate false R (z j).1 : ℝ) * (p.2.1 j - (z j).1.1))) := by
    have hj := hv.2.2.1 j
    change 1 < (z j).1.2.2.1 ∧ argFlatActionValid (z j).1 (p.1 j) ∧ (z j).1.1 < p.2.1 j at hj
    by_cases hjs : j = s
    · subst j
      rw [hi] at hj ⊢
      obtain ⟨hlo, hhi⟩ := argFlatRun_split_hull N p.1 p.2.1 p.2.2 s hp i hj.2.1
      change lineageHullEndpoint false (z s).1 i = 0 at hlo
      change lineageHullEndpoint true (z s).1 i = 1 at hhi
      have hib : i < (z s).1.2.2.1 := hj.2.1
      simp only [argFlatActionWeight, argFlatSplitWeight, hlo, hhi]
      rw [ite_eq_left ⟨hj.1, hib, hj.2.2, hv.2.1.1, hv.2.1.2⟩, ite_true]
      rw [ENNReal.ofReal_mul (by positivity)]
    · obtain ⟨ij, hij⟩ := hp j hjs
      rw [hij] at hj ⊢
      simp only [argFlatActionWeight, argFlatPairWeight, argFlatActionValid] at hj ⊢
      simp only [hj.1, hj.2.1.1, hj.2.1.2, hj.2.2, and_self, ite_true,
        ite_eq_right hjs, one_mul]
  change (∏ j, argFlatActionWeight R (z j) (p.1 j) (p.2.1 j) p.2.2) = _
  rw [Finset.prod_congr rfl (fun j _ => he j), Finset.prod_mul_distrib,
    Fintype.prod_ite_eq', ← ENNReal.ofReal_prod_of_nonneg (fun _ _ => Real.exp_nonneg _),
    ← ENNReal.ofReal_mul (by positivity)]
  rw [argClockProduct_factorization R hR (fun j => (z j).1)
    (fun j => p.2.1 j - (z j).1.1)]
  exact (ite_eq_left hv).symm
end Rhone.Coalescent.SmcPrime
