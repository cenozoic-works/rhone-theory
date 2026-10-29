/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.FStatistics
public import Rhone.Statistics.FStatistics
public import Mathlib.Basic.Real.Basic

/-!
# Executable F-statistics equal the specification

Source: wright1951, p. 328, p. 330. -/

@[expose] public section
namespace Rhone.Computation.FStatistics
open Finset Rhone.Dynamics MarkovChain

def wReal (ds : List (Rat × Rat)) : Fin ds.length → ℝ := fun i => ((ds[i.1]).1 : ℝ)

def pReal (ds : List (Rat × Rat)) : Fin ds.length → ℝ := fun i => ((ds[i.1]).2 : ℝ)

theorem cast_sumBy {α : Type} (f : α → Rat) (l : List α) :
    ((sumBy f l : Rat) : ℝ) = ∑ i : Fin l.length, ((f l[i.1] : Rat) : ℝ) := by
  induction l with
  | nil => simp [sumBy]
  | cons x xs ih =>
    rw [sumBy, Rat.cast_add, ih]
    exact (Fin.sum_univ_succ (n := xs.length) (fun i : Fin (xs.length + 1) =>
      ((f (x :: xs)[i.1]  : Rat) : ℝ))).symm

theorem hweHet_eq (p : Rat) :
    ((hweHet p : Rat) : ℝ) = Rhone.Statistics.FStatistics.hweHet (p : ℝ) := by
  simp [hweHet, Rhone.Statistics.FStatistics.hweHet]

theorem fRatio_eq_none_iff (Hobs Href : Rat) : fRatio Hobs Href = none ↔ Href = 0 := by
  unfold fRatio
  by_cases h : Href = 0 <;> simp [h]

theorem fRatio_eq_some (Hobs Href : Rat) (h : Href ≠ 0) :
    ∃ q : Rat, fRatio Hobs Href = some q ∧
      (q : ℝ) = Rhone.Statistics.FStatistics.fRatio (Hobs : ℝ) (Href : ℝ) := by
  refine ⟨1 - Hobs / Href, by simp [fRatio, h], ?_⟩
  simp [Rhone.Statistics.FStatistics.fRatio]

theorem fStatistics_eq_none_iff (HI HS HT : Rat) :
    fStatistics HI HS HT = none ↔ HS = 0 ∨ HT = 0 := by
  unfold fStatistics
  by_cases h : HS = 0 ∨ HT = 0 <;> simp [h]

theorem fStatistics_eq (HI HS HT : Rat) (hHS : HS ≠ 0) (hHT : HT ≠ 0) :
    ∃ a b c : Rat, fStatistics HI HS HT = some (a, b, c) ∧
      (a : ℝ) = Rhone.Statistics.FStatistics.fRatio (HI : ℝ) (HS : ℝ) ∧
      (b : ℝ) = Rhone.Statistics.FStatistics.fRatio (HS : ℝ) (HT : ℝ) ∧
      (c : ℝ) = Rhone.Statistics.FStatistics.fRatio (HI : ℝ) (HT : ℝ) ∧
      1 - c = (1 - a) * (1 - b) := by
  refine ⟨1 - HI / HS, 1 - HS / HT, 1 - HI / HT, by simp [fStatistics, hHS, hHT],
    by simp [Rhone.Statistics.FStatistics.fRatio], by simp [Rhone.Statistics.FStatistics.fRatio],
    by simp [Rhone.Statistics.FStatistics.fRatio], ?_⟩
  have h := Rhone.Statistics.FStatistics.f_statistics_decomposition (HI : ℝ) (HS : ℝ) (HT : ℝ)
    (by exact_mod_cast hHS) (by exact_mod_cast hHT)
  unfold Rhone.Statistics.FStatistics.fRatio at h
  have h' : ((1 - (1 - HI / HT) : Rat) : ℝ) =
      (((1 - (1 - HI / HS)) * (1 - (1 - HS / HT)) : Rat) : ℝ) := by
    push_cast
    exact h
  exact_mod_cast h'

theorem weightedMean_eq (ds : List (Rat × Rat)) :
    ((weightedMean ds : Rat) : ℝ) = wMean (wReal ds) (pReal ds) := by
  unfold weightedMean wMean wReal pReal
  rw [cast_sumBy]
  simp

theorem weightedVariance_eq (ds : List (Rat × Rat)) :
    ((weightedVariance ds : Rat) : ℝ) = wVar (wReal ds) (pReal ds) := by
  have h1 := weightedMean_eq ds
  unfold weightedVariance wVar wCov
  rw [Rat.cast_sub, Rat.cast_mul, h1]
  congr 1
  unfold wMean wReal pReal
  rw [cast_sumBy]
  simp

theorem meanHet_eq (ds : List (Rat × Rat)) :
    ((meanHet ds : Rat) : ℝ) =
      wMean (wReal ds) (fun i => Rhone.Statistics.FStatistics.hweHet (pReal ds i)) := by
  unfold meanHet wMean wReal pReal
  rw [cast_sumBy]
  simp [hweHet, Rhone.Statistics.FStatistics.hweHet]

theorem pooledHet_eq (ds : List (Rat × Rat)) :
    ((pooledHet ds : Rat) : ℝ) =
      Rhone.Statistics.FStatistics.hweHet (wMean (wReal ds) (pReal ds)) := by
  rw [pooledHet, hweHet_eq, weightedMean_eq]

theorem weightsNormalized_iff (ds : List (Rat × Rat)) :
    weightsNormalized ds = true ↔ ∑ i, wReal ds i = 1 := by
  have h : ((sumBy (fun d => d.1) ds : Rat) : ℝ) = ∑ i, wReal ds i := by
    rw [cast_sumBy]
    rfl
  unfold weightsNormalized
  rw [beq_iff_eq, ← h]
  constructor
  · intro h1
    rw [h1]
    simp
  · intro h1
    exact_mod_cast h1

theorem wahlundDeficit_eq (ds : List (Rat × Rat)) (h : weightsNormalized ds = true) :
    ∃ q : Rat, wahlundDeficit ds = some q ∧
      (q : ℝ) = Rhone.Statistics.FStatistics.hweHet (wMean (wReal ds) (pReal ds)) -
        wMean (wReal ds) (fun i => Rhone.Statistics.FStatistics.hweHet (pReal ds i)) := by
  refine ⟨pooledHet ds - meanHet ds, by simp [wahlundDeficit, h], ?_⟩
  rw [Rat.cast_sub, pooledHet_eq, meanHet_eq]

theorem wahlundVarianceForm_eq (ds : List (Rat × Rat)) (h : weightsNormalized ds = true) :
    ∃ v : Rat, wahlundVarianceForm ds = some v ∧
      (v : ℝ) = 2 * wVar (wReal ds) (pReal ds) := by
  refine ⟨2 * weightedVariance ds, by simp [wahlundVarianceForm, h], ?_⟩
  rw [Rat.cast_mul, weightedVariance_eq]
  simp

theorem wahlund_eq_none_iff (ds : List (Rat × Rat)) :
    (wahlundDeficit ds = none ↔ ¬ weightsNormalized ds = true) ∧
      (wahlundVarianceForm ds = none ↔ ¬ weightsNormalized ds = true) := by
  unfold wahlundDeficit wahlundVarianceForm
  by_cases h : weightsNormalized ds = true <;> simp [h]

theorem wahlund_identity_exec (ds : List (Rat × Rat)) (h : weightsNormalized ds = true) :
    ∃ q : Rat, wahlundDeficit ds = some q ∧ wahlundVarianceForm ds = some q := by
  obtain ⟨q, hq, hqe⟩ := wahlundDeficit_eq ds h
  obtain ⟨v, hv, hve⟩ := wahlundVarianceForm_eq ds h
  have hw : ∑ i, wReal ds i = 1 := (weightsNormalized_iff ds).1 h
  have hid := Rhone.Statistics.FStatistics.wahlund_identity (wReal ds) (pReal ds) hw
  have hqv : q = v := by
    have : (q : ℝ) = (v : ℝ) := by rw [hqe, hve, hid]
    exact_mod_cast this
  exact ⟨q, hq, by rw [hv, hqv]⟩

theorem fStWahlund_eq (ds : List (Rat × Rat)) (h : weightsNormalized ds = true)
    (hT : pooledHet ds ≠ 0) :
    ∃ x : Rat, fStWahlund ds = some x ∧
      (x : ℝ) = Rhone.Statistics.FStatistics.fRatio
        (wMean (wReal ds) (fun i => Rhone.Statistics.FStatistics.hweHet (pReal ds i)))
        (Rhone.Statistics.FStatistics.hweHet (wMean (wReal ds) (pReal ds))) := by
  refine ⟨2 * weightedVariance ds / pooledHet ds, by simp [fStWahlund, h, hT], ?_⟩
  have hw : ∑ i, wReal ds i = 1 := (weightsNormalized_iff ds).1 h
  have hid := Rhone.Statistics.FStatistics.wahlund_identity (wReal ds) (pReal ds) hw
  have hT' : Rhone.Statistics.FStatistics.hweHet (wMean (wReal ds) (pReal ds)) ≠ 0 := by
    rw [← pooledHet_eq]
    exact_mod_cast hT
  unfold Rhone.Statistics.FStatistics.fRatio
  rw [Rat.cast_div, Rat.cast_mul, weightedVariance_eq, pooledHet_eq]
  field_simp
  push_cast
  linarith [hid]

end Rhone.Computation.FStatistics
