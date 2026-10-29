/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.FisherFundamental
public import Rhone.Statistics.Fisher
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Logic.Equiv.Defs

/-!
# Executable Fisher partial change and variance equal the specification

Source: ewens_lessard2015, p. 61, eq. 11–13; ewens1989, pp. 175–177, eq. (22)–(28). -/

@[expose] public section
namespace Rhone.Computation.FisherFundamental
open Finset Rhone.Dynamics Statistics

theorem cast_sumBy {α : Type} (f : α → Rat) (l : List α) :
    ((sumBy f l : Rat) : ℝ) = ∑ i : Fin l.length, ((f l[i.1] : Rat) : ℝ) := by
  induction l with
  | nil => simp [sumBy]
  | cons x xs ih =>
    rw [sumBy, Rat.cast_add, ih]
    exact (Fin.sum_univ_succ (n := xs.length) (fun i : Fin (xs.length + 1) =>
      ((f (x :: xs)[i.1] : Rat) : ℝ))).symm

theorem cast_sumTo (f : Nat → Rat) (n : Nat) :
    ((sumTo f n : Rat) : ℝ) = ∑ i : Fin n, ((f i.1 : Rat) : ℝ) := by
  induction n with
  | zero => simp [sumTo]
  | succ n ih =>
    rw [sumTo, Rat.cast_add, ih, Fin.sum_univ_castSucc]
    simp

def pReal (gs : List Genotype) : Fin gs.length → ℝ := fun i => ((gs[i.1]).p : ℝ)

def wReal (gs : List Genotype) : Fin gs.length → ℝ := fun i => ((gs[i.1]).W : ℝ)

def xReal (gs : List Genotype) (m : Nat) : Fin gs.length → Fin m → ℝ :=
  fun i k => ((count gs[i.1] k.1 : Rat) : ℝ)

def bReal (β : List Rat) : Fin β.length → ℝ := fun k => ((β.getD k.1 0 : Rat) : ℝ)

theorem cast_meanFitness (gs : List Genotype) :
    ((meanFitness gs : Rat) : ℝ) = wMean (pReal gs) (wReal gs) := by
  unfold meanFitness wMean
  rw [cast_sumBy]
  simp [pReal, wReal]

theorem cast_score (gs : List Genotype) (β : List Rat) (i : Fin gs.length) :
    ((score β gs[i.1] : Rat) : ℝ) = fisherScore (xReal gs β.length) (bReal β) i := by
  unfold score fisherScore
  rw [cast_sumTo]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [xReal, bReal]

theorem cast_alleleFreq (gs : List Genotype) {m : Nat} (k : Fin m) :
    ((alleleFreq gs k.1 : Rat) : ℝ) =
      fisherAlleleFreq (pReal gs) (xReal gs m) k := by
  unfold alleleFreq fisherAlleleFreq wMean
  rw [Rat.cast_div, cast_sumBy]
  simp [pReal, xReal]

theorem cast_selectedFreq (gs : List Genotype) {m : Nat} (k : Fin m) :
    ((selectedFreq gs k.1 : Rat) : ℝ) =
      fisherSelectedAlleleFreq (pReal gs) (wReal gs) (xReal gs m) k := by
  unfold selectedFreq fisherSelectedAlleleFreq fisherAlleleFreq haploidStep wMean
  rw [Rat.cast_div, cast_sumBy]
  simp only [Rat.cast_mul, Rat.cast_div, cast_meanFitness, Rat.cast_ofNat]
  simp [pReal, wReal, xReal, wMean]

theorem partialChange_eq (gs : List Genotype) (β : List Rat)
    (h : meanFitness gs ≠ 0) :
    ∃ q : Rat, partialChange gs β = some q ∧
      (q : ℝ) = fisherPartial (pReal gs) (wReal gs) (xReal gs β.length) (bReal β) := by
  refine ⟨2 * sumTo (fun k => (selectedFreq gs k - alleleFreq gs k) * β.getD k 0) β.length,
    by simp [partialChange, h], ?_⟩
  unfold fisherPartial
  rw [Rat.cast_mul, cast_sumTo, Rat.cast_ofNat]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Rat.cast_mul, Rat.cast_sub, cast_selectedFreq, cast_alleleFreq]
  rfl

theorem cast_additiveVar (gs : List Genotype) (β : List Rat) :
    ((additiveVar gs β : Rat) : ℝ) =
      fisherAdditiveVar (pReal gs) (wReal gs) (xReal gs β.length) (bReal β) := by
  unfold additiveVar fisherAdditiveVar wMean
  rw [cast_sumBy]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Rat.cast_mul, Rat.cast_pow, Rat.cast_sub, cast_score, cast_meanFitness]
  rfl

theorem varianceOverMean_eq_none_iff (gs : List Genotype) (β : List Rat) :
    varianceOverMean gs β = none ↔ meanFitness gs = 0 := by
  unfold varianceOverMean
  by_cases h : meanFitness gs = 0 <;> simp [h]

theorem partialChange_eq_none_iff (gs : List Genotype) (β : List Rat) :
    partialChange gs β = none ↔ meanFitness gs = 0 := by
  unfold partialChange
  by_cases h : meanFitness gs = 0 <;> simp [h]

section Fundamental
variable {G K : Type*}

theorem fisherScore_reindex [Fintype K] (X : G → K → ℝ) (β : K → ℝ)
    {S : Type*} [Fintype S] (e : S ≃ K)
    (g : G) :
    fisherScore (fun g s => X g (e s)) (fun s => β (e s)) g = fisherScore X β g := by
  unfold fisherScore
  exact Equiv.sum_comp e (fun k => X g k * β k)

theorem fisherPartial_reindex [Fintype G] [Fintype K] (P W : G → ℝ) (X : G → K → ℝ)
    (β : K → ℝ) {S : Type*}
    [Fintype S] (e : S ≃ K) :
    fisherPartial P W (fun g s => X g (e s)) (fun s => β (e s)) = fisherPartial P W X β := by
  unfold fisherPartial
  congr 1
  exact Equiv.sum_comp e (fun k =>
    (fisherSelectedAlleleFreq P W X k - fisherAlleleFreq P X k) * β k)

theorem fisherAdditiveVar_reindex [Fintype G] [Fintype K] (P W : G → ℝ) (X : G → K → ℝ)
    (β : K → ℝ) {S : Type*}
    [Fintype S] (e : S ≃ K) :
    fisherAdditiveVar P W (fun g s => X g (e s)) (fun s => β (e s)) =
      fisherAdditiveVar P W X β := by
  unfold fisherAdditiveVar
  simp only [fisherScore_reindex X β e]

theorem partialChange_eq_varianceOverMean {L : Type*} {A : L → Type*} [Fintype L] [Nonempty L]
    [∀ l, Fintype (A l)] (gs : List Genotype) (β : List Rat)
    (e : (Σ l, A l) ≃ Fin β.length)
    (hp0 : ∀ i, 0 ≤ pReal gs i) (hp1 : ∑ i, pReal gs i = 1)
    (hW0 : ∀ i, 0 ≤ wReal gs i) (hbar : 0 < wMean (pReal gs) (wReal gs))
    (hX0 : ∀ i s, 0 ≤ xReal gs β.length i (e s))
    (hcopies : ∀ i l, ∑ a, xReal gs β.length i (e ⟨l, a⟩) = 2)
    (hfit : IsFisherLeastSquares (pReal gs) (wReal gs)
      (fun i s => xReal gs β.length i (e s)) (fun s => bReal β (e s))) :
    ∃ q : Rat, partialChange gs β = some q ∧ varianceOverMean gs β = some q := by
  have hm : meanFitness gs ≠ 0 := by
    intro h
    have : ((meanFitness gs : Rat) : ℝ) = 0 := by rw [h]; simp
    rw [cast_meanFitness] at this
    exact hbar.ne' this
  obtain ⟨q, hq, hqe⟩ := partialChange_eq gs β hm
  refine ⟨q, hq, ?_⟩
  have hft := fisher_fundamental_theorem (pReal gs) (wReal gs)
    (fun i s => xReal gs β.length i (e s)) (fun s => bReal β (e s))
    hp0 hp1 hW0 hbar hX0 hcopies hfit
  rw [fisherPartial_reindex (pReal gs) (wReal gs) (xReal gs β.length) (bReal β) e,
    fisherAdditiveVar_reindex (pReal gs) (wReal gs) (xReal gs β.length) (bReal β) e] at hft
  have hr : ((additiveVar gs β / meanFitness gs : Rat) : ℝ) = (q : ℝ) := by
    rw [hqe, hft, Rat.cast_div, cast_additiveVar, cast_meanFitness]
  have hr' : additiveVar gs β / meanFitness gs = q := by exact_mod_cast hr
  simp [varianceOverMean, hm, hr']

end Fundamental

end Rhone.Computation.FisherFundamental
