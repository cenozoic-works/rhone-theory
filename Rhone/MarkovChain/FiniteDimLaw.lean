/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.RateLumpingLaw
public import Mathlib.Probability.Process.FiniteDimensionalLaws

/-! # Finite-dimensional laws of a continuous-time chain, and lumping -/

@[expose] public section

namespace Rhone.MarkovChain

open Finset MeasureTheory
open scoped NNReal ENNReal

section ChainProd

variable {S T : Type*}

def chainProd {k : ℕ} (P : Fin k → Matrix S S ℝ) (x : S) (y : Fin k → S) : ℝ :=
  ∏ i : Fin k, P i ((Fin.cons x y : Fin (k + 1) → S) i.castSucc) (y i)

theorem chainProd_succ {k : ℕ} (P : Fin (k + 1) → Matrix S S ℝ) (x : S) (y : Fin (k + 1) → S) :
    chainProd P x y = P 0 x (y 0) * chainProd (fun i => P i.succ) (y 0) (Fin.tail y) := by
  unfold chainProd
  rw [Fin.prod_univ_succ]
  have h0 : (Fin.cons x y : Fin (k + 2) → S) (0 : Fin (k + 1)).castSucc = x := by
    rw [Fin.castSucc_zero, Fin.cons_zero]
  rw [h0]
  refine congrArg _ (Finset.prod_congr rfl fun i _ => ?_)
  have h1 : (Fin.cons x y : Fin (k + 2) → S) i.succ.castSucc = y i.castSucc := by
    rw [← Fin.succ_castSucc, Fin.cons_succ]
  have h2 : (Fin.cons (y 0) (Fin.tail y) : Fin (k + 1) → S) i.castSucc = y i.castSucc := by
    rw [Fin.cons_self_tail]
  rw [h1, h2]
  rfl

theorem chainProd_nonneg {k : ℕ} {P : Fin k → Matrix S S ℝ} (hP : ∀ i x y, 0 ≤ P i x y) (x : S)
    (y : Fin k → S) : 0 ≤ chainProd P x y :=
  Finset.prod_nonneg fun i _ => hP i _ _

variable [Fintype S]

theorem sum_fin_succ_tuple {k : ℕ} (F : (Fin (k + 1) → S) → ℝ) :
    ∑ y, F y = ∑ a, ∑ y' : Fin k → S, F (Fin.cons a y') := by
  rw [← (Fin.consEquiv fun _ : Fin (k + 1) => S).sum_comp, Fintype.sum_prod_type]
  rfl

theorem sum_chainProd {k : ℕ} {P : Fin k → Matrix S S ℝ} (hP : ∀ i x, ∑ y, P i x y = 1) (x : S) :
    ∑ y, chainProd P x y = 1 := by
  induction k generalizing x with
  | zero =>
    rw [Fintype.sum_unique]
    simp [chainProd]
  | succ k ih =>
    rw [sum_fin_succ_tuple]
    simp_rw [chainProd_succ, Fin.cons_zero, Fin.tail_cons, ← Finset.mul_sum,
      ih (fun i => hP i.succ), mul_one]
    exact hP 0 x

variable [DecidableEq T]

theorem sum_chainProd_fibre {f : S → T} {k : ℕ} {P : Fin k → Matrix S S ℝ}
    {P' : Fin k → Matrix T T ℝ} (h : ∀ i x s, ∑ y with f y = s, P i x y = P' i (f x) s) (x : S)
    (s : Fin k → T) :
    ∑ y with (fun i => f (y i)) = s, chainProd P x y = chainProd P' (f x) s := by
  induction k generalizing x with
  | zero =>
    rw [Finset.filter_true_of_mem fun y _ => Subsingleton.elim _ _, Fintype.sum_unique]
    simp [chainProd]
  | succ k ih =>
    have key : ∀ (a : S) (y' : Fin k → S),
        ((fun i => f ((Fin.cons a y' : Fin (k + 1) → S) i)) = s) ↔
          (f a = s 0 ∧ (fun i => f (y' i)) = Fin.tail s) := by
      intro a y'
      constructor
      · intro hs
        subst hs
        exact ⟨by simp, by funext i; simp [Fin.tail]⟩
      · rintro ⟨h0, ht⟩
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using h0
        · simpa [Fin.tail] using congrFun ht j
    have hstep : ∀ a : S,
        (∑ y' : Fin k → S, if (fun i => f ((Fin.cons a y' : Fin (k + 1) → S) i)) = s then
            chainProd P x (Fin.cons a y') else 0) =
          if f a = s 0 then
            P 0 x a * chainProd (fun i => P' i.succ) (s 0) (Fin.tail s) else 0 := by
      intro a
      by_cases ha : f a = s 0
      · simp only [ha, ↓reduceIte]
        rw [← ha, ← ih (fun i => h i.succ) a (Fin.tail s), Finset.sum_filter, Finset.mul_sum]
        refine Finset.sum_congr rfl fun y' _ => ?_
        by_cases hy : (fun i => f (y' i)) = Fin.tail s
        · have hc := (key a y').2 ⟨ha, hy⟩
          simp only [hy, hc, ↓reduceIte]
          rw [chainProd_succ, Fin.cons_zero, Fin.tail_cons]
        · have hc : ¬(fun i => f ((Fin.cons a y' : Fin (k + 1) → S) i)) = s :=
            fun hc => hy ((key a y').1 hc).2
          simp only [hy, hc, ↓reduceIte, mul_zero]
      · simp only [ha, ↓reduceIte]
        refine Finset.sum_eq_zero fun y' _ => ?_
        have hc : ¬(fun i => f ((Fin.cons a y' : Fin (k + 1) → S) i)) = s :=
          fun hc => ha ((key a y').1 hc).1
        simp only [hc, ↓reduceIte]
    rw [Finset.sum_filter, sum_fin_succ_tuple]
    simp_rw [hstep]
    rw [← Finset.sum_filter, ← Finset.sum_mul, h 0 x (s 0), chainProd_succ]

end ChainProd

namespace RateChain

variable {S T : Type*} [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]

noncomputable def fddMass (R : RateChain S) (x : S) {k : ℕ} (t : Fin k → ℝ) (y : Fin k → S) :
    ℝ :=
  ∏ i : Fin k, R.semigroup (t i - (Fin.cons 0 t : Fin (k + 1) → ℝ) i.castSucc)
    ((Fin.cons x y : Fin (k + 1) → S) i.castSucc) (y i)

variable (R : RateChain S)

theorem fddMass_eq_chainProd (x : S) {k : ℕ} (t : Fin k → ℝ) (y : Fin k → S) :
    R.fddMass x t y =
      chainProd (fun i => R.semigroup (t i - (Fin.cons 0 t : Fin (k + 1) → ℝ) i.castSucc)) x y :=
  rfl

theorem fdd_increment_nonneg {k : ℕ} {t : Fin k → ℝ} (hmono : Monotone t) (h0 : ∀ i, 0 ≤ t i)
    (i : Fin k) : 0 ≤ t i - (Fin.cons 0 t : Fin (k + 1) → ℝ) i.castSucc := by
  cases k with
  | zero => exact i.elim0
  | succ k =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [Fin.castSucc_zero, Fin.cons_zero, sub_zero]
      exact h0 0
    · rw [← Fin.succ_castSucc, Fin.cons_succ, sub_nonneg]
      exact hmono (Fin.castSucc_lt_succ).le

theorem fdd_increment_succ {k : ℕ} (t : Fin (k + 1) → ℝ) (i : Fin k) :
    t i.succ - (Fin.cons 0 t : Fin (k + 2) → ℝ) i.succ.castSucc =
      (t i.succ - t 0) -
        (Fin.cons 0 (fun j : Fin k => t j.succ - t 0) : Fin (k + 1) → ℝ) i.castSucc := by
  rw [← Fin.succ_castSucc, Fin.cons_succ]
  cases k with
  | zero => exact i.elim0
  | succ k =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [Fin.castSucc_zero, Fin.cons_zero, sub_zero]
    · rw [← Fin.succ_castSucc, Fin.cons_succ]
      ring

theorem fddMass_succ (x : S) {k : ℕ} (t : Fin (k + 1) → ℝ) (y : Fin (k + 1) → S) :
    R.fddMass x t y =
      R.semigroup (t 0) x (y 0) * R.fddMass (y 0) (fun i => t i.succ - t 0) (Fin.tail y) := by
  rw [fddMass_eq_chainProd, chainProd_succ, fddMass_eq_chainProd]
  have h0 : t 0 - (Fin.cons 0 t : Fin (k + 2) → ℝ) (0 : Fin (k + 1)).castSucc = t 0 := by
    rw [Fin.castSucc_zero, Fin.cons_zero, sub_zero]
  simp only [h0, fdd_increment_succ]

theorem fddMass_nonneg (x : S) {k : ℕ} {t : Fin k → ℝ} (hmono : Monotone t)
    (h0 : ∀ i, 0 ≤ t i) (y : Fin k → S) : 0 ≤ R.fddMass x t y :=
  Finset.prod_nonneg fun i _ => R.semigroup_nonneg (fdd_increment_nonneg hmono h0 i) _ _

theorem sum_fddMass (x : S) {k : ℕ} (t : Fin k → ℝ) : ∑ y, R.fddMass x t y = 1 := by
  simp_rw [fddMass_eq_chainProd]
  exact sum_chainProd (fun i z => R.semigroup_row_sum _ z) x

theorem fddMass_one (x : S) (t : Fin 1 → ℝ) (y : Fin 1 → S) :
    R.fddMass x t y = R.semigroup (t 0) x (y 0) := by
  simp [fddMass]

theorem sum_fddMass_insertNth (x : S) {k : ℕ} (t : Fin (k + 1) → ℝ) (j : Fin (k + 1))
    (y : Fin k → S) :
    ∑ z, R.fddMass x t (j.insertNth z y) = R.fddMass x (j.removeNth t) y := by
  induction k generalizing x with
  | zero =>
    have hj : j = 0 := Fin.fin_one_eq_zero j
    subst hj
    simp [fddMass, R.semigroup_row_sum]
  | succ k ih =>
    refine Fin.cases ?_ (fun j' => ?_) j
    · simp_rw [Fin.insertNth_zero', R.fddMass_succ x t, Fin.cons_zero, Fin.tail_cons]
      rw [R.fddMass_succ x (Fin.removeNth 0 t) y]
      simp_rw [R.fddMass_succ _ (fun i : Fin (k + 1) => t i.succ - t 0) y, ← mul_assoc,
        ← Finset.sum_mul]
      have hCK : ∑ z, R.semigroup (t 0) x z * R.semigroup (t (Fin.succ 0) - t 0) z (y 0) =
          R.semigroup (t (Fin.succ 0)) x (y 0) := by
        rw [← Matrix.mul_apply, ← R.semigroup_add]
        congr 2
        ring
      rw [hCK]
      have hrem : ∀ i : Fin (k + 1), Fin.removeNth 0 t i = t i.succ := fun i => rfl
      simp only [hrem]
      congr 2
      funext i
      ring
    · have hy : j'.succ.insertNth (α := fun _ => S) = fun z y =>
          (Fin.cons (y 0) (j'.insertNth z (Fin.tail y)) : Fin (k + 2) → S) := by
        funext z y
        conv_lhs => rw [← Fin.cons_self_tail y]
        exact Fin.insertNth_succ_cons j' z (y 0) (Fin.tail y)
      simp_rw [hy, R.fddMass_succ x t, Fin.cons_zero, Fin.tail_cons, ← Finset.mul_sum, ih]
      rw [R.fddMass_succ x (j'.succ.removeNth t) y]
      have h0 : j'.succ.removeNth t 0 = t 0 := by
        simp [Fin.removeNth]
      have hs : (fun i : Fin k => j'.succ.removeNth t i.succ - t 0) =
          j'.removeNth fun i : Fin (k + 1) => t i.succ - t 0 := by
        funext i
        simp [Fin.removeNth]
      rw [h0, hs]

section Measure

variable [MeasurableSpace S] [DiscreteMeasurableSpace S]

noncomputable def fdd (x : S) {k : ℕ} (t : Fin k → ℝ) : Measure (Fin k → S) :=
  ∑ y, ENNReal.ofReal (R.fddMass x t y) • Measure.dirac y

theorem fdd_apply_singleton (x : S) {k : ℕ} (t : Fin k → ℝ) (y : Fin k → S) :
    R.fdd x t {y} = ENNReal.ofReal (R.fddMass x t y) := by
  rw [fdd, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ (measurableSet_singleton y), Set.indicator_apply,
    Set.mem_singleton_iff, Pi.one_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' univ y]
  simp

theorem isProbabilityMeasure_fdd (x : S) {k : ℕ} {t : Fin k → ℝ} (hmono : Monotone t)
    (h0 : ∀ i, 0 ≤ t i) : IsProbabilityMeasure (R.fdd x t) := by
  refine ⟨?_⟩
  rw [← Finset.coe_univ, ← sum_measure_singleton]
  simp_rw [fdd_apply_singleton]
  rw [← ENNReal.ofReal_sum_of_nonneg fun y _ => R.fddMass_nonneg x hmono h0 y, R.sum_fddMass,
    ENNReal.ofReal_one]

structure HasFDD (x : S) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → S) :
    Prop where
  measurable : ∀ t, Measurable (X t)
  map_fdd : ∀ (k : ℕ) (t : Fin k → ℝ≥0), Monotone t →
    P.map (fun ω i => X (t i) ω) = R.fdd x fun i => (t i : ℝ)

noncomputable def fddFinset (x : S) (I : Finset ℝ≥0) : Measure (I → S) :=
  (R.fdd x fun i => (((I.orderIsoOfFin rfl i : I) : ℝ≥0) : ℝ)).map
    fun y j => y ((I.orderIsoOfFin rfl).symm j)

variable {R}

omit [DiscreteMeasurableSpace S] in
theorem HasFDD.map_restrict {x : S} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℝ≥0 → Ω → S} (hX : R.HasFDD x P X) (I : Finset ℝ≥0) :
    (P.map fun ω t => X t ω).map I.restrict = R.fddFinset x I := by
  have hXm' : Measurable fun ω t => X t ω := measurable_pi_iff.2 hX.measurable
  have hmono : Monotone fun i => ((I.orderIsoOfFin rfl i : I) : ℝ≥0) :=
    (Subtype.mono_coe _).comp (I.orderIsoOfFin rfl).monotone
  have hg : Measurable fun (y : Fin I.card → S) (j : I) => y ((I.orderIsoOfFin rfl).symm j) :=
    measurable_pi_iff.2 fun j => measurable_pi_apply _
  rw [fddFinset, ← hX.map_fdd _ _ hmono, Measure.map_map (Finset.measurable_restrict I) hXm',
    Measure.map_map hg (measurable_pi_iff.2 fun i => hX.measurable _)]
  congr 1
  funext ω j
  change _ = X (((I.orderIsoOfFin rfl) ((I.orderIsoOfFin rfl).symm j) : I) : ℝ≥0) ω
  rw [OrderIso.apply_symm_apply]
  rfl

omit [DiscreteMeasurableSpace S] in
theorem HasFDD.map_eq {x : S} {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {X : ℝ≥0 → Ω → S} {Y : ℝ≥0 → Ω' → S} (hX : R.HasFDD x P X) (hY : R.HasFDD x P' Y) :
    P.map (fun ω t => X t ω) = P'.map (fun ω t => Y t ω) := by
  have : ∀ I : Finset ℝ≥0, IsFiniteMeasure (R.fddFinset x I) := fun I => by
    rw [← hX.map_restrict I]
    infer_instance
  exact IsProjectiveLimit.unique (P := fun I : Finset ℝ≥0 => R.fddFinset x I)
    (fun I => hX.map_restrict I) fun I => hY.map_restrict I

end Measure

variable {R : RateChain S} {f : S → T} {R' : RateChain T}

theorem Lumps.sum_fddMass_fibre (hL : R.Lumps f R') (x : S) {k : ℕ} (t : Fin k → ℝ)
    (s : Fin k → T) :
    ∑ y with (fun i => f (y i)) = s, R.fddMass x t y = R'.fddMass (f x) t s := by
  simp_rw [fddMass_eq_chainProd]
  exact sum_chainProd_fibre
    (P := fun i => R.semigroup (t i - (Fin.cons 0 t : Fin (k + 1) → ℝ) i.castSucc))
    (P' := fun i => R'.semigroup (t i - (Fin.cons 0 t : Fin (k + 1) → ℝ) i.castSucc))
    (fun i z u => hL.sum_semigroup_fibre _ z u) x s

variable [MeasurableSpace S] [DiscreteMeasurableSpace S] [MeasurableSpace T]
  [DiscreteMeasurableSpace T]

theorem Lumps.map_fdd (hL : R.Lumps f R') (x : S) {k : ℕ} {t : Fin k → ℝ} (hmono : Monotone t)
    (h0 : ∀ i, 0 ≤ t i) : (R.fdd x t).map (fun y i => f (y i)) = R'.fdd (f x) t := by
  have hF : Measurable fun (y : Fin k → S) (i : Fin k) => f (y i) :=
    measurable_pi_iff.2 fun i => (Measurable.of_discrete (f := f)).comp (measurable_pi_apply i)
  refine Measure.ext_of_singleton fun s => ?_
  have hset : (fun (y : Fin k → S) (i : Fin k) => f (y i)) ⁻¹' {s} =
      ↑(univ.filter fun y : Fin k → S => (fun i => f (y i)) = s) := by
    ext y
    simp
  rw [Measure.map_apply hF (measurableSet_singleton s), hset, ← sum_measure_singleton]
  simp only [fdd_apply_singleton]
  rw [← ENNReal.ofReal_sum_of_nonneg fun y _ => R.fddMass_nonneg x hmono h0 y,
    hL.sum_fddMass_fibre x t s]

theorem Lumps.hasFDD_comp (hL : R.Lumps f R') {x : S} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : ℝ≥0 → Ω → S} (hX : R.HasFDD x P X) :
    R'.HasFDD (f x) P fun t ω => f (X t ω) := by
  refine ⟨fun t => (Measurable.of_discrete (f := f)).comp (hX.measurable t),
    fun k t hmono => ?_⟩
  have hF : Measurable fun (y : Fin k → S) (i : Fin k) => f (y i) :=
    measurable_pi_iff.2 fun i => (Measurable.of_discrete (f := f)).comp (measurable_pi_apply i)
  have hmap := hL.map_fdd x (t := fun i => (t i : ℝ)) (NNReal.coe_mono.comp hmono)
    fun i => (t i).coe_nonneg
  rw [← hmap, ← hX.map_fdd k t hmono,
    Measure.map_map hF (measurable_pi_iff.2 fun i => hX.measurable (t i))]
  rfl

theorem Lumps.map_process_eq (hL : R.Lumps f R') {x : S} {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P]
    [IsProbabilityMeasure P'] {X : ℝ≥0 → Ω → S} {Y : ℝ≥0 → Ω' → T} (hX : R.HasFDD x P X)
    (hY : R'.HasFDD (f x) P' Y) :
    P.map (fun ω t => f (X t ω)) = P'.map (fun ω t => Y t ω) :=
  (hL.hasFDD_comp hX).map_eq hY

end RateChain

end Rhone.MarkovChain
