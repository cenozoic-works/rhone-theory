/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.FullARGTwoSampleKernel
public import Rhone.Coalescent.FullARGTwoSamplePath

/-!
# The interval state read at two probe positions

Source: griffiths1991_two_locus_graph, p. 106. -/

@[expose] public section

namespace Rhone.Coalescent.IntervalCounts

open MeasureTheory IntervalProcess MarkovChain.IntervalProcess

abbrev Counts := ℕ × ℕ × ℕ

def mergeType (t t' : Bool × Bool) : Bool × Bool := (t.1 || t'.1, t.2 || t'.2)

noncomputable def typeCount (x y : ℝ) (t : Bool × Bool) (s : State) : ℕ :=
  materialCount (fun a => carrierType x y a = t) s

noncomputable def typeCounts (x y : ℝ) (s : State) : Counts :=
  (typeCount x y (true, false) s, typeCount x y (false, true) s, typeCount x y (true, true) s)

def typeVec (t : Bool × Bool) : Counts :=
  (if t = (true, false) then 1 else 0, if t = (false, true) then 1 else 0,
    if t = (true, true) then 1 else 0)

def mergeCounts (k : Counts) (t t' : Bool × Bool) : Counts :=
  (k.1 + (typeVec (mergeType t t')).1 - (typeVec t).1 - (typeVec t').1,
    k.2.1 + (typeVec (mergeType t t')).2.1 - (typeVec t).2.1 - (typeVec t').2.1,
    k.2.2 + (typeVec (mergeType t t')).2.2 - (typeVec t).2.2 - (typeVec t').2.2)

def recCounts (k : Counts) : Counts := (k.1 + 1, k.2.1 + 1, k.2.2 - 1)

theorem carrierType_measurableSet (x y : ℝ) (t : Bool × Bool) :
    MeasurableSet {a : Material | carrierType x y a = t} := by
  classical
  have hx := materialContains_measurable x
  have hy := materialContains_measurable y
  obtain ⟨t1, t2⟩ := t
  have heq : {a : Material | carrierType x y a = (t1, t2)} =
      {a | (materialContains a x ↔ t1 = true)} ∩ {a | (materialContains a y ↔ t2 = true)} := by
    ext a
    simp only [carrierType, Set.mem_ofPred_eq, Set.mem_inter_iff, Prod.mk.injEq]
    cases t1 <;> cases t2 <;> simp [decide_eq_false_iff_not]
  rw [heq]
  refine MeasurableSet.inter ?_ ?_
  · cases t1 <;> simp only [Bool.false_eq_true, iff_false, iff_true]
    exacts [hx.compl, hx]
  · cases t2 <;> simp only [Bool.false_eq_true, iff_false, iff_true]
    exacts [hy.compl, hy]

theorem typeCount_measurable (x y : ℝ) (t : Bool × Bool) : Measurable (typeCount x y t) :=
  materialCount_measurable _ (carrierType_measurableSet x y t)

theorem typeCounts_measurable (x y : ℝ) : Measurable (typeCounts x y) :=
  (typeCount_measurable x y _).prodMk
    ((typeCount_measurable x y _).prodMk (typeCount_measurable x y _))

theorem carrierType_merge (x y : ℝ) (a b : Material) :
    carrierType x y (mergeMaterial a b) = mergeType (carrierType x y a) (carrierType x y b) := by
  classical
  simp only [carrierType, mergeType, materialContains_merge, Prod.mk.injEq]
  constructor <;> simp [Bool.decide_or]

open scoped Classical in
theorem carrierType_split_left (x y c : ℝ) (a : Material) :
    carrierType x y (splitMaterial a c).1 =
      (decide (materialContains a x ∧ x < c), decide (materialContains a y ∧ y < c)) := by
  classical
  simp only [carrierType, materialContains_split_left]

open scoped Classical in
theorem carrierType_split_right (x y c : ℝ) (a : Material) :
    carrierType x y (splitMaterial a c).2 =
      (decide (materialContains a x ∧ c ≤ x), decide (materialContains a y ∧ c ≤ y)) := by
  classical
  simp only [carrierType, materialContains_split_right]

theorem typeCount_coalSuccessor (x y : ℝ) (t : Bool × Bool) (s : State)
    (i j : Fin s.2.2.1) (hij : i.val < j.val) :
    typeCount x y t (coalSuccessor s i j) +
        (if carrierType x y (s.2.2.2 i).2 = t then 1 else 0) +
        (if carrierType x y (s.2.2.2 j).2 = t then 1 else 0) =
      typeCount x y t s +
        (if mergeType (carrierType x y (s.2.2.2 i).2) (carrierType x y (s.2.2.2 j).2) = t
          then 1 else 0) := by
  classical
  have h := materialCount_coalSuccessor (fun a => carrierType x y a = t) s i j hij
  simp only [carrierType_merge] at h
  unfold typeCount
  split_ifs at h ⊢ <;> omega

theorem typeCounts_coalSuccessor (x y : ℝ) (s : State) (i j : Fin s.2.2.1)
    (hij : i.val < j.val) :
    typeCounts x y (coalSuccessor s i j) =
      mergeCounts (typeCounts x y s) (carrierType x y (s.2.2.2 i).2)
        (carrierType x y (s.2.2.2 j).2) := by
  have h1 := typeCount_coalSuccessor x y (true, false) s i j hij
  have h2 := typeCount_coalSuccessor x y (false, true) s i j hij
  have h3 := typeCount_coalSuccessor x y (true, true) s i j hij
  simp only [typeCounts, mergeCounts, typeVec]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> dsimp only <;> omega

open scoped Classical in
theorem typeCount_splitSuccessor (x y : ℝ) (t : Bool × Bool) (s : State)
    (i : Fin s.2.2.1) (c : ℝ) :
    typeCount x y t (splitSuccessor s i c) +
        (if carrierType x y (s.2.2.2 i).2 = t then 1 else 0) =
      typeCount x y t s +
        (if (decide (materialContains (s.2.2.2 i).2 x ∧ x < c),
            decide (materialContains (s.2.2.2 i).2 y ∧ y < c)) = t then 1 else 0) +
        (if (decide (materialContains (s.2.2.2 i).2 x ∧ c ≤ x),
            decide (materialContains (s.2.2.2 i).2 y ∧ c ≤ y)) = t then 1 else 0) := by
  classical
  have h := materialCount_splitSuccessor (fun a => carrierType x y a = t) s i c
  simp only [carrierType_split_left, carrierType_split_right] at h
  unfold typeCount
  convert h using 3

open scoped Classical in
theorem typeCounts_splitSuccessor (x y : ℝ) (hxy : x < y) (s : State) (i : Fin s.2.2.1)
    (c : ℝ) :
    typeCounts x y (splitSuccessor s i c) =
      if carrierType x y (s.2.2.2 i).2 = (true, true) ∧ x < c ∧ c ≤ y then
        recCounts (typeCounts x y s) else typeCounts x y s := by
  classical
  have h1 := typeCount_splitSuccessor x y (true, false) s i c
  have h2 := typeCount_splitSuccessor x y (false, true) s i c
  have h3 := typeCount_splitSuccessor x y (true, true) s i c
  simp only [carrierType] at h1 h2 h3 ⊢
  by_cases hx : materialContains (s.2.2.2 i).2 x <;>
    by_cases hy : materialContains (s.2.2.2 i).2 y <;>
    rcases lt_or_ge x c with hxc | hxc <;>
    rcases lt_or_ge y c with hyc | hyc <;>
    simp only [hx, hy, hxc, hyc, not_lt.mpr, not_le.mpr, and_true, and_false,
      decide_true, decide_false, Prod.mk.injEq, Bool.true_eq_false,
      Bool.false_eq_true, and_self, ite_true, ite_false, typeCounts, recCounts] at h1 h2 h3 ⊢ <;>
    first
    | (exfalso; linarith)
    | (refine ⟨?_, ?_, ?_⟩ <;> omega)

theorem carrierCount_eq_typeCounts_fst (x y : ℝ) (s : State) :
    carrierCount x s = (typeCounts x y s).1 + (typeCounts x y s).2.2 := by
  classical
  simp only [typeCounts, typeCount, carrierCount, materialCount_eq_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h1 : materialContains (s.2.2.2 i).2 x <;>
    by_cases h2 : materialContains (s.2.2.2 i).2 y <;> simp [carrierType, h1, h2]

theorem carrierCount_eq_typeCounts_snd (x y : ℝ) (s : State) :
    carrierCount y s = (typeCounts x y s).2.1 + (typeCounts x y s).2.2 := by
  classical
  simp only [typeCounts, typeCount, carrierCount, materialCount_eq_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h1 : materialContains (s.2.2.2 i).2 x <;>
    by_cases h2 : materialContains (s.2.2.2 i).2 y <;> simp [carrierType, h1, h2]

theorem typeCounts_sum_le (x y : ℝ) (s : State) :
    (typeCounts x y s).1 + (typeCounts x y s).2.1 + (typeCounts x y s).2.2 ≤ s.2.2.1 := by
  classical
  have h := materialCount_le (fun a => materialContains a x ∨ materialContains a y) s
  have heq : materialCount (fun a => materialContains a x ∨ materialContains a y) s =
      (typeCounts x y s).1 + (typeCounts x y s).2.1 + (typeCounts x y s).2.2 := by
    simp only [typeCounts, typeCount, materialCount_eq_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h1 : materialContains (s.2.2.2 i).2 x <;>
      by_cases h2 : materialContains (s.2.2.2 i).2 y <;> simp [carrierType, h1, h2]
  omega

theorem typeCounts_initialState (N : ℕ) (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hy0 : 0 ≤ y) (hy1 : y < 1) : typeCounts x y (initialState N) = (0, 0, N) := by
  classical
  have hall : ∀ i : Fin (initialState N).2.2.1,
      carrierType x y ((initialState N).2.2.2 i).2 = (true, true) := fun i => by
    simp [carrierType, (initial_materialContains N i x).mpr ⟨hx0, hx1⟩,
      (initial_materialContains N i y).mpr ⟨hy0, hy1⟩]
  have h11 : typeCount x y (true, true) (initialState N) = N :=
    (materialCount_eq_of_forall _ _ hall).trans rfl
  have h0 : ∀ t, t ≠ (true, true) → typeCount x y t (initialState N) = 0 := by
    intro t ht
    unfold typeCount
    rw [materialCount_eq_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    simp [hall i, Ne.symm ht]
  simp only [typeCounts, h11, h0 (true, false) (by decide), h0 (false, true) (by decide)]

end Rhone.Coalescent.IntervalCounts
