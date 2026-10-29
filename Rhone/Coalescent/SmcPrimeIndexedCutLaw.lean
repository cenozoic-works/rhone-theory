/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeCutLaw

/-!
# Indexed cut law of the SMC′ source sampler

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, step 2. -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess MeasureTheory SmcSupport
open scoped ENNReal

noncomputable def indexedCutValue {N : ℕ} (T : Tree N) (uv : ℝ × ℝ) : ℕ × ℝ :=
  match chooseByRate (fun i => branchLength (T.2 i)) (List.finRange T.1)
      (uv.1 * treeLength T) with
  | none => (T.1, 0)
  | some i => (i.val, (T.2 i).2.1 + ((T.2 i).2.2 - (T.2 i).2.1) * uv.2)

noncomputable def indexedBranchCutMeasure {N : ℕ} (T : Tree N) (i : Fin T.1) :
    Measure (ℕ × ℝ) := by
  classical
  exact if (T.2 i).1 = ∅ ∨ (T.2 i).1 = Finset.univ then 0
    else (volume.restrict (Set.Ioo (T.2 i).2.1 (T.2 i).2.2)).map (fun t => (i.val, t))

noncomputable def indexedTreeCutMeasure {N : ℕ} (T : Tree N) :
    Measure (ℕ × ℝ) := ∑ i, indexedBranchCutMeasure T i

noncomputable def forgetCutIndex {N : ℕ} (T : Tree N) (p : ℕ × ℝ) :
    Finset (Fin N) × ℝ :=
  if h : p.1 < T.1 then ((T.2 ⟨p.1, h⟩).1, p.2) else (∅, 0)

theorem indexedCutValue_measurable {N : ℕ} (T : Tree N) :
    Measurable (indexedCutValue T) := by
  classical
  let : MeasurableSpace (Option (Fin T.1)) := ⊤
  let g (p : ℝ × ℝ) := chooseByRate (fun i => branchLength (T.2 i))
    (List.finRange T.1) (p.1 * treeLength T)
  have hg : Measurable g := chooseByRate_measurable
    (fun i _ => branchLength (T.2 i)) (fun _ => measurable_const) (List.finRange T.1)
    (fun p : ℝ × ℝ => p.1 * treeLength T) (measurable_fst.mul_const _)
  let f (a : Option (Fin T.1)) (p : ℝ × ℝ) : ℕ × ℝ :=
    match a with
    | none => (T.1, 0)
    | some i => (i.val, (T.2 i).2.1 + ((T.2 i).2.2 - (T.2 i).2.1) * p.2)
  have hf (a : Option (Fin T.1)) : Measurable (f a) := by
    cases a <;> dsimp [f] <;> fun_prop
  exact measurable_countable_choice g hg f hf

theorem forgetCutIndex_measurable {N : ℕ} (T : Tree N) :
    Measurable (forgetCutIndex T) := by
  let f (k : ℕ) (p : ℕ × ℝ) : Finset (Fin N) × ℝ :=
    if h : k < T.1 then ((T.2 ⟨k, h⟩).1, p.2) else (∅, 0)
  have hf (k : ℕ) : Measurable (f k) := by
    by_cases h : k < T.1
    · simpa only [f, dite_eq_left h] using measurable_const.prodMk measurable_snd
    · simp only [f, dite_eq_right h]
      exact measurable_const
  exact measurable_countable_choice Prod.fst measurable_fst f hf

theorem forgetCutIndex_indexedCutValue {N : ℕ} (T : Tree N) (uv : ℝ × ℝ) :
    forgetCutIndex T (indexedCutValue T uv) = cutValue T uv := by
  cases h : chooseByRate (fun i => branchLength (T.2 i)) (List.finRange T.1)
      (uv.1 * treeLength T) with
  | none => simp [indexedCutValue, cutValue, cutPoint, h, forgetCutIndex]
  | some i => simp [indexedCutValue, cutValue, cutPoint, h, forgetCutIndex, i.isLt]

private theorem indexedBranchCutMeasure_zero {N : ℕ} (T : Tree N) (i : Fin T.1)
    (h : branchLength (T.2 i) = 0) : indexedBranchCutMeasure T i = 0 := by
  classical
  by_cases hp : (T.2 i).1 = ∅ ∨ (T.2 i).1 = Finset.univ
  · simp [indexedBranchCutMeasure, hp]
  · have hw : (T.2 i).2.2 ≤ (T.2 i).2.1 := by
      have hd : (T.2 i).2.2 - (T.2 i).2.1 ≤ 0 := by
        have hm := le_max_right 0 ((T.2 i).2.2 - (T.2 i).2.1)
        have hm0 : max 0 ((T.2 i).2.2 - (T.2 i).2.1) = 0 := by
          simpa only [branchLength, ite_eq_right hp] using h
        rwa [hm0] at hm
      linarith
    simp [indexedBranchCutMeasure, hp, Set.Ioo_eq_empty_of_le hw]

private theorem indexedBranchCut_component {N : ℕ} (T : Tree N)
    (hL : 0 < treeLength T) (i : Fin T.1) :
    ENNReal.ofReal (branchLength (T.2 i) / treeLength T) •
      unitUniform.map (fun v =>
        (i.val, (T.2 i).2.1 + ((T.2 i).2.2 - (T.2 i).2.1) * v)) =
    ENNReal.ofReal ((treeLength T)⁻¹) • indexedBranchCutMeasure T i := by
  classical
  by_cases hb : 0 < branchLength (T.2 i)
  · have hp : ¬ ((T.2 i).1 = ∅ ∨ (T.2 i).1 = Finset.univ) := by
      intro hp
      simp [branchLength, hp] at hb
    have hw : (T.2 i).2.1 < (T.2 i).2.2 := by
      simpa only [branchLength, ite_eq_right hp, lt_max_iff, lt_self_iff_false,
        false_or, sub_pos] using hb
    have hl : branchLength (T.2 i) = (T.2 i).2.2 - (T.2 i).2.1 := by
      simp [branchLength, hp, max_eq_right (sub_pos.mpr hw).le]
    have hg : Measurable (fun t : ℝ => (i.val, t)) := measurable_const.prodMk measurable_id
    change ENNReal.ofReal (branchLength (T.2 i) / treeLength T) •
      unitUniform.map ((fun t : ℝ => (i.val, t)) ∘
        fun v => (T.2 i).2.1 + ((T.2 i).2.2 - (T.2 i).2.1) * v) = _
    rw [← Measure.map_map hg (by fun_prop), affineCut_uniform_law _ _ hw,
      Measure.map_smul _ hg.aemeasurable, smul_smul]
    simp only [indexedBranchCutMeasure, ite_eq_right hp]
    congr 1
    rw [← ENNReal.ofReal_mul (by positivity), hl]
    congr 1
    field_simp [(sub_pos.mpr hw).ne']
  · have hz := le_antisymm (le_of_not_gt hb) (branchLength_nonneg (T.2 i))
    simp [hz, indexedBranchCutMeasure_zero _ _ hz]

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, step 2. -/
theorem indexedCutPoint_uniform_law {N : ℕ} (T : Tree N) (hL : 0 < treeLength T) :
    (unitUniform.prod unitUniform).map (indexedCutValue T) =
      ENNReal.ofReal ((treeLength T)⁻¹) • indexedTreeCutMeasure T := by
  classical
  let : MeasurableSpace (Option (Fin T.1)) := ⊤
  let E (i : Fin T.1) : Set ℝ := {u | chooseByRate (fun j => branchLength (T.2 j))
    (List.finRange T.1) (u * treeLength T) = some i}
  have hg : Measurable (fun u => chooseByRate (fun j => branchLength (T.2 j))
      (List.finRange T.1) (u * treeLength T)) := chooseByRate_measurable
    (fun i _ => branchLength (T.2 i)) (fun _ => measurable_const) (List.finRange T.1)
    (fun u : ℝ => u * treeLength T) (measurable_id.mul_const _)
  have hE (i : Fin T.1) : MeasurableSet (E i) :=
    hg (show MeasurableSet ({some i} : Set (Option (Fin T.1))) from by trivial)
  let g (i : Fin T.1) (v : ℝ) :=
    (i.val, (T.2 i).2.1 + ((T.2 i).2.2 - (T.2 i).2.1) * v)
  have hbranch (i : Fin T.1) (u : ℝ) (hu : u ∈ E i) (v : ℝ) :
      indexedCutValue T (u, v) = g i v := by
    have hi : chooseByRate (fun j => branchLength (T.2 j))
        (List.finRange T.1) (u * treeLength T) = some i := hu
    simp [indexedCutValue, hi, g]
  rw [map_prod_of_partition unitUniform unitUniform E hE
    (branchSelector_partition T hL) (indexedCutValue T) (indexedCutValue_measurable T)
    g (fun _ => by dsimp [g]; fun_prop) hbranch]
  dsimp only [E, g]
  simp_rw [branchChoice_mass T hL, indexedBranchCut_component T hL]
  simp only [indexedTreeCutMeasure, Finset.smul_sum]

theorem indexedTreeCutMeasure_map_forget {N : ℕ} (T : Tree N) :
    (indexedTreeCutMeasure T).map (forgetCutIndex T) = treeCutMeasure T := by
  classical
  rw [indexedTreeCutMeasure, Measure.map_finset_sum]
  · apply Finset.sum_congr rfl
    intro i _
    by_cases hp : (T.2 i).1 = ∅ ∨ (T.2 i).1 = Finset.univ
    · simp [indexedBranchCutMeasure, branchCutMeasure, hp]
    · simp only [indexedBranchCutMeasure, branchCutMeasure, ite_eq_right hp]
      rw [Measure.map_map (forgetCutIndex_measurable T)
        (show Measurable (fun t : ℝ => (i.val, t)) from
          measurable_const.prodMk measurable_id)]
      congr 1
      funext t
      simp [forgetCutIndex, i.isLt]
  · exact (forgetCutIndex_measurable T).aemeasurable
end Rhone.Coalescent.SmcPrime
