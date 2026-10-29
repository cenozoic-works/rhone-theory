/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeProposalKernel
public import Rhone.Coalescent.SmcSupport.HistoryCoordinates
public import Rhone.Coalescent.SmcSupport.SelectorProduct

/-!
# Branch-length cut measure of the SMC′ source sampler

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, step 2. -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess MeasureTheory SmcSupport
open scoped ENNReal

noncomputable def cutValue {N : ℕ} (T : Tree N) (uv : ℝ × ℝ) : Finset (Fin N) × ℝ :=
  (cutPoint T uv.1 uv.2).getD (∅, 0)

noncomputable def branchCutMeasure {N : ℕ} (b : Branch N) :
    Measure (Finset (Fin N) × ℝ) := by
  classical
  exact if b.1 = ∅ ∨ b.1 = Finset.univ then 0
    else (volume.restrict (Set.Ioo b.2.1 b.2.2)).map (fun t => (b.1, t))

noncomputable def treeCutMeasure {N : ℕ} (T : Tree N) :
    Measure (Finset (Fin N) × ℝ) := ∑ i, branchCutMeasure (T.2 i)

theorem cutValue_measurable {N : ℕ} (T : Tree N) : Measurable (cutValue T) := by
  classical
  let : MeasurableSpace (Option (Fin T.1)) := ⊤
  let g (p : ℝ × ℝ) := chooseByRate (fun i => branchLength (T.2 i))
    (List.finRange T.1) (p.1 * treeLength T)
  have hg : Measurable g := chooseByRate_measurable
    (fun i _ => branchLength (T.2 i)) (fun _ => measurable_const) (List.finRange T.1)
    (fun p : ℝ × ℝ => p.1 * treeLength T) (measurable_fst.mul_const _)
  let f (a : Option (Fin T.1)) (p : ℝ × ℝ) : Finset (Fin N) × ℝ :=
    match a with
    | none => (∅, 0)
    | some i => ((T.2 i).1, (T.2 i).2.1 + ((T.2 i).2.2 - (T.2 i).2.1) * p.2)
  have hf (a : Option (Fin T.1)) : Measurable (f a) := by
    cases a <;> dsimp [f] <;> fun_prop
  have hfinal := measurable_countable_choice g hg f hf
  convert hfinal using 1
  funext p
  simp only [cutValue, cutPoint]
  change (match g p with | none => none | some i => some ((T.2 i).1,
    (T.2 i).2.1 + ((T.2 i).2.2 - (T.2 i).2.1) * p.2)).getD (∅, 0) = _
  cases g p <;> rfl

theorem branchSelector_partition {N : ℕ} (T : Tree N) (hL : 0 < treeLength T) :
    unitUniform = ∑ i : Fin T.1,
      unitUniform.restrict {u | chooseByRate (fun j => branchLength (T.2 j))
        (List.finRange T.1) (u * treeLength T) = some i} := by
  classical
  let : MeasurableSpace (Option (Fin T.1)) := ⊤
  let g (u : ℝ) := chooseByRate (fun i => branchLength (T.2 i))
    (List.finRange T.1) (u * treeLength T)
  let E (i : Fin T.1) : Set ℝ := {u | g u = some i}
  have hg : Measurable g := chooseByRate_measurable
    (fun i _ => branchLength (T.2 i)) (fun _ => measurable_const) (List.finRange T.1)
    (fun u : ℝ => u * treeLength T) (measurable_id.mul_const _)
  have hE (i : Fin T.1) : MeasurableSet (E i) :=
    hg (show MeasurableSet ({some i} : Set (Option (Fin T.1))) from by trivial)
  have hd : Pairwise (fun i j => Disjoint (E i) (E j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro u hi hj
    exact hij (Option.some.inj (hi.symm.trans hj))
  have hsum : ((List.finRange T.1).map (fun i => branchLength (T.2 i))).sum =
      treeLength T := by
    rw [← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]
    rfl
  have hcover : (⋃ i, E i) =ᵐ[unitUniform] Set.univ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    obtain ⟨i, hi, _⟩ := chooseByRate_exists_positive
      (fun i => branchLength (T.2 i)) (List.finRange T.1)
      (fun _ _ => branchLength_nonneg _) (u * treeLength T)
      (mul_nonneg hu.1.le hL.le) (by rw [hsum]; nlinarith [hu.2])
    exact propext ⟨fun _ => Set.mem_univ _, fun _ => Set.mem_iUnion.mpr ⟨i, hi⟩⟩
  calc
    unitUniform = unitUniform.restrict (⋃ i, E i) := by
      rw [Measure.restrict_congr_set hcover, Measure.restrict_univ]
    _ = ∑ i, unitUniform.restrict (E i) := by
      rw [Measure.restrict_iUnion hd hE, Measure.sum_fintype]

private theorem branchCutMeasure_zero {N : ℕ} (b : Branch N)
    (h : branchLength b = 0) : branchCutMeasure b = 0 := by
  classical
  by_cases hp : b.1 = ∅ ∨ b.1 = Finset.univ
  · simp [branchCutMeasure, hp]
  · have hw : b.2.2 ≤ b.2.1 := by
      have hd : b.2.2 - b.2.1 ≤ 0 := by
        have hm := le_max_right 0 (b.2.2 - b.2.1)
        have hm0 : max 0 (b.2.2 - b.2.1) = 0 := by
          simpa only [branchLength, ite_eq_right hp] using h
        rwa [hm0] at hm
      linarith
    simp [branchCutMeasure, hp, Set.Ioo_eq_empty_of_le hw]

private theorem branchCut_component {N : ℕ} (T : Tree N)
    (hL : 0 < treeLength T) (i : Fin T.1) :
    ENNReal.ofReal (branchLength (T.2 i) / treeLength T) •
      unitUniform.map (fun v =>
        ((T.2 i).1, (T.2 i).2.1 + ((T.2 i).2.2 - (T.2 i).2.1) * v)) =
    ENNReal.ofReal ((treeLength T)⁻¹) • branchCutMeasure (T.2 i) := by
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
    have hg : Measurable (fun t : ℝ => ((T.2 i).1, t)) :=
      measurable_const.prodMk measurable_id
    change ENNReal.ofReal (branchLength (T.2 i) / treeLength T) •
      unitUniform.map ((fun t : ℝ => ((T.2 i).1, t)) ∘
        fun v => (T.2 i).2.1 + ((T.2 i).2.2 - (T.2 i).2.1) * v) = _
    rw [← Measure.map_map hg (by fun_prop), affineCut_uniform_law _ _ hw,
      Measure.map_smul _ hg.aemeasurable, smul_smul]
    simp only [branchCutMeasure, ite_eq_right hp]
    congr 1
    rw [← ENNReal.ofReal_mul (by positivity), hl]
    congr 1
    field_simp [(sub_pos.mpr hw).ne']
  · have hz := le_antisymm (le_of_not_gt hb) (branchLength_nonneg (T.2 i))
    simp [hz, branchCutMeasure_zero _ hz]

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, step 2. -/
theorem cutPoint_uniform_law {N : ℕ} (T : Tree N) (hL : 0 < treeLength T) :
    (unitUniform.prod unitUniform).map (cutValue T) =
      ENNReal.ofReal ((treeLength T)⁻¹) • treeCutMeasure T := by
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
    ((T.2 i).1, (T.2 i).2.1 + ((T.2 i).2.2 - (T.2 i).2.1) * v)
  have hbranch (i : Fin T.1) (u : ℝ) (hu : u ∈ E i) (v : ℝ) :
      cutValue T (u, v) = g i v := by
    have hi : chooseByRate (fun j => branchLength (T.2 j))
        (List.finRange T.1) (u * treeLength T) = some i := hu
    simp [cutValue, cutPoint, hi, g]
  rw [map_prod_of_partition unitUniform unitUniform E hE
    (branchSelector_partition T hL) (cutValue T) (cutValue_measurable T)
    g (fun _ => by dsimp [g]; fun_prop) hbranch]
  dsimp only [E, g]
  simp_rw [branchChoice_mass T hL]
  simp_rw [branchCut_component T hL]
  simp only [treeCutMeasure, Finset.smul_sum]

end Rhone.Coalescent.SmcPrime
