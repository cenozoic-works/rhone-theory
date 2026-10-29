/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.FiniteIntervalMaterialArrays
public import Mathlib.MeasureTheory.MeasurableSpace.Prod

/-! # Borel operations on the finite-interval material arrays -/
@[expose] public section

namespace Rhone.Coalescent.IntervalProcess
open MeasureTheory

theorem measurable_sigma_mk {ι : Type*} {β : ι → Type*}
    [∀ i, MeasurableSpace (β i)] (i : ι) : Measurable (Sigma.mk i : β i → Sigma β) := by
  rw [measurable_iff_le_map]
  exact iInf_le _ i

theorem measurableEmbedding_sigma_mk {ι : Type*} {β : ι → Type*}
    [∀ i, MeasurableSpace (β i)] (i : ι) :
    MeasurableEmbedding (Sigma.mk i : β i → Sigma β) := by
  classical
  have hinj : Function.Injective (Sigma.mk i : β i → Sigma β) :=
    fun _ _ h => eq_of_heq (Sigma.mk.inj h).2
  refine ⟨hinj, measurable_sigma_mk i, ?_⟩
  intro s hs
  change MeasurableSet[⨅ j, (inferInstance : MeasurableSpace (β j)).map (Sigma.mk j)] _
  rw [MeasurableSpace.measurableSet_iInf]
  intro j
  change MeasurableSet ((Sigma.mk j) ⁻¹' (Sigma.mk i '' s))
  by_cases h : j = i
  · subst j
    rw [hinj.preimage_image]
    exact hs
  · have heq : (Sigma.mk j) ⁻¹' (Sigma.mk i '' s) = ∅ := by
      ext x
      constructor
      · rintro ⟨y, _, hy⟩
        exact (h (congrArg Sigma.fst hy).symm).elim
      · simp
    rw [heq]
    exact MeasurableSet.empty

theorem measurable_prod_sigma_of_fibers {ι : Type*} [Countable ι]
    {β : ι → Type*} {γ δ : Type*} [∀ i, MeasurableSpace (β i)]
    [MeasurableSpace γ] [MeasurableSpace δ] (f : Sigma β × γ → δ)
    (hf : ∀ i, Measurable (fun p : β i × γ => f (⟨i,p.1⟩,p.2))) :
    Measurable f := by
  intro t ht
  let g (i : ι) : β i × γ → Sigma β × γ := Prod.map (Sigma.mk i) id
  have hg (i : ι) : MeasurableEmbedding (g i) :=
    (measurableEmbedding_sigma_mk i).prodMap MeasurableEmbedding.id
  have hi (i : ι) : MeasurableSet (g i '' ((f ∘ g i) ⁻¹' t)) :=
    (hg i).measurableSet_image' (hf i ht)
  have heq : f ⁻¹' t = ⋃ i, g i '' ((f ∘ g i) ⁻¹' t) := by
    ext p
    constructor
    · intro hp
      exact Set.mem_iUnion.mpr ⟨p.1.1, ⟨(p.1.2,p.2), hp, rfl⟩⟩
    · intro hp
      obtain ⟨i, q, hq, rfl⟩ := Set.mem_iUnion.mp hp
      exact hq
  rw [heq]
  exact MeasurableSet.iUnion hi

theorem splitMaterial_measurable :
    Measurable (fun p : Material × ℝ => splitMaterial p.1 p.2) := by
  apply measurable_prod_sigma_of_fibers
  intro k
  change Measurable (fun p : (Fin (k+1) → ℝ × ℝ) × ℝ =>
    ((⟨k, fun i => ((p.1 i).1, max (p.1 i).1 (min (p.1 i).2 p.2))⟩ : Material),
     (⟨k, fun i => (max (p.1 i).1 (min (p.1 i).2 p.2), (p.1 i).2)⟩ : Material)))
  apply Measurable.prodMk
  · apply (measurable_sigma_mk k).comp
    apply measurable_pi_iff.mpr
    intro i
    fun_prop
  · apply (measurable_sigma_mk k).comp
    apply measurable_pi_iff.mpr
    intro i
    fun_prop

theorem mergeMaterial_measurable :
    Measurable (fun p : Material × Material => mergeMaterial p.1 p.2) := by
  apply measurable_prod_sigma_of_fibers
  intro k
  have hf : Measurable (fun p : Material × (Fin (k+1) → ℝ × ℝ) =>
      mergeMaterial ⟨k,p.2⟩ p.1) := by
    apply measurable_prod_sigma_of_fibers
    intro l
    change Measurable (fun p : (Fin (l+1) → ℝ × ℝ) × (Fin (k+1) → ℝ × ℝ) =>
      (⟨k+l+1, fun i => if h : i.val < k+1 then p.2 ⟨i.val,h⟩
        else p.1 ⟨i.val-(k+1), by omega⟩⟩ : Material))
    apply (measurable_sigma_mk (k+l+1)).comp
    apply measurable_pi_iff.mpr
    intro i
    split_ifs <;> fun_prop
  exact hf.comp measurable_swap

end Rhone.Coalescent.IntervalProcess
