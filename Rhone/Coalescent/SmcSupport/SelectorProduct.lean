/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcSupport.HistoryNoise
public import Rhone.Coalescent.SmcSupport.Selector

/-! # Finite measurable selector partitions of independent product noise -/
@[expose] public section
namespace Rhone.Coalescent.SmcSupport
open MeasureTheory IntervalProcess

theorem map_prod_of_partition {A Ω Ξ Y : Type*} [Fintype A]
    [MeasurableSpace Ω] [MeasurableSpace Ξ] [MeasurableSpace Y]
    (μ : Measure Ω) (ν : Measure Ξ) [SFinite μ] [SFinite ν]
    (E : A → Set Ω) (hE : ∀ a, MeasurableSet (E a))
    (hcover : μ = ∑ a, μ.restrict (E a))
    (f : Ω × Ξ → Y) (hf : Measurable f)
    (g : A → Ξ → Y) (hg : ∀ a, Measurable (g a))
    (hbranch : ∀ a, ∀ ω ∈ E a, ∀ ξ, f (ω, ξ) = g a ξ) :
    (μ.prod ν).map f = ∑ a, μ (E a) • ν.map (g a) := by
  calc
    (μ.prod ν).map f =
        ((Measure.sum (fun a => μ.restrict (E a))).prod ν).map f := by
      rw [Measure.sum_fintype, ← hcover]
    _ = ∑ a, ((μ.restrict (E a)).prod ν).map f := by
      rw [Measure.prod_sum_left, Measure.map_sum hf.aemeasurable, Measure.sum_fintype]
    _ = ∑ a, μ (E a) • ν.map (g a) := by
      apply Finset.sum_congr rfl
      intro a _
      have hmem : ∀ᵐ p ∂(μ.restrict (E a)).prod ν, p.1 ∈ E a := by
        apply (Measure.ae_prod_iff_ae_ae ((hE a).preimage measurable_fst)).mpr
        filter_upwards [ae_restrict_mem (hE a)] with ω hω
        exact Filter.Eventually.of_forall (fun _ => hω)
      have heq : f =ᵐ[(μ.restrict (E a)).prod ν] (g a ∘ Prod.snd) := by
        filter_upwards [hmem] with p hp
        exact hbranch a p.1 hp p.2
      rw [Measure.map_congr heq, ← Measure.map_map (hg a) measurable_snd,
        Measure.map_snd_prod, Measure.map_smul]
      · simp
      · exact (hg a).aemeasurable

theorem selectorScalar_partition (mode : Mode) (R : ℝ) (s : State)
    (ht : 0 < totalRate mode R s) :
    unitUniform = ∑ a : ActionIndex s,
      unitUniform.restrict {v | selectorScalar mode R s v = some a} := by
  classical
  let : MeasurableSpace (Option (ActionIndex s)) := ⊤
  have hm : Measurable (selectorScalar mode R s) :=
    chooseByRate_measurable (fun b _ => (candidateRate mode R s b : ℝ))
      (fun _ => measurable_const) Finset.univ.toList
      (fun v => v * (totalRate mode R s : ℝ)) (measurable_id.mul_const _)
  let E : ActionIndex s → Set ℝ := fun a => {v | selectorScalar mode R s v = some a}
  have hE : ∀ a, MeasurableSet (E a) := fun a =>
    hm (show MeasurableSet ({some a} : Set (Option (ActionIndex s))) from by trivial)
  have hd : Pairwise (fun a b => Disjoint (E a) (E b)) := by
    intro a b hab
    apply Set.disjoint_left.mpr
    intro v ha hb
    apply hab
    exact Option.some.inj (ha.symm.trans hb)
  have hcover : (⋃ a, E a) =ᵐ[unitUniform] Set.univ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    have hu : 0 ≤ v ∧ v < 1 := ⟨hv.1.le, hv.2⟩
    obtain ⟨a, ha, _⟩ := selectedAction_exists_positive mode R s
      (fun _ => v) hu.1 hu.2 ht
    have hmem : v ∈ ⋃ a, E a := Set.mem_iUnion.mpr ⟨a, ha⟩
    exact propext ⟨fun _ => Set.mem_univ v, fun _ => hmem⟩
  calc
    unitUniform = unitUniform.restrict (⋃ a, E a) := by
      rw [Measure.restrict_congr_set hcover, Measure.restrict_univ]
    _ = ∑ a, unitUniform.restrict (E a) := by
      rw [Measure.restrict_iUnion hd hE, Measure.sum_fintype]

end Rhone.Coalescent.SmcSupport
