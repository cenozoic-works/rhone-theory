/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.ProbabilityCellTransport
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Exact transport under injective recoding and real coordinate permutations -/

@[expose] public section
namespace Rhone.Probability.MeasureTransport
open MeasureTheory
open scoped Function

abbrev MarkedClocks (n : ℕ) := (Fin n → ℝ) × ℝ

def clockPermutation {n : ℕ} (p : Equiv.Perm (Fin n)) :
    MarkedClocks n ≃ᵐ MarkedClocks n :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) p).prodCongr
    (MeasurableEquiv.refl ℝ)

theorem clockPermutation_preserving {n : ℕ} (p : Equiv.Perm (Fin n)) :
    MeasurePreserving (clockPermutation p) volume volume := by
  exact (volume_measurePreserving_piCongrLeft (fun _ : Fin n => ℝ) p).prod
    (MeasurePreserving.id volume)

theorem clockPermutation_eq {n : ℕ} (z : MarkedClocks n)
    (hz : Function.Injective z.1) (p q : Equiv.Perm (Fin n))
    (hpq : clockPermutation p z = clockPermutation q z) : p = q := by
  apply Equiv.ext
  intro i
  have heq := congrArg (fun w : MarkedClocks n => w.1 (p i)) hpq
  change (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) p) z.1 (p i) =
    (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) q) z.1 (p i) at heq
  rw [MeasurableEquiv.piCongrLeft_apply_apply] at heq
  have hr : (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) q) z.1 (p i) =
      z.1 (q.symm (p i)) := by
    simpa only [q.apply_symm_apply] using
      (MeasurableEquiv.piCongrLeft_apply_apply q (β := fun _ : Fin n => ℝ)
        z.1 (q.symm (p i)))
  rw [hr] at heq
  simpa only [q.apply_symm_apply] using (congrArg q (hz heq)).symm

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β] [Countable α] [Countable β]

theorem markedPermutation_transport (n : ℕ) (A : Set (α × MarkedClocks n))
    (hA : MeasurableSet A) (F : α × MarkedClocks n → β × MarkedClocks n)
    (hF : Measurable F) (hinj : Set.InjOn F A)
    (hdistinct : ∀ z ∈ A, Function.Injective z.2.1)
    (hperm : ∀ z ∈ A, ∃ p : Equiv.Perm (Fin n), (F z).2 = clockPermutation p z.2) :
    MeasurableSet (F '' A) ∧
      (((Measure.count : Measure α).prod volume).restrict A).map F =
        ((Measure.count : Measure β).prod volume).restrict (F '' A) := by
  classical
  let I := α × β × Equiv.Perm (Fin n)
  let C : I → Set (α × MarkedClocks n) := fun k =>
    {z | z ∈ A ∧ z.1 = k.1 ∧ (F z).1 = k.2.1 ∧
      (F z).2 = clockPermutation k.2.2 z.2}
  have hC (k : I) : MeasurableSet (C k) := by
    apply hA.inter
    apply ((measurableSet_singleton k.1).preimage measurable_fst).inter
    apply ((measurableSet_singleton k.2.1).preimage hF.fst).inter
    exact measurableSet_eq_fun hF.snd ((clockPermutation k.2.2).measurable.comp measurable_snd)
  have hCA (k : I) : C k ⊆ A := fun _ hz => hz.1
  have hdis : Pairwise (Disjoint on C) := by
    intro k l hkl
    apply Set.disjoint_left.mpr
    intro z hz hz'
    apply hkl
    apply Prod.ext (hz.2.1.symm.trans hz'.2.1)
    apply Prod.ext (hz.2.2.1.symm.trans hz'.2.2.1)
    exact clockPermutation_eq z.2 (hdistinct z hz.1) k.2.2 l.2.2
      (hz.2.2.2.symm.trans hz'.2.2.2)
  have hcover : A = ⋃ k, C k := by
    ext z
    constructor
    · intro hz
      obtain ⟨p, hp⟩ := hperm z hz
      exact Set.mem_iUnion.mpr ⟨(z.1, (F z).1, p), hz, rfl, rfl, hp⟩
    · intro hz
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hz
      exact hk.1
  have hcell (k : I) : MeasurableSet (F '' C k) ∧
      (((Measure.count : Measure α).prod volume).restrict (C k)).map F =
        ((Measure.count : Measure β).prod volume).restrict (F '' C k) := by
    apply markCell_transport volume k.1 k.2.1 (C k) (hC k)
      (fun _ hz => hz.2.1) F hF (clockPermutation k.2.2)
      (clockPermutation_preserving k.2.2)
    intro z hz
    exact Prod.ext hz.2.2.1 hz.2.2.2
  have himdis : Pairwise (Disjoint on fun k => F '' C k) := by
    intro k l hkl
    apply Set.disjoint_left.mpr
    rintro y ⟨z, hz, hzy⟩ ⟨w, hw, hwy⟩
    have he : z = w := hinj (hCA k hz) (hCA l hw) (hzy.trans hwy.symm)
    exact Set.disjoint_left.mp (hdis hkl) hz (he ▸ hw)
  have him : F '' A = ⋃ k, F '' C k := by
    rw [hcover, Set.image_iUnion]
  refine ⟨by rw [him]; exact MeasurableSet.iUnion (fun k => (hcell k).1), ?_⟩
  rw [hcover, Measure.restrict_iUnion hdis hC, Measure.map_sum hF.aemeasurable,
    Set.image_iUnion, Measure.restrict_iUnion himdis (fun k => (hcell k).1)]
  congr 1
  funext k
  exact (hcell k).2

end Rhone.Probability.MeasureTransport
