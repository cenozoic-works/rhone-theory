/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.FiniteIntervalMaterialSuccessorMeas
public import Rhone.Coalescent.FiniteIntervalMaterialSelection

/-! # Measurability of the finite candidate rates and the sampler step -/
@[expose] public section

namespace Rhone.Coalescent.IntervalProcess
open MeasureTheory
open scoped BigOperators

theorem measurable_countable_choice {α δ γ : Type*} [Countable α]
    [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace δ]
    [MeasurableSpace γ] (g : δ → α) (hg : Measurable g)
    (f : α → δ → γ) (hf : ∀ a, Measurable (f a)) :
    Measurable (fun x => f (g x) x) := by
  intro t ht
  have heq : (fun x => f (g x) x) ⁻¹' t =
      ⋃ a, g ⁻¹' {a} ∩ (f a) ⁻¹' t := by
    ext x
    constructor
    · intro hx
      exact Set.mem_iUnion.mpr ⟨g x, rfl, hx⟩
    · intro hx
      obtain ⟨a, ha, hx⟩ := Set.mem_iUnion.mp hx
      have he : g x = a := ha
      change f a x ∈ t at hx
      change f (g x) x ∈ t
      rw [he]
      exact hx
  rw [heq]
  exact MeasurableSet.iUnion (fun a => (hg (measurableSet_singleton a)).inter (hf a ht))

theorem candidateRateFiber_coe_measurable (mode : Mode) (R : ℝ)
    (m : ℕ) (a : (Fin m × Fin m) ⊕ Fin m) :
    Measurable (fun p : FiberState m => (candidateRate mode R (stateOfFiber m p) a : ℝ)) := by
  classical
  cases a with
  | inl ij =>
    have heq : (fun p : FiberState m =>
        (candidateRate mode R (stateOfFiber m p) (.inl ij) : ℝ)) =
        (fun p => if ij.1.val < ij.2.val ∧
          (mode = false ∨ touches (p.2.2 ij.1).2 (p.2.2 ij.2).2) then 1 else 0) := by
      funext p
      simp only [candidateRate, stateOfFiber]
      split_ifs <;> rfl
    rw [heq]
    by_cases hij : ij.1.val < ij.2.val
    · have hi : Measurable (fun p : FiberState m => (p.2.2 ij.1).2) :=
        ((measurable_pi_apply ij.1).comp measurable_snd.snd).snd
      have hj : Measurable (fun p : FiberState m => (p.2.2 ij.2).2) :=
        ((measurable_pi_apply ij.2).comp measurable_snd.snd).snd
      have hc : MeasurableSet {p : FiberState m | touches (p.2.2 ij.1).2 (p.2.2 ij.2).2} :=
        (measurableSet_le (hullLo_measurable.comp hi) (hullHi_measurable.comp hj)).inter
          (measurableSet_le (hullLo_measurable.comp hj) (hullHi_measurable.comp hi))
      cases mode
      · simp [hij]
      · convert (measurable_const.piecewise hc measurable_const :
            Measurable (fun p : FiberState m =>
              if touches (p.2.2 ij.1).2 (p.2.2 ij.2).2 then (1 : ℝ) else 0)) using 1
        funext p
        simp [hij]
        rfl
    · simp [hij]
  | inr i =>
    change Measurable (fun p : FiberState m =>
      (R.toNNReal : ℝ) / 2 * hullLength (p.2.2 i).2)
    exact measurable_const.mul (hullLength_measurable.comp
      (((measurable_pi_apply i).comp measurable_snd.snd).snd))

theorem totalRateFiber_coe_measurable (mode : Mode) (R : ℝ) (m : ℕ) :
    Measurable (fun p : FiberState m => (totalRate mode R (stateOfFiber m p) : ℝ)) := by
  simp only [totalRate, NNReal.coe_sum]
  exact Finset.measurable_sum Finset.univ (fun a _ => candidateRateFiber_coe_measurable mode R m a)

theorem sampleStepFiber_measurable (mode : Mode) (R : ℝ) (m : ℕ) :
    Measurable (fun p : FiberState m × Noise =>
      sampleStep mode R (stateOfFiber m p.1) p.2) := by
  classical
  let α := Option ((Fin m × Fin m) ⊕ Fin m)
  let : MeasurableSpace α := ⊤
  let g : FiberState m × Noise → α := fun p =>
    selectedAction mode R (stateOfFiber m p.1) p.2
  have hr : Measurable (fun p : FiberState m × Noise =>
      (totalRate mode R (stateOfFiber m p.1) : ℝ)) :=
    (totalRateFiber_coe_measurable mode R m).comp measurable_fst
  have hg : Measurable g := by
    exact chooseByRate_measurable
      (fun a (p : FiberState m × Noise) =>
        (candidateRate mode R (stateOfFiber m p.1) a : ℝ))
      (fun a => (candidateRateFiber_coe_measurable mode R m a).comp measurable_fst)
      Finset.univ.toList (fun p => p.2 0 * (totalRate mode R (stateOfFiber m p.1) : ℝ))
      (((measurable_pi_apply 0).comp measurable_snd).mul hr)
  let t : FiberState m × Noise → ℝ := fun p =>
    p.1.1 - Real.log (p.2 1) / (totalRate mode R (stateOfFiber m p.1) : ℝ)
  have ht : Measurable t :=
    measurable_fst.fst.sub ((Real.measurable_log.comp
      ((measurable_pi_apply 1).comp measurable_snd)).div hr)
  let f : α → (FiberState m × Noise) → State × EventRecord := fun a p => match a with
    | none => (stateOfFiber m p.1, (p.1.1, .inl ()))
    | some (.inl ij) =>
      (atTime (t p) (coalSuccessor (stateOfFiber m p.1) ij.1 ij.2),
        (t p, .inr (.inl (ij.1.val,ij.2.val))))
    | some (.inr i) =>
      let x := hullLo (p.1.2.2 i).2 + hullLength (p.1.2.2 i).2 * p.2 2
      (atTime (t p) (splitSuccessor (stateOfFiber m p.1) i x),
        (t p, .inr (.inr (i.val,x))))
  have hf (a : α) : Measurable (f a) := by
    cases a with
    | none =>
      exact ((stateOfFiber_measurable m).comp measurable_fst).prodMk
        (measurable_fst.fst.prodMk measurable_const)
    | some a =>
      cases a with
      | inl ij =>
        have hc : Measurable (fun p : FiberState m × Noise =>
            coalSuccessor (stateOfFiber m p.1) ij.1 ij.2) :=
          (coalSuccessorFiber_measurable m ij.1 ij.2).comp measurable_fst
        exact (ht.prodMk hc.snd).prodMk (ht.prodMk measurable_const)
      | inr i =>
        have hm : Measurable (fun p : FiberState m × Noise => (p.1.2.2 i).2) :=
          ((measurable_pi_apply i).comp measurable_fst.snd.snd).snd
        have hx : Measurable (fun p : FiberState m × Noise =>
            hullLo (p.1.2.2 i).2 + hullLength (p.1.2.2 i).2 * p.2 2) :=
          (hullLo_measurable.comp hm).add ((hullLength_measurable.comp hm).mul
            ((measurable_pi_apply 2).comp measurable_snd))
        have hc := (splitSuccessorFiber_measurable m i).comp (measurable_fst.prodMk hx)
        have he : Measurable (fun p : FiberState m × Noise =>
            (Sum.inr (Sum.inr (i.val,
              hullLo (p.1.2.2 i).2 + hullLength (p.1.2.2 i).2 * p.2 2)) : Event)) :=
          measurable_inr.comp (measurable_inr.comp (measurable_const.prodMk hx))
        exact (ht.prodMk hc.snd).prodMk (ht.prodMk he)
  have hchosen := measurable_countable_choice g hg f hf
  have hstop : Measurable (fun p : FiberState m × Noise =>
      (stateOfFiber m p.1, ((p.1.1, Sum.inl ()) : EventRecord))) :=
    ((stateOfFiber_measurable m).comp measurable_fst).prodMk
      (measurable_fst.fst.prodMk measurable_const)
  have hs : MeasurableSet {p : FiberState m × Noise |
      m ≤ 1 ∨ totalRate mode R (stateOfFiber m p.1) = 0} := by
    by_cases hm : m ≤ 1
    · simp [hm]
    · have hz : MeasurableSet {p : FiberState m × Noise |
          (totalRate mode R (stateOfFiber m p.1) : ℝ) = 0} :=
        hr (measurableSet_singleton (0 : ℝ))
      convert hz using 1
      ext p
      simp [hm]
  convert hstop.piecewise hs hchosen using 1
  · funext p
    unfold sampleStep Set.piecewise
    dsimp only [g, f, t, stateOfFiber, Set.mem_ofPred_eq]
    split_ifs
    · rfl
    · cases selectedAction mode R (stateOfFiber m p.1) p.2 with
      | none => rfl
      | some a => cases a <;> rfl
  · infer_instance

theorem sampleStep_measurable (mode : Mode) (R : ℝ) :
    Measurable (fun p : State × Noise => sampleStep mode R p.1 p.2) := by
  let f : LiveState × (ℝ × ℕ × Noise) → State × EventRecord := fun p =>
    sampleStep mode R (p.2.1,p.2.2.1,p.1) p.2.2.2
  have hf : Measurable f := by
    apply measurable_prod_sigma_of_fibers
    intro m
    exact (sampleStepFiber_measurable mode R m).comp
      ((measurable_snd.fst.prodMk (measurable_snd.snd.fst.prodMk measurable_fst)).prodMk
        measurable_snd.snd.snd)
  exact hf.comp (measurable_fst.snd.snd.prodMk
    (measurable_fst.fst.prodMk (measurable_fst.snd.fst.prodMk measurable_snd)))

end Rhone.Coalescent.IntervalProcess
