/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.FiniteIntervalMaterialArrayOperations

/-! # Measurability of the coalescence and split successor maps on lineage arrays -/
@[expose] public section

namespace Rhone.Coalescent.IntervalProcess
open MeasureTheory

abbrev FiberState (m : ℕ) := ℝ × ℕ × (Fin m → ℕ × Material)

@[reducible] def stateOfFiber (m : ℕ) (p : FiberState m) : State := (p.1,p.2.1,⟨m,p.2.2⟩)

theorem stateOfFiber_measurable (m : ℕ) : Measurable (stateOfFiber m) :=
  measurable_fst.prodMk (measurable_snd.fst.prodMk
    ((measurable_sigma_mk m).comp measurable_snd.snd))

theorem liveOfList_map_measurable {α δ : Type*} [MeasurableSpace δ]
    (l : List α) (f : α → δ → ℕ × Material)
    (hf : ∀ a ∈ l, Measurable (f a)) :
    Measurable (fun x => liveOfList (l.map (fun a => f a x))) := by
  have hg : Measurable (fun x : δ => fun i : Fin l.length => f (l.get i) x) :=
    measurable_pi_iff.mpr (fun i => hf _ (List.get_mem l i))
  convert (measurable_sigma_mk (β := fun m => Fin m → ℕ × Material) l.length).comp hg using 1
  funext x
  apply Sigma.ext (List.length_map (fun a => f a x))
  apply (Fin.heq_fun_iff (List.length_map (fun a => f a x))).mpr
  intro i
  simp [liveOfList, List.get_eq_getElem]

theorem coalSuccessorFiber_measurable (m : ℕ) (i j : Fin m) :
    Measurable (fun p : FiberState m => coalSuccessor (stateOfFiber m p) i j) := by
  classical
  by_cases hij : i.val < j.val
  · let survivors := (List.finRange m).filter (fun k => k ≠ i ∧ k ≠ j)
    let l : List (Fin m ⊕ Unit) := survivors.map Sum.inl ++ [Sum.inr ()]
    let f : (Fin m ⊕ Unit) → FiberState m → ℕ × Material := fun a p => match a with
      | .inl k => p.2.2 k
      | .inr _ => (p.2.1, mergeMaterial (p.2.2 i).2 (p.2.2 j).2)
    have hf (a : Fin m ⊕ Unit) : Measurable (f a) := by
      cases a with
      | inl k => exact (measurable_pi_apply k).comp measurable_snd.snd
      | inr u =>
        exact measurable_snd.fst.prodMk (mergeMaterial_measurable.comp
          ((((measurable_pi_apply i).comp measurable_snd.snd).snd).prodMk
            (((measurable_pi_apply j).comp measurable_snd.snd).snd)))
    have hlist := liveOfList_map_measurable l f (fun a _ => hf a)
    have htime : Measurable (fun p : FiberState m => p.1) := measurable_fst
    have hid : Measurable (fun p : FiberState m => p.2.1+1) := by fun_prop
    convert htime.prodMk (hid.prodMk hlist) using 1
    funext p
    simp [coalSuccessor, stateOfFiber, hij, l, f, survivors, Function.comp_def]
  · simpa only [coalSuccessor, ite_eq_right hij] using stateOfFiber_measurable m

theorem splitSuccessorFiber_measurable (m : ℕ) (i : Fin m) :
    Measurable (fun p : FiberState m × ℝ =>
      splitSuccessor (stateOfFiber m p.1) i p.2) := by
  classical
  let survivors := (List.finRange m).filter (fun k => k ≠ i)
  let l : List (Fin m ⊕ Bool) := survivors.map Sum.inl ++ [Sum.inr false,Sum.inr true]
  let f : (Fin m ⊕ Bool) → (FiberState m × ℝ) → ℕ × Material := fun a p => match a with
    | .inl k => p.1.2.2 k
    | .inr false => (p.1.2.1, (splitMaterial (p.1.2.2 i).2 p.2).1)
    | .inr true => (p.1.2.1+1, (splitMaterial (p.1.2.2 i).2 p.2).2)
  have hd : Measurable (fun p : FiberState m × ℝ =>
      splitMaterial (p.1.2.2 i).2 p.2) :=
    splitMaterial_measurable.comp
      ((((measurable_pi_apply i).comp measurable_fst.snd.snd).snd).prodMk measurable_snd)
  have hf (a : Fin m ⊕ Bool) : Measurable (f a) := by
    cases a with
    | inl k => exact (measurable_pi_apply k).comp measurable_fst.snd.snd
    | inr b =>
      cases b
      · exact measurable_fst.snd.fst.prodMk hd.fst
      · have hid : Measurable (fun p : FiberState m × ℝ => p.1.2.1+1) := by fun_prop
        exact hid.prodMk hd.snd
  have hlist := liveOfList_map_measurable l f (fun a _ => hf a)
  have htime : Measurable (fun p : FiberState m × ℝ => p.1.1) := measurable_fst.fst
  have hid : Measurable (fun p : FiberState m × ℝ => p.1.2.1+2) := by fun_prop
  convert htime.prodMk (hid.prodMk hlist) using 1
  funext p
  simp [splitSuccessor, stateOfFiber, l, f, survivors, Function.comp_def]

end Rhone.Coalescent.IntervalProcess
