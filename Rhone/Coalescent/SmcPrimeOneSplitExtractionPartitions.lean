/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitExtraction

/-! # Left ancestor labels and partition updates during one-split extraction -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime

def SameLeftPartition {N : ℕ} (f g : Fin N → ℕ) : Prop :=
  ∀ i j, f i = f j ↔ g i = g j

theorem sameLeftPartition_replace {N : ℕ} (f : Fin N → ℕ) (a fresh : ℕ)
    (hfresh : ∀ i, f i ≠ fresh) :
    SameLeftPartition f (fun i => if f i = a then fresh else f i) := by
  intro i j
  by_cases hi : f i = a <;> by_cases hj : f j = a
  · simp only [hi, hj, ite_true, iff_self]
  · simp only [hi, hj, ite_true, ite_false]
    exact iff_of_false (Ne.symm hj) (Ne.symm (hfresh j))
  · simp only [hi, hj, ite_true, ite_false, hfresh i]
  · simp only [hi, hj, ite_false]

theorem sameLeftPartition_merge {N : ℕ} (f g : Fin N → ℕ)
    (hfg : SameLeftPartition f g) (u v : Fin N) (freshF freshG : ℕ)
    (hfresh : ∀ i, f i ≠ freshF) (gfresh : ∀ i, g i ≠ freshG) :
    SameLeftPartition
      (fun i => if f i = f u ∨ f i = f v then freshF else f i)
      (fun i => if g i = g u ∨ g i = g v then freshG else g i) := by
  intro i j
  have hhi : (f i = f u ∨ f i = f v) ↔ (g i = g u ∨ g i = g v) :=
    or_congr (hfg i u) (hfg i v)
  have hhj : (f j = f u ∨ f j = f v) ↔ (g j = g u ∨ g j = g v) :=
    or_congr (hfg j u) (hfg j v)
  by_cases hi : f i = f u ∨ f i = f v <;>
    by_cases hj : f j = f u ∨ f j = f v
  · simp only [ite_eq_left hi, ite_eq_left hj, ite_eq_left (hhi.mp hi),
      ite_eq_left (hhj.mp hj)]
  · simp only [ite_eq_left hi, ite_eq_right hj, ite_eq_left (hhi.mp hi),
      ite_eq_right (not_congr hhj |>.mp hj), Ne.symm (hfresh j), Ne.symm (gfresh j)]
  · simp only [ite_eq_right hi, ite_eq_left hj,
      ite_eq_right (not_congr hhi |>.mp hi), ite_eq_left (hhj.mp hj), hfresh i, gfresh i]
  · simp only [ite_eq_right hi, ite_eq_right hj,
      ite_eq_right (not_congr hhi |>.mp hi), ite_eq_right (not_congr hhj |>.mp hj)]
    exact hfg i j

theorem SameLeftPartition.replace_fresh {N : ℕ} {f g : Fin N → ℕ}
    (hfg : SameLeftPartition f g) (a fresh : ℕ) (hfresh : ∀ i, f i ≠ fresh) :
    SameLeftPartition (fun i => if f i = a then fresh else f i) g := by
  intro i j
  exact (sameLeftPartition_replace f a fresh hfresh i j).symm.trans (hfg i j)

end Rhone.Coalescent.SmcPrime
