/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeTreeProposal
public import Rhone.Coalescent.FiniteIntervalMaterialSamplerMeas

/-! # Measurability of source-defined SMC′ tree proposals -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess MeasureTheory

theorem branchLength_measurable (N : ℕ) : Measurable (@branchLength N) := by
  classical
  have hs : MeasurableSet {b : Branch N | b.1 = ∅ ∨ b.1 = Finset.univ} :=
    (measurableSet_eq_fun measurable_fst measurable_const).union
      (measurableSet_eq_fun measurable_fst measurable_const)
  exact measurable_const.piecewise hs
    (measurable_const.max (measurable_snd.snd.sub measurable_snd.fst))

theorem treeLengthFiber_measurable (N m : ℕ) :
    Measurable (fun f : Fin m → Branch N => treeLength ⟨m, f⟩) := by
  exact Finset.measurable_sum Finset.univ
    (fun i _ => (branchLength_measurable N).comp (measurable_pi_apply i))

theorem rootHeightFiber_measurable (N m : ℕ) :
    Measurable (fun f : Fin m → Branch N => rootHeight ⟨m, f⟩) := by
  have h (l : List (Fin m)) : Measurable (fun f : Fin m → Branch N =>
      (l.map (fun i => if 0 < branchLength (f i) then (f i).2.2 else 0)).foldr max 0) := by
    induction l with
    | nil => exact measurable_const
    | cons i l ih =>
      have hi : Measurable (fun f : Fin m → Branch N =>
          if 0 < branchLength (f i) then (f i).2.2 else 0) :=
        (measurable_pi_apply i).snd.snd.piecewise
          (measurableSet_lt measurable_const
            ((branchLength_measurable N).comp (measurable_pi_apply i))) measurable_const
      exact hi.max ih
  simpa only [rootHeight] using h (List.finRange m)

theorem activeBranchesFiber_measurable (N m : ℕ) :
    Measurable (fun p : (Fin m → Branch N) × ℝ =>
      (show Finset (Fin m) from activeBranches ⟨m, p.1⟩ p.2)) := by
  classical
  apply measurable_finset_iff.mpr
  intro i
  have hi : Measurable (fun p : (Fin m → Branch N) × ℝ => p.1 i) :=
    (measurable_pi_apply i).comp measurable_fst
  have hs : MeasurableSet {p : (Fin m → Branch N) × ℝ |
      0 < branchLength (p.1 i) ∧ (p.1 i).2.1 ≤ p.2 ∧ p.2 < (p.1 i).2.2} :=
    (measurableSet_lt measurable_const ((branchLength_measurable N).comp hi)).inter
      ((measurableSet_le hi.snd.fst measurable_snd).inter
        (measurableSet_lt measurable_snd hi.snd.snd))
  simpa only [activeBranches, Finset.mem_filter, Finset.mem_univ, true_and] using
    measurableSet_setOfPred.mp hs

theorem attachmentRateFiber_measurable (N m : ℕ) :
    Measurable (fun p : (Fin m → Branch N) × ℝ => attachmentRate ⟨m, p.1⟩ p.2) := by
  have hcard : Measurable (fun s : Finset (Fin m) => (s.card : ℝ)) :=
    measurable_of_countable _
  exact measurable_const.piecewise
    (measurableSet_le ((rootHeightFiber_measurable N m).comp measurable_fst) measurable_snd)
    (hcard.comp (activeBranchesFiber_measurable N m))

theorem nextBoundaryFiber_measurable (N m : ℕ) :
    Measurable (fun p : (Fin m → Branch N) × ℝ => nextBoundary ⟨m, p.1⟩ p.2) := by
  classical
  have h (l : List (Fin m)) : Measurable (fun p : (Fin m → Branch N) × ℝ =>
      (l.flatMap (fun i => [(p.1 i).2.1, (p.1 i).2.2])).foldr
        (fun v a => if p.2 < v then min v a else a) (rootHeight ⟨m, p.1⟩)) := by
    induction l with
    | nil => exact (rootHeightFiber_measurable N m).comp measurable_fst
    | cons i l ih =>
      have hi : Measurable (fun p : (Fin m → Branch N) × ℝ => p.1 i) :=
        (measurable_pi_apply i).comp measurable_fst
      let tail (p : (Fin m → Branch N) × ℝ) :=
        (l.flatMap (fun j => [(p.1 j).2.1, (p.1 j).2.2])).foldr
          (fun v a => if p.2 < v then min v a else a) (rootHeight ⟨m, p.1⟩)
      have hh : Measurable (fun p : (Fin m → Branch N) × ℝ =>
          if p.2 < (p.1 i).2.2 then min (p.1 i).2.2 (tail p) else tail p) :=
        (hi.snd.snd.min ih).piecewise
        (s := {p : (Fin m → Branch N) × ℝ | p.2 < (p.1 i).2.2})
        (measurableSet_lt measurable_snd hi.snd.snd) ih
      have hlo : Measurable (fun p : (Fin m → Branch N) × ℝ =>
          if p.2 < (p.1 i).2.1 then
            min (p.1 i).2.1 (if p.2 < (p.1 i).2.2 then min (p.1 i).2.2 (tail p) else tail p)
          else if p.2 < (p.1 i).2.2 then min (p.1 i).2.2 (tail p) else tail p) :=
        (hi.snd.fst.min hh).piecewise
        (s := {p : (Fin m → Branch N) × ℝ | p.2 < (p.1 i).2.1})
        (measurableSet_lt measurable_snd hi.snd.fst) hh
      exact hlo
  simpa only [nextBoundary] using h (List.finRange m)

theorem attachmentAuxFiber_measurable (N m k : ℕ) :
    Measurable (fun p : (Fin m → Branch N) × ℝ × ℝ =>
      attachmentAux ⟨m, p.1⟩ k p.2.1 p.2.2) := by
  classical
  induction k with
  | zero => exact measurable_snd.fst.add measurable_snd.snd
  | succ k ih =>
    have ht : Measurable (fun p : (Fin m → Branch N) × ℝ × ℝ => p.2.1) :=
      measurable_snd.fst
    have he : Measurable (fun p : (Fin m → Branch N) × ℝ × ℝ => p.2.2) :=
      measurable_snd.snd
    have hn := (nextBoundaryFiber_measurable N m).comp (measurable_fst.prodMk ht)
    have hr := (attachmentRateFiber_measurable N m).comp (measurable_fst.prodMk ht)
    have hb := hr.mul (hn.sub ht)
    have hnext := ih.comp (measurable_fst.prodMk (hn.prodMk (he.sub hb)))
    have hinside : Measurable (fun p : (Fin m → Branch N) × ℝ × ℝ =>
        if p.2.2 < attachmentRate ⟨m, p.1⟩ p.2.1 *
            (nextBoundary ⟨m, p.1⟩ p.2.1 - p.2.1) then
          p.2.1 + p.2.2 / attachmentRate ⟨m, p.1⟩ p.2.1 else
          attachmentAux ⟨m, p.1⟩ k (nextBoundary ⟨m, p.1⟩ p.2.1)
            (p.2.2 - attachmentRate ⟨m, p.1⟩ p.2.1 *
              (nextBoundary ⟨m, p.1⟩ p.2.1 - p.2.1))) :=
      (ht.add (he.div hr)).piecewise
      (s := {p : (Fin m → Branch N) × ℝ × ℝ |
        p.2.2 < attachmentRate ⟨m, p.1⟩ p.2.1 *
          (nextBoundary ⟨m, p.1⟩ p.2.1 - p.2.1)})
      (measurableSet_lt he hb) hnext
    exact (ht.add he).piecewise
      (measurableSet_le ((rootHeightFiber_measurable N m).comp measurable_fst) ht) hinside

end Rhone.Coalescent.SmcPrime
