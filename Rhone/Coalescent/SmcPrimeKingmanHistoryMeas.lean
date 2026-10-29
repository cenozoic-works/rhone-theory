/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeKingmanHistory
public import Rhone.Coalescent.SmcPrimeRegraftMeas

/-! # Measurability of the extraction of Kingman histories -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess MeasureTheory

theorem historyExtension_measurable (N : ℕ) :
    Measurable (historyExtension N) := by
  apply measurable_pi_iff.mpr
  intro k
  by_cases hk : k < N
  · simpa only [historyExtension, dite_eq_left hk] using
      (measurable_pi_apply (⟨k, hk⟩ : Fin N))
  · simpa only [historyExtension, dite_eq_right hk] using
      (measurable_const : Measurable (fun _ : KingmanHistory N =>
        ((initialState N, (0, .inl ())) : AugmentedState)))

theorem pairBirthTime_measurable (k : ℕ) :
    Measurable (fun p : EventPath × ℕ => pairBirthTime p.1 k p.2) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    let c (p : EventPath × ℕ) := genealogyEventCode (p.1 (k + 1)).2.2
    have he : Measurable (fun p : EventPath × ℕ => p.1 (k + 1)) :=
      (measurable_pi_apply (k + 1)).comp measurable_fst
    have ho : Measurable (fun p : EventPath × ℕ => p.1 k) :=
      (measurable_pi_apply k).comp measurable_fst
    have hc : Measurable c := genealogyEventCode_measurable.comp he.snd.snd
    have hm : Measurable (fun p : EventPath × ℕ => (p.1 k).1.2.2.1) :=
      liveCount_measurable.comp ho.fst
    have hp : MeasurableSet {p : EventPath × ℕ |
        (c p).2.1 < (c p).2.2.1 ∧ (c p).2.2.1 < (p.1 k).1.2.2.1 ∧
          p.2 = (p.1 k).1.2.1} :=
      (measurableSet_lt hc.snd.fst hc.snd.snd.fst).inter
        ((measurableSet_lt hc.snd.snd.fst hm).inter
          (measurableSet_eq_fun measurable_snd ho.fst.snd.fst))
    have hb : Measurable (fun p : EventPath × ℕ =>
        if (c p).1 = 1 then
          if (c p).2.1 < (c p).2.2.1 ∧ (c p).2.2.1 < (p.1 k).1.2.2.1 ∧
            p.2 = (p.1 k).1.2.1 then (p.1 (k + 1)).1.1 else pairBirthTime p.1 k p.2
        else pairBirthTime p.1 k p.2) :=
      (he.fst.fst.piecewise hp ih).piecewise
        (measurableSet_eq_fun hc.fst measurable_const) ih
    convert hb using 1
    funext p
    cases h : (p.1 (k + 1)).2.2 with
    | inl u => simp [pairBirthTime, c, h, genealogyEventCode]
    | inr e => cases e <;> simp [pairBirthTime, c, h, genealogyEventCode]

theorem historyClade_measurable (N k : ℕ) :
    Measurable (fun p : KingmanHistory N × ℕ => historyClade N p.1 k p.2) := by
  classical
  apply measurable_finset_iff.mpr
  intro i
  have ha : Measurable (fun p : KingmanHistory N × ℕ =>
      ancestorLabel N (historyExtension N p.1) leftBoundaryProbe i k) :=
    (ancestorLabel_measurable N leftBoundaryProbe i k).comp
      ((historyExtension_measurable N).comp measurable_fst)
  simpa only [historyClade, Finset.mem_filter, Finset.mem_univ, true_and] using
    measurableSet_setOfPred.mp (measurableSet_eq_fun ha measurable_snd)

theorem historyChildBranch_measurable (N : ℕ) (k : Fin (N - 1)) (right : Bool) :
    Measurable (fun h : KingmanHistory N => historyChildBranch N h k right) := by
  classical
  let c (h : KingmanHistory N) :=
    genealogyEventCode (historyExtension N h (k.val + 1)).2.2
  have ho : Measurable (fun h : KingmanHistory N => historyExtension N h k.val) :=
    (measurable_pi_apply k.val).comp (historyExtension_measurable N)
  have he : Measurable (fun h : KingmanHistory N => historyExtension N h (k.val + 1)) :=
    (measurable_pi_apply (k.val + 1)).comp (historyExtension_measurable N)
  have hc : Measurable c := genealogyEventCode_measurable.comp he.snd.snd
  have hidx : Measurable (fun h : KingmanHistory N =>
      if right then (c h).2.2.1 else (c h).2.1) := by
    cases right
    · exact hc.snd.fst
    · exact hc.snd.snd.fst
  let a (h : KingmanHistory N) :=
    liveLabelAt (historyExtension N h k.val).1
      (if right then (c h).2.2.1 else (c h).2.1)
  have ha : Measurable a := liveLabelAt_measurable.comp (ho.fst.prodMk hidx)
  have hb : Measurable (fun h : KingmanHistory N =>
      finiteBranch (historyClade N h k.val (a h))
        (pairBirthTime (historyExtension N h) k.val (a h))
        (historyExtension N h (k.val + 1)).1.1) :=
    (finiteBranch_measurable N).comp
      (((historyClade_measurable N k.val).comp (measurable_id.prodMk ha)).prodMk
        (((pairBirthTime_measurable k.val).comp
          ((historyExtension_measurable N).prodMk ha)).prodMk he.fst.fst))
  have hp : MeasurableSet {h : KingmanHistory N |
      (c h).2.1 < (c h).2.2.1 ∧
        (c h).2.2.1 < (historyExtension N h k.val).1.2.2.1} :=
    (measurableSet_lt hc.snd.fst hc.snd.snd.fst).inter
      (measurableSet_lt hc.snd.snd.fst (liveCount_measurable.comp ho.fst))
  have hm : Measurable (fun h : KingmanHistory N =>
      if (c h).1 = 1 then
        if (c h).2.1 < (c h).2.2.1 ∧
          (c h).2.2.1 < (historyExtension N h k.val).1.2.2.1 then
          finiteBranch (historyClade N h k.val (a h))
            (pairBirthTime (historyExtension N h) k.val (a h))
            (historyExtension N h (k.val + 1)).1.1
        else finiteBranch ∅ 0 0
      else finiteBranch ∅ 0 0) :=
    (hb.piecewise hp measurable_const).piecewise
      (measurableSet_eq_fun hc.fst measurable_const) measurable_const
  convert hm using 1
  funext h
  cases hevt : (historyExtension N h (k.val + 1)).2.2 with
  | inl u => simp [historyChildBranch, c, hevt, genealogyEventCode]
  | inr e => cases e <;> simp [historyChildBranch, c, a, hevt, genealogyEventCode]

theorem metricTreeFromHistory_measurable (N : ℕ) :
    Measurable (metricTreeFromHistory N) := by
  let l := (List.finRange (N - 1)).flatMap
    (fun k => [(k, false), (k, true)])
  have hm := treeOfList_map_measurable N l
    (fun z h => historyChildBranch N h z.1 z.2)
    (fun z _ => historyChildBranch_measurable N z.1 z.2)
  convert hm using 1
  funext h
  simp only [metricTreeFromHistory, l, List.map_flatMap, List.map_cons, List.map_nil]

end Rhone.Coalescent.SmcPrime
