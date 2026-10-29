/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeExtractionStateMeas
/-! # Measurability of one step of the one-split extraction -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess MeasureTheory
theorem extractionStep_measurable (N : ℕ) :
    Measurable (fun p : OneSplitExtractionState N × (AugmentedState × AugmentedState) =>
      extractionStep p.1 p.2.1 p.2.2) := by
  classical
  let P := OneSplitExtractionState N × (AugmentedState × AugmentedState)
  have ho := (extractionOld_measurable N).comp
    (measurable_fst : Measurable (fun p : P => p.1))
  have hl := (extractionOldLabels_measurable N).comp
    (measurable_fst : Measurable (fun p : P => p.1))
  have hp := (extractionARGLabels_measurable N).comp
    (measurable_fst : Measurable (fun p : P => p.1))
  have hd := (extractionDetached_measurable N).comp
    (measurable_fst : Measurable (fun p : P => p.1))
  have hh := (extractionOldHistory_measurable N).comp
    (measurable_fst : Measurable (fun p : P => p.1))
  have hm := (extractionMergers_measurable N).comp
    (measurable_fst : Measurable (fun p : P => p.1))
  have hc := (extractionCut_measurable N).comp
    (measurable_fst : Measurable (fun p : P => p.1))
  have hb := (extractionAttachment_measurable N).comp
    (measurable_fst : Measurable (fun p : P => p.1))
  let f (p : P) := fun i => ancestorStep p.2.1.1 p.2.2.2.2 leftBoundaryProbe (p.1.argLabels i)
  have hf : Measurable f := measurable_pi_iff.mpr (fun i =>
    (ancestorStep_measurable leftBoundaryProbe).comp
      (measurable_snd.fst.fst.prodMk (measurable_snd.snd.snd.snd.prodMk
        ((measurable_pi_apply i).comp hp))))
  let code (p : P) := genealogyEventCode p.2.2.2.2
  have hcode : Measurable code := genealogyEventCode_measurable.comp measurable_snd.snd.snd.snd
  let a (p : P) := liveLabelAt p.2.1.1 (code p).2.1
  let b (p : P) := liveLabelAt p.2.1.1 (code p).2.2.1
  have ha : Measurable a := liveLabelAt_measurable.comp
    (measurable_snd.fst.fst.prodMk hcode.snd.fst)
  have hB : Measurable b := liveLabelAt_measurable.comp
    (measurable_snd.fst.fst.prodMk hcode.snd.snd.fst)
  let c (p : P) := extractionClade p.1.argLabels (a p)
  let d (p : P) := extractionClade p.1.argLabels (b p)
  have hcl : Measurable c := (extractionClade_measurable N).comp (hp.prodMk ha)
  have hdl : Measurable d := (extractionClade_measurable N).comp (hp.prodMk hB)
  have hSome : Measurable (some : ℕ → Option ℕ) := measurable_of_countable _
  have hDa : MeasurableSet {p : P | p.1.detached = some (a p)} :=
    measurableSet_eq_fun hd (hSome.comp ha)
  have hDb : MeasurableSet {p : P | p.1.detached = some (b p)} :=
    measurableSet_eq_fun hd (hSome.comp hB)
  let target (p : P) := if p.1.detached = some (a p) then b p else a p
  have htarget : Measurable target := hB.ite hDa ha
  have htc := (extractionClade_measurable N).comp (hp.prodMk htarget)
  let oldNext (p : P) := rebuildCoal (p.1.old,p.1.oldLabels,p.1.oldLabels,none)
    p.2.2.1.1 (rebuildSampleUID p.1.oldLabels (c p))
      (rebuildSampleUID p.1.oldLabels (d p))
  have hnext : Measurable oldNext := (rebuildCoal_measurable N).comp
    ((ho.prodMk (hl.prodMk (hl.prodMk measurable_const))).prodMk
      (measurable_snd.snd.fst.fst.prodMk
        (((rebuildSampleUID_measurable N).comp (hl.prodMk hcl)).prodMk
          ((rebuildSampleUID_measurable N).comp (hl.prodMk hdl)))))
  let idle (p : P) : OneSplitExtractionState N := { p.1 with argLabels := f p }
  have hidle : Measurable idle := extractionState_mk_measurable N _ _ _ _ _ _ _ _
    ho hl hf hd hh hm hc hb
  let split (p : P) : OneSplitExtractionState N :=
    { p.1 with argLabels := f p
               detached := some (p.2.1.1.2.1 + 1)
               cut := (c p,p.2.2.1.1,(code p).2.2.2) }
  have hsplit : Measurable split := extractionState_mk_measurable N _ _ _ _ _ _ _ _
    ho hl hf (hSome.comp (measurable_snd.fst.fst.snd.fst.add_const 1)) hh hm
    (hcl.prodMk (measurable_snd.snd.fst.fst.prodMk hcode.snd.snd.snd)) hb
  let attach (p : P) : OneSplitExtractionState N :=
    { p.1 with argLabels := f p
               detached := none
               attachment := (p.2.2.1.1,extractionClade p.1.argLabels (target p)) }
  have hatt : Measurable attach := extractionState_mk_measurable N _ _ _ _ _ _ _ _
    ho hl hf measurable_const hh hm hc (measurable_snd.snd.fst.fst.prodMk htc)
  let coal (p : P) : OneSplitExtractionState N :=
    { p.1 with old := (oldNext p).1
               oldLabels := (oldNext p).2.1
               argLabels := f p
               oldHistory := if hj : p.1.mergers + 1 < N then
                 Function.update p.1.oldHistory ⟨p.1.mergers + 1,hj⟩ (oldNext p).1
                 else p.1.oldHistory
               mergers := p.1.mergers + 1 }
  have hcoal : Measurable coal := extractionState_mk_measurable N _ _ _ _ _ _ _ _
    hnext.fst hnext.snd.fst hf hd
    ((extractionHistoryUpdate_measurable N).comp ((hh.prodMk hm).prodMk hnext.fst))
    (hm.add_const 1) hc hb
  let pair (p : P) := if p.1.detached = some (a p) ∨ p.1.detached = some (b p)
    then attach p else coal p
  have hpair : Measurable pair := hatt.ite (hDa.union hDb) hcoal
  let result (p : P) := if (code p).1 = 0 then idle p
    else if (code p).1 = 1 then pair p else split p
  have hr : Measurable result := hidle.ite (measurableSet_eq_fun hcode.fst measurable_const)
    (hpair.ite (measurableSet_eq_fun hcode.fst measurable_const) hsplit)
  convert hr using 1
  funext p
  dsimp only [result, code]
  have hdet (a b : ℕ) : (∃ d, p.1.detached = some d ∧ (d = a ∨ d = b)) ↔
      p.1.detached = some a ∨ p.1.detached = some b := by
    constructor
    · rintro ⟨d,hd,h | h⟩ <;> subst d
      · exact Or.inl hd
      · exact Or.inr hd
    · rintro (h | h)
      · exact ⟨a,h,Or.inl rfl⟩
      · exact ⟨b,h,Or.inr rfl⟩
  rcases p with ⟨z,pre,nextState,nextClock,nextEvent⟩
  cases nextEvent with
  | inl u => simp [genealogyEventCode, extractionStep, idle, f]
  | inr e => cases e with
    | inl ij =>
      simp only [extractionStep, hdet, genealogyEventCode, one_ne_zero, ↓reduceIte,
        pair, a, code, b, attach, f, target, coal, oldNext, c, d]
      split <;> simp_all only [measurableSet_setOfPred, Function.comp_apply,
        OneSplitExtractionState.mk.injEq, Prod.mk.injEq, true_and, not_or]
      all_goals rfl
    | inr ix => simp [genealogyEventCode, extractionStep, split, c, a, code, f]
end Rhone.Coalescent.SmcPrime
