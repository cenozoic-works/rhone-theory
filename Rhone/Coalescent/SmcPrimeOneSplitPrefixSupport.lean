/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeARGTransition
public import Rhone.Coalescent.SmcSupport.ARGFiniteHistory

/-! # Support of finite terminal ARG prefixes with exactly one split -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport MeasureTheory

def oneSplitPrefixSector (N : ℕ) : Set (ARGPrefix (N + 1)) :=
  {h | (∃ s : Fin (N + 1),
    (h ⟨s.val + 1, Finset.mem_Iic.mpr (by have := s.isLt; omega)⟩).2.2 ∈ splitSet ∧
    ∀ k : Fin (N + 1), k ≠ s →
      (h ⟨k.val + 1, Finset.mem_Iic.mpr (by have := k.isLt; omega)⟩).2.2 ∈ coalSet) ∧
    (h ⟨N + 1, Finset.mem_Iic.mpr le_rfl⟩).1.2.2.1 = 1}

def OneSplitPrefixSupported (N : ℕ) (h : ARGPrefix (N + 1)) : Prop :=
  h ⟨0, Finset.mem_Iic.mpr (Nat.zero_le _)⟩ = (initialState N, (0, .inl ())) ∧
  (∀ k, Valid (h k).1) ∧
  (∀ k : Fin (N + 1), ARGTransition
    (h ⟨k.val, Finset.mem_Iic.mpr (by have := k.isLt; omega)⟩,
      h ⟨k.val + 1, Finset.mem_Iic.mpr (by have := k.isLt; omega)⟩)) ∧
  (∀ k, (h k).2.1 = (h k).1.1) ∧ h ∈ oneSplitPrefixSector N

theorem oneSplitPrefixSector_measurable (N : ℕ) : MeasurableSet (oneSplitPrefixSector N) := by
  have hs : MeasurableSet {h : ARGPrefix (N + 1) | ∃ s : Fin (N + 1),
      (h ⟨s.val + 1, Finset.mem_Iic.mpr (by have := s.isLt; omega)⟩).2.2 ∈ splitSet ∧
      ∀ k : Fin (N + 1), k ≠ s →
        (h ⟨k.val + 1, Finset.mem_Iic.mpr (by have := k.isLt; omega)⟩).2.2 ∈ coalSet} := by
    apply measurableSet_exists
    intro s
    apply (splitSet_measurable.preimage (measurable_pi_apply _).snd.snd).inter
    apply measurableSet_forall
    intro k
    by_cases hk : k = s
    · simp [hk]
    · have hcoal : MeasurableSet {h : ARGPrefix (N + 1) |
          (h ⟨k.val + 1, Finset.mem_Iic.mpr (by have := k.isLt; omega)⟩).2.2 ∈ coalSet} :=
        coalSet_measurable.preimage (measurable_pi_apply _).snd.snd
      convert hcoal using 1
      ext h
      exact ⟨fun hh => hh hk, fun hh _ => hh⟩
  exact hs.inter (measurableSet_eq_fun
    (IntervalProcess.liveCount_measurable.comp (measurable_pi_apply _).fst) measurable_const)

theorem OneSplitPrefixSupported_measurable (N : ℕ) :
    MeasurableSet {h : ARGPrefix (N + 1) | OneSplitPrefixSupported N h} := by
  have hi : MeasurableSet {h : ARGPrefix (N + 1) |
      h ⟨0, Finset.mem_Iic.mpr (Nat.zero_le _)⟩ =
        (initialState N, (0, .inl ()))} := measurableSet_eq_fun
    (measurable_pi_apply (⟨0, Finset.mem_Iic.mpr (Nat.zero_le (N + 1))⟩ : Finset.Iic (N + 1)))
    (measurable_const (a := ((initialState N, (0, .inl ())) : AugmentedState)))
  have hv : MeasurableSet {h : ARGPrefix (N + 1) | ∀ k, Valid (h k).1} :=
    measurableSet_forall _
      (fun k => validState_measurable.preimage (measurable_pi_apply k).fst)
  have ht : MeasurableSet {h : ARGPrefix (N + 1) | ∀ k : Fin (N + 1), ARGTransition
      (h ⟨k.val, Finset.mem_Iic.mpr (by have := k.isLt; omega)⟩,
        h ⟨k.val + 1, Finset.mem_Iic.mpr (by have := k.isLt; omega)⟩)} :=
    measurableSet_forall _ (fun _ =>
      ARGTransition_measurable.preimage ((measurable_pi_apply _).prodMk (measurable_pi_apply _)))
  have hc : MeasurableSet {h : ARGPrefix (N + 1) | ∀ k, (h k).2.1 = (h k).1.1} :=
    measurableSet_forall _ (fun k => measurableSet_eq_fun
      (measurable_pi_apply k).snd.fst (measurable_pi_apply k).fst.fst)
  exact hi.inter (hv.inter (ht.inter (hc.inter (oneSplitPrefixSector_measurable N))))

noncomputable def oneSplitARGPrefixLaw (N : ℕ) (R : ℝ) : Measure (ARGPrefix (N + 1)) :=
  (argPrefixLaw R (initialState N, (0, .inl ())) (N + 1)).restrict (oneSplitPrefixSector N)

theorem oneSplitARGPrefixLaw_supported (N : ℕ) (R : ℝ) :
    ∀ᵐ h ∂oneSplitARGPrefixLaw N R, OneSplitPrefixSupported N h := by
  have hbase : ∀ᵐ h ∂argPrefixLaw R (initialState N, (0, .inl ())) (N + 1),
      h ∈ oneSplitPrefixSector N → OneSplitPrefixSupported N h := by
    unfold argPrefixLaw
    have hf : Measurable (fun ω : EventPath => fun k : Finset.Iic (N + 1) => ω k.val) :=
      measurable_pi_iff.mpr (fun k => measurable_pi_apply k.val)
    have hImp : MeasurableSet {h : ARGPrefix (N + 1) |
        h ∈ oneSplitPrefixSector N → OneSplitPrefixSupported N h} := by
      convert (oneSplitPrefixSector_measurable N).compl.union
        (OneSplitPrefixSupported_measurable N) using 1
      ext h
      simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq, imp_iff_not_or]
    apply (ae_map_iff hf.aemeasurable hImp).mpr
    filter_upwards [eventProcess_chronologicalAncestryPath N false R,
      eventProcess_ARGTransition R (initialState N, (0, .inl ()))] with ω hc ht
    intro hsector
    refine ⟨hc.1, ?_, ?_, ?_, hsector⟩
    · intro k
      exact hc.valid k.val
    · intro k
      exact ht k.val
    · intro k
      cases he : k.val with
      | zero => simp only [he, hc.1]; rfl
      | succ n => simpa only [he] using (hc.2 n).2.1
  exact (ae_restrict_iff' (oneSplitPrefixSector_measurable N)).mpr hbase

end Rhone.Coalescent.SmcPrime
