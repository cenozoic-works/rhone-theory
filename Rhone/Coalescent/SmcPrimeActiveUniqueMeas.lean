/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeActiveUnique
public import Rhone.Coalescent.SmcPrimeTreeChronologyMeas

/-! # Borel measurability of active branch-index uniqueness in finite metric trees -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open MeasureTheory

theorem TreeActiveUnique_measurable (N : ℕ) :
    MeasurableSet {T : Tree N | TreeActiveUnique T} := by
  classical
  apply Rhone.Coalescent.SmcSupport.measurableSet_sigma_of_fibers
  intro m
  let B := Fin m → Branch N
  let P := fun f : B => fun q : ℝ => 0 ≤ q →
    ∀ i ∈ activeBranches ⟨m, f⟩ q, ∀ j ∈ activeBranches ⟨m, f⟩ q,
      (f i).1 = (f j).1 → i = j
  have hU : MeasurableSet {p : (Fin m → Finset (Fin N)) × Finset (Fin m) |
      ∀ i ∈ p.2, ∀ j ∈ p.2, p.1 i = p.1 j → i = j} :=
    Set.to_countable _ |>.measurableSet
  have hf : Measurable (fun p : B × ℝ => fun i => (p.1 i).1) := by
    apply measurable_pi_iff.mpr
    intro i
    exact ((measurable_pi_apply i).comp measurable_fst).fst
  have hP : MeasurableSet {p : B × ℝ | P p.1 p.2} := by
    convert (measurableSet_le (measurable_const (a := (0 : ℝ))) measurable_snd).compl.union
      (hU.preimage (hf.prodMk (activeBranchesFiber_measurable N m))) using 1
    ext p
    simp only [P, Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_preimage,
      imp_iff_not_or]
  have h0 : MeasurableSet {f : B | P f 0} :=
    hP.preimage (measurable_id.prodMk measurable_const)
  have hr : MeasurableSet {f : B | P f (rootHeight ⟨m, f⟩)} :=
    hP.preimage (measurable_id.prodMk (rootHeightFiber_measurable N m))
  have hb : MeasurableSet {f : B | ∀ i : Fin m,
      P f ((f i).2.1) ∧ P f ((f i).2.2)} := by
    apply Rhone.Coalescent.SmcSupport.measurableSet_forall
    intro i
    have hi : Measurable (fun f : B => f i) := measurable_pi_apply i
    exact (hP.preimage (measurable_id.prodMk hi.snd.fst)).inter
      (hP.preimage (measurable_id.prodMk hi.snd.snd))
  convert h0.inter (hr.inter hb) using 1
  ext f
  rw [Set.mem_ofPred_eq, tree_active_unique_iff_epochs]
  change (∀ q ∈ treeEpochs ⟨m, f⟩, P f q) ↔ _
  simp only [treeEpochs, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_flatMap, List.mem_finRange, true_and, Set.mem_inter_iff]
  constructor
  · intro h
    exact ⟨h 0 (Or.inl (Or.inl rfl)), h _ (Or.inl (Or.inr rfl)),
      fun i => ⟨h _ (Or.inr ⟨i, Or.inl rfl⟩), h _ (Or.inr ⟨i, Or.inr rfl⟩)⟩⟩
  · rintro ⟨h0, hr, hb⟩ q ((rfl | rfl) | ⟨i, rfl | rfl⟩)
    · exact h0
    · exact hr
    · exact (hb i).1
    · exact (hb i).2

end Rhone.Coalescent.SmcPrime
