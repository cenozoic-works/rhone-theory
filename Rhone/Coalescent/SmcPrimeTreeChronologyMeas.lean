/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeTreeEpochs
public import Rhone.Coalescent.SmcPrimeProposalMeas
public import Rhone.Coalescent.SmcSupport.MaterialMeasurable

/-!
# Measurability of tree chronology via finite endpoint epochs

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open MeasureTheory

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem timeCladesFiber_measurable (N m : ℕ) :
    Measurable (fun p : (Fin m → Branch N) × ℝ => timeClades ⟨m, p.1⟩ p.2) := by
  classical
  have hImage : Measurable (fun p : (Fin m → Branch N) × ℝ =>
      (activeBranches ⟨m, p.1⟩ p.2).image (fun i => (p.1 i).1)) := by
    apply measurable_finset_iff.mpr
    intro c
    apply measurableSet_setOfPred.mp
    have hex : MeasurableSet {p : (Fin m → Branch N) × ℝ |
        ∃ i : Fin m, i ∈ activeBranches ⟨m, p.1⟩ p.2 ∧ (p.1 i).1 = c} := by
      apply Rhone.Coalescent.SmcSupport.measurableSet_exists
      intro i
      have hmem : MeasurableSet {p : (Fin m → Branch N) × ℝ |
          i ∈ activeBranches ⟨m, p.1⟩ p.2} :=
        measurableSet_setOfPred.mpr
          ((measurable_finset_mem i).comp (activeBranchesFiber_measurable N m))
      have hi : Measurable (fun p : (Fin m → Branch N) × ℝ => (p.1 i).1) :=
        ((measurable_pi_apply i).comp measurable_fst).fst
      exact hmem.inter (measurableSet_eq_fun hi measurable_const)
    simpa only [Finset.mem_image] using hex
  have hroot : MeasurableSet {p : (Fin m → Branch N) × ℝ |
      rootHeight ⟨m, p.1⟩ ≤ p.2} :=
    measurableSet_le ((rootHeightFiber_measurable N m).comp measurable_fst) measurable_snd
  exact Measurable.ite hroot measurable_const hImage

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem TreeChronologyEpochs_measurable (N : ℕ) :
    MeasurableSet {T : Tree N | TreeChronologyEpochs T} := by
  classical
  apply Rhone.Coalescent.SmcSupport.measurableSet_sigma_of_fibers
  intro m
  let B := Fin m → Branch N
  have hepoch {δ : Type} [MeasurableSpace δ] (f : δ → B) (hf : Measurable f)
      (P : δ → ℝ → Prop) (hP : MeasurableSet {p : δ × ℝ | P p.1 p.2}) :
      MeasurableSet {x : δ | ∀ q ∈ treeEpochs ⟨m, f x⟩, P x q} := by
    have h0 : MeasurableSet {x : δ | P x 0} :=
      hP.preimage (measurable_id.prodMk measurable_const)
    have hr : MeasurableSet {x : δ | P x (rootHeight ⟨m, f x⟩)} :=
      hP.preimage (measurable_id.prodMk ((rootHeightFiber_measurable N m).comp hf))
    have hb : MeasurableSet {x : δ | ∀ i : Fin m,
        P x ((f x) i).2.1 ∧ P x ((f x) i).2.2} := by
      apply Rhone.Coalescent.SmcSupport.measurableSet_forall
      intro i
      have hi : Measurable (fun x : δ => (f x) i) := (measurable_pi_apply i).comp hf
      exact (hP.preimage (measurable_id.prodMk hi.snd.fst)).inter
        (hP.preimage (measurable_id.prodMk hi.snd.snd))
    convert h0.inter (hr.inter hb) using 1
    ext x
    simp only [treeEpochs, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, List.mem_flatMap, List.mem_finRange, true_and, Set.mem_inter_iff,
      Set.mem_ofPred_eq]
    constructor
    · intro h
      exact ⟨h 0 (Or.inl (Or.inl rfl)), h _ (Or.inl (Or.inr rfl)),
        fun i => ⟨h _ (Or.inr ⟨i, Or.inl rfl⟩), h _ (Or.inr ⟨i, Or.inr rfl⟩)⟩⟩
    · rintro ⟨h0, hr, hb⟩ q ((rfl | rfl) | ⟨i, rfl | rfl⟩)
      · exact h0
      · exact hr
      · exact (hb i).1
      · exact (hb i).2
  let Part (C : Finset (Finset (Fin N))) :=
    (∀ c ∈ C, c ≠ ∅) ∧ (∀ i : Fin N, ∃ c ∈ C, i ∈ c) ∧
      (∀ c ∈ C, ∀ d ∈ C, c ≠ d → Disjoint c d)
  let Refines (C D : Finset (Finset (Fin N))) := ∀ c ∈ C, ∃ d ∈ D, c ⊆ d
  have hPart : MeasurableSet {C : Finset (Finset (Fin N)) | Part C} :=
    Set.to_countable _ |>.measurableSet
  have hRef : MeasurableSet {p : Finset (Finset (Fin N)) × Finset (Finset (Fin N)) |
      Refines p.1 p.2} := Set.to_countable _ |>.measurableSet
  have hP : MeasurableSet {p : B × ℝ | 0 ≤ p.2 → Part (timeClades ⟨m, p.1⟩ p.2)} := by
    convert (measurableSet_le (measurable_const (a := (0 : ℝ))) measurable_snd).compl.union
      (hPart.preimage (timeCladesFiber_measurable N m)) using 1
    ext p
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_preimage,
      imp_iff_not_or]
    rfl
  have hparts := hepoch (δ := B) id measurable_id
    (fun f q => 0 ≤ q → Part (timeClades ⟨m, f⟩ q)) hP
  have hQ : MeasurableSet {p : (B × ℝ) × ℝ |
      0 ≤ p.1.2 → p.1.2 ≤ p.2 → Refines
        (timeClades ⟨m, p.1.1⟩ p.1.2) (timeClades ⟨m, p.1.1⟩ p.2)} := by
    have hleft : Measurable (fun p : (B × ℝ) × ℝ =>
        timeClades ⟨m, p.1.1⟩ p.1.2) :=
      (timeCladesFiber_measurable N m).comp measurable_fst
    have hright : Measurable (fun p : (B × ℝ) × ℝ =>
        timeClades ⟨m, p.1.1⟩ p.2) := (timeCladesFiber_measurable N m).comp
      (measurable_fst.fst.prodMk measurable_snd)
    convert ((measurableSet_le (measurable_const (a := (0 : ℝ))) measurable_fst.snd).inter
      (measurableSet_le measurable_fst.snd measurable_snd)).compl.union
      (hRef.preimage (hleft.prodMk hright)) using 1
    ext p
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_ofPred_eq,
      imp_iff_not_or, not_and_or]
    tauto
  have hrefsInner := hepoch (δ := B × ℝ) Prod.fst measurable_fst
    (fun p r => 0 ≤ p.2 → p.2 ≤ r → Refines
      (timeClades ⟨m, p.1⟩ p.2) (timeClades ⟨m, p.1⟩ r)) hQ
  have hrefs := hepoch (δ := B) id measurable_id
    (fun f q => ∀ r ∈ treeEpochs ⟨m, f⟩, 0 ≤ q → q ≤ r → Refines
      (timeClades ⟨m, f⟩ q) (timeClades ⟨m, f⟩ r)) hrefsInner
  exact hparts.inter hrefs

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem TreeChronology_measurable (N : ℕ) :
    MeasurableSet {T : Tree N | TreeChronology T} := by
  convert TreeChronologyEpochs_measurable N using 1
  ext T
  exact tree_chronology_iff_epochs T

end Rhone.Coalescent.SmcPrime
