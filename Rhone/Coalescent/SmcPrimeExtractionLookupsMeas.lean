/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitExtraction
public import Rhone.Coalescent.SmcPrimeProposalMeas
/-! # Measurability of lineage lookups and clades in the one-split extraction -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess MeasureTheory
instance : MeasurableSpace (Option ℕ) := ⊤

theorem rebuildSampleUID_measurable (N : ℕ) :
    Measurable (fun p : (Fin N → ℕ) × Finset (Fin N) => rebuildSampleUID p.1 p.2) :=
  measurable_of_countable _

theorem extractionClade_measurable (N : ℕ) :
    Measurable (fun p : (Fin N → ℕ) × ℕ => extractionClade p.1 p.2) :=
  measurable_of_countable _

theorem rebuildUIDIndex_measurable :
    Measurable (fun p : State × ℕ => rebuildUIDIndex p.1 p.2) := by
  let f (p : LiveState × ((ℝ × ℕ) × ℕ)) :=
    rebuildUIDIndex (p.2.1.1,p.2.1.2,p.1) p.2.2
  have hf : Measurable f := by
    apply measurable_prod_sigma_of_fibers
    intro m
    let g (p : (Fin m → ℕ) × ℕ) :=
      match (List.finRange m).find? (fun i => p.1 i = p.2) with
      | none => m
      | some i => i.val
    have hg : Measurable g := measurable_of_countable _
    have hu : Measurable (fun p : (Fin m → ℕ × Material) × ((ℝ × ℕ) × ℕ) =>
        (fun i : Fin m => (p.1 i).1)) :=
      measurable_pi_iff.mpr (fun i => ((measurable_pi_apply i).comp measurable_fst).fst)
    convert hg.comp (hu.prodMk measurable_snd.snd) using 1
    funext p
    simp only [f, g, rebuildUIDIndex, Function.comp_def]
    split <;> split <;> simp_all only [List.find?_eq_none, List.mem_finRange,
      decide_eq_true_eq, forall_const, reduceCtorEq, Option.some.injEq]
  exact hf.comp (measurable_fst.snd.snd.prodMk
    ((measurable_fst.fst.prodMk measurable_fst.snd.fst).prodMk measurable_snd))

theorem extractionCutIndex_measurable (N : ℕ) :
    Measurable (fun p : Tree N × (Finset (Fin N) × ℝ) =>
      extractionCutIndex p.1 p.2.1 p.2.2) := by
  classical
  apply measurable_prod_sigma_of_fibers
  intro m
  let g (p : Finset (Fin m) × (Fin m → Finset (Fin N)) × Finset (Fin N)) :=
    match (List.finRange m).find? (fun i => i ∈ p.1 ∧ p.2.1 i = p.2.2) with
    | none => m
    | some i => i.val
  have hg : Measurable g := measurable_of_countable _
  have hA : Measurable (fun p : (Fin m → Branch N) × (Finset (Fin N) × ℝ) =>
      (show Finset (Fin m) from activeBranches ⟨m,p.1⟩ p.2.2)) :=
    (activeBranchesFiber_measurable N m).comp (measurable_fst.prodMk measurable_snd.snd)
  have hC : Measurable (fun p : (Fin m → Branch N) × (Finset (Fin N) × ℝ) =>
      (fun i : Fin m => (p.1 i).1)) :=
    measurable_pi_iff.mpr (fun i => ((measurable_pi_apply i).comp measurable_fst).fst)
  convert hg.comp (hA.prodMk (hC.prodMk measurable_snd.fst)) using 1
  funext p
  simp only [g, extractionCutIndex, Function.comp_def]
  split <;> split <;> simp_all only [Bool.decide_and, List.find?_eq_none, List.mem_finRange,
    Bool.and_eq_true, decide_eq_true_eq, not_and, forall_const, not_false_eq_true,
    implies_true, reduceCtorEq, Option.some.injEq]
  rename_i i hnone hsome
  have hi := List.find?_some hsome
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hi
  exact False.elim (hnone i hi.1 hi.2)

theorem rebuildCoal_measurable (N : ℕ) :
    Measurable (fun p : RebuildState N × (ℝ × (ℕ × ℕ)) =>
      rebuildCoal p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let P := RebuildState N × (ℝ × (ℕ × ℕ))
  let i (p : P) := rebuildUIDIndex p.1.1.1 p.2.2.1
  let j (p : P) := rebuildUIDIndex p.1.1.1 p.2.2.2
  have hi : Measurable i := rebuildUIDIndex_measurable.comp
    (measurable_fst.fst.fst.prodMk measurable_snd.snd.fst)
  have hj : Measurable j := rebuildUIDIndex_measurable.comp
    (measurable_fst.fst.fst.prodMk measurable_snd.snd.snd)
  let ij (p : P) := (min (i p) (j p),max (i p) (j p))
  have hij : Measurable ij := (hi.min hj).prodMk (hi.max hj)
  let e (p : P) : Event := .inr (.inl (ij p))
  have he : Measurable e := measurable_inr.comp (measurable_inl.comp hij)
  have hc : Measurable (fun p : P => coalSuccessorNat p.1.1.1 (ij p)) :=
    coalSuccessorNat_measurable.comp (measurable_fst.fst.fst.prodMk hij)
  have hL : Measurable (fun p : P => fun k : Fin N =>
      ancestorStep p.1.1.1 (e p) leftBoundaryProbe (p.1.2.1 k)) := by
    apply measurable_pi_iff.mpr
    intro k
    exact (ancestorStep_measurable leftBoundaryProbe).comp
      (measurable_fst.fst.fst.prodMk
        (he.prodMk ((measurable_pi_apply k).comp measurable_fst.snd.fst)))
  have hR : Measurable (fun p : P => fun k : Fin N =>
      ancestorStep p.1.1.1 (e p) leftBoundaryProbe (p.1.2.2.1 k)) := by
    apply measurable_pi_iff.mpr
    intro k
    exact (ancestorStep_measurable leftBoundaryProbe).comp
      (measurable_fst.fst.fst.prodMk
        (he.prodMk ((measurable_pi_apply k).comp measurable_fst.snd.snd.fst)))
  exact ((measurable_snd.fst.prodMk hc.snd).prodMk (measurable_snd.fst.prodMk he)).prodMk
    (hL.prodMk (hR.prodMk measurable_fst.snd.snd.snd))
end Rhone.Coalescent.SmcPrime
