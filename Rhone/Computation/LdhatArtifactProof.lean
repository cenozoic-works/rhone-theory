/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.LdhatArtifact
public import Rhone.Computation.LogKernelProof
public import Rhone.Computation.GenericArtifactProof

/-! # Meaning of acceptance of the LDhat bound reader -/

@[expose] public section
namespace Rhone.Computation.LdhatArtifact
open Lean GenericArtifact
open TableArtifact (fieldsAllowed strictField strictRational strictArray tableFields
  baselineModel readRow)

theorem configIndex_spec {h : Header} {x : Config} {c : Nat} (hc : configIndex h x = some c) :
    c < h.configs.size ∧ h.configs.getD c default = x := by
  unfold configIndex at hc
  have hmem := List.mem_of_find?_eq_some hc
  have hp := List.find?_some hc
  simp only [beq_iff_eq] at hp
  exact ⟨List.mem_range.mp hmem, GenericKernel.keyOf_inj hp⟩

theorem accepted_bound {r : Request} (ha : r.accepted = true) :
    r.artifact.header.thetaA = r.artifact.header.thetaB ∧
      r.artifact.header.piA = #[1 / 2, 1 / 2] ∧ r.artifact.header.piB = #[1 / 2, 1 / 2] ∧
      ∀ i g, i < r.lk.rows.size → g < r.artifact.header.grid.size →
        |(((r.lk.rows.getD i default).values.getD g 0 : Rat) : Real) -
          Real.log (Rhone.Coalescent.TwoLocusGenealogy.qProb
            (r.artifact.header.thetaA : Real) (r.artifact.header.thetaB : Real)
            (r.artifact.header.grid.getD g 0 : Real)
            (fun i => (GenericWire.pi r.artifact.header.piA i : Real))
            (fun j => (GenericWire.pi r.artifact.header.piB j : Real))
            (GenericWire.toSpec r.artifact.header.piA.size r.artifact.header.piB.size
              (r.lk.rows.getD i default).config))| ≤ (budget : Real) := by
  simp only [LdhatArtifact.Request.accepted, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.all_eq_true, List.mem_range] at ha
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hart, hth⟩, hpa⟩, hpb⟩, _⟩, _⟩, _⟩, _⟩, _⟩, hrows⟩ := ha
  refine ⟨hth, hpa, hpb, fun i g hi hg => ?_⟩
  have hrow := hrows i hi
  unfold rowAccepted at hrow
  simp only [Bool.and_eq_true, beq_iff_eq] at hrow
  obtain ⟨⟨_, _⟩, hmatch⟩ := hrow
  split at hmatch
  · cases hmatch
  rename_i c hc
  obtain ⟨hcs, hconf⟩ := configIndex_spec hc
  simp only [List.all_eq_true, List.mem_range] at hmatch
  have hb := LogKernel.bracketCheck_sound (hmatch g hg)
  have hp := GenericArtifact.Request.accepted_probability hart hg hcs
  rw [hconf] at hp
  rw [← hp]
  rw [abs_sub_comm] at hb
  rw [abs_sub_comm]
  exact hb

end Rhone.Computation.LdhatArtifact
