/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.Float64Artifact
public import Rhone.Computation.Float64KernelProof
public import Rhone.Computation.GenericArtifactProof

/-! # Meaning of acceptance of the float64 table artifact reader -/

@[expose] public section
namespace Rhone.Computation.Float64Artifact
open Lean GenericArtifact Float64Kernel
open TableArtifact (fieldsAllowed strictField strictRational strictArray tableFields
  baselineModel readRow)

@[simp] private theorem ok_bind {α β : Type} (x : α) (f : α → Except String β) :
    ((Except.ok x : Except String α) >>= f) = f x := rfl

private theorem of_bind_ok {α β : Type} {x : Except String α} {f : α → Except String β}
    {b : β} {P : Prop} (h : x >>= f = .ok b)
    (step : ∀ a, x = .ok a → f a = .ok b → P) : P := by
  cases x with
  | error e => cases h
  | ok a => exact step a rfl h

theorem decode_header {doc : Json} {r : Request} (hd : decode doc = .ok r) :
    ∃ table : Json,
      decodeHeaderAs "rhone-table-float64-v3" floatFields table = .ok r.header := by
  unfold decode at hd
  refine of_bind_ok hd fun _ _ hd => ?_
  refine of_bind_ok hd fun _ _ hd => ?_
  split at hd
  · cases hd
  refine of_bind_ok hd fun table _ hd => ?_
  refine of_bind_ok hd fun header hh hd => ?_
  refine of_bind_ok hd fun _ _ hd => ?_
  refine of_bind_ok hd fun _ _ hd => ?_
  refine of_bind_ok hd fun _ _ hd => ?_
  cases hd
  exact ⟨table, hh⟩

theorem leaf_mem {r : Request} {g c : Nat} (hg : g < r.leaves.size)
    (hc : c < (r.leaves.getD g #[]).size) :
    (r.leaves.getD g #[]).getD c (0, 0) ∈ r.allLeaves := by
  unfold Request.allLeaves
  have hrow : r.leaves.getD g #[] = r.leaves[g] := by simp [Array.getD, hg]
  rw [hrow] at hc ⊢
  refine List.mem_flatMap.mpr ⟨r.leaves[g], by simp, ?_⟩
  simp [Array.getD, hc]

theorem artifact_value (r : Request) (g c : Nat) :
    (r.artifact.values.getD g #[]).getD c 0 = ((r.leaves.getD g #[]).getD c (0, 0)).1 := by
  simp only [Request.artifact, Array.getD]
  by_cases hg : g < r.leaves.size
  · by_cases hc : c < (r.leaves[g]).size
    · simp [hg, hc]
    · simp [hg, hc]
  · simp [hg]

theorem decode_accepted_leaf {doc : Json} {r : Request} (hd : decode doc = .ok r)
    (ha : r.accepted = true) {g c : Nat} (hg : g < r.header.grid.size)
    (hc : c < r.header.keys.size) :
    let leaf := (r.leaves.getD g #[]).getD c (0, 0)
    (∃ config : Config,
      parseConfig (r.header.keys.getD c "") r.header.piA.size r.header.piB.size = .ok config ∧
      (leaf.1 : Real) = Rhone.Coalescent.TwoLocusGenealogy.qProb
        (r.header.thetaA : Real) (r.header.thetaB : Real) (r.header.grid.getD g 0 : Real)
        (fun i => (GenericWire.pi r.header.piA i : Real))
        (fun j => (GenericWire.pi r.header.piB j : Real))
        (GenericWire.toSpec r.header.piA.size r.header.piB.size config)) ∧
    ∃ y : Rat, decodeFinite (nearestWord leaf.1) = some y ∧
      (∀ (other : Nat) (z : Rat), decodeFinite other = some z →
        |y - leaf.1| ≤ |z - leaf.1| ∧ |y - leaf.2| ≤ |z - leaf.2|) ∧
      |y - leaf.1| / leaf.1 ≤ 1 / (2 : Rat) ^ 53 := by
  intro leaf
  simp only [Request.accepted, Bool.and_eq_true, beq_iff_eq] at ha
  obtain ⟨⟨⟨⟨hart, hex⟩, hdec⟩, _⟩, _⟩ := ha
  obtain ⟨table, hh⟩ := decode_header hd
  have hprob := header_accepted_probability (r := r.artifact) hh hart hg hc
  rw [artifact_value] at hprob
  refine ⟨hprob, ?_⟩
  have hart' := hart
  simp only [GenericArtifact.Request.accepted, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.mem_range] at hart'
  obtain ⟨⟨hvs, _⟩, hrows⟩ := hart'
  have hrow := hrows g hg
  simp only [rowAccepted, Bool.and_eq_true, beq_iff_eq] at hrow
  obtain ⟨⟨hsize, _⟩, _⟩ := hrow
  have hg' : g < r.leaves.size := by
    have hvs' : r.leaves.size = r.header.grid.size := by
      simpa [Request.artifact] using hvs
    omega
  have hc' : c < (r.leaves.getD g #[]).size := by
    have : (r.artifact.values.getD g #[]).size = (r.leaves.getD g #[]).size := by
      simp [Request.artifact, Array.getD, hg']
    have hsize' : (r.artifact.values.getD g #[]).size = r.header.keys.size := hsize
    omega
  have hmem := leaf_mem hg' hc'
  simp only [cellsAccepted, List.all_eq_true, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂] at hex hdec
  have h1 := hex leaf hmem
  have h2 := hdec leaf hmem
  obtain ⟨y, hy⟩ := guarded_decode h1
  refine ⟨y, hy, fun other z hz => ⟨guarded_nearest h1 hy hz, guarded_nearest h2 hy hz⟩,
    guarded_relative h1 hy⟩

theorem accepted_export {r : Request} (ha : r.accepted = true) :
    r.count = r.allLeaves.length ∧
      r.maxError = TableFloatError.maxRelativeError
        ((r.allLeaves.map exactCell).map Cell.toSpec) ∧
      r.maxError ≤ 1 / (2 : Rat) ^ 53 := by
  simp only [Request.accepted, Bool.and_eq_true, beq_iff_eq] at ha
  obtain ⟨⟨⟨⟨_, hex⟩, _⟩, hcount⟩, hmax⟩ := ha
  rw [maxRelativeError_eq] at hmax
  rw [cellsAccepted_eq] at hex
  exact ⟨hcount, hmax, hmax ▸ TableFloatError.maxRelativeError_bound hex⟩

end Rhone.Computation.Float64Artifact
