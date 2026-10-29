/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib
/-! # Exact LDhat scientific headers and grid -/

@[expose] public section
namespace Rhone.Computation.LdhatHeaders

def fourDecimal (k : Int) : Rat := (k : Rat) / 10000

def exactHeader (x : Rat) : Option Int :=
  let k := Int.floor (x * 10000)
  if fourDecimal k = x then some k else none

lemma exactHeader_some {x : Rat} {k : Int} (h : exactHeader x = some k) :
    fourDecimal k = x := by
  dsimp only [exactHeader] at h
  split_ifs at h with he
  · exact (Option.some.inj h) ▸ he

lemma exactHeader_complete (k : Int) : exactHeader (fourDecimal k) = some k := by
  have hm : fourDecimal k * 10000 = (k : Rat) := by unfold fourDecimal; ring
  simp [exactHeader, hm]

lemma exactHeader_none_iff (x : Rat) : exactHeader x = none ↔ ∀ k : Int, fourDecimal k ≠ x := by
  constructor
  · intro h k he
    rw [← he, exactHeader_complete] at h
    contradiction
  · intro h
    dsimp only [exactHeader]
    simp [h]

def grid (rhoMax : Rat) (nPts : Nat) : Array Rat :=
  (Array.range nPts).map (fun (i : Nat) => (i : Rat) * rhoMax / (nPts - 1 : Nat))

def accepted (thetaPim rhoMax : Rat) (thetaIndex rhoIndex : Int)
    (nPts : Nat) (originalGrid : Array Rat) : Bool :=
  decide (0 < thetaPim ∧ 0 ≤ rhoMax ∧ 2 ≤ nPts ∧
    thetaPim = 2 * fourDecimal thetaIndex ∧ rhoMax = fourDecimal rhoIndex ∧
    originalGrid = grid rhoMax nPts)

lemma accepted_parameters {thetaPim rhoMax : Rat} {thetaIndex rhoIndex : Int}
    {nPts : Nat} {originalGrid : Array Rat}
    (h : accepted thetaPim rhoMax thetaIndex rhoIndex nPts originalGrid = true) :
    thetaPim = 2 * fourDecimal thetaIndex ∧ rhoMax = fourDecimal rhoIndex ∧
      originalGrid = grid (fourDecimal rhoIndex) nPts := by
  simp only [accepted, decide_eq_true_eq] at h
  exact ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.1 ▸ h.2.2.2.2.2⟩

lemma accepted_grid_size {thetaPim rhoMax : Rat} {thetaIndex rhoIndex : Int}
    {nPts : Nat} {originalGrid : Array Rat}
    (h : accepted thetaPim rhoMax thetaIndex rhoIndex nPts originalGrid = true) :
    originalGrid.size = nPts := by
  rw [(accepted_parameters h).2.2]
  simp [grid]

lemma grid_at (rhoMax : Rat) (nPts : Nat) (i : Fin nPts) :
    (grid rhoMax nPts)[i.val]'(by simp [grid]) =
      (i.val : Rat) * rhoMax / (nPts - 1 : Nat) := by
  simp [grid]

end Rhone.Computation.LdhatHeaders
