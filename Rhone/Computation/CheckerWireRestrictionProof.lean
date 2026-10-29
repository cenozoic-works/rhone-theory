/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.CheckerWireRequestProof
public import Rhone.Computation.CheckerCompletenessProof
public import Rhone.Computation.CheckerSoundnessProof

/-! # Complete exact q restrictions on the bounded checker wire -/

@[expose] public section
namespace Rhone.Computation.CheckerWire
open Lean

theorem closure_bounded {n : Nat} (hn : n ≤ 65535) {s : Config}
    (hs : s ∈ closure n) : BoundedConfig s := by
  have hm : s ∈ closureList n := by
    simpa only [closure, List.mem_toArray] using hs
  simp only [closureList, List.mem_flatMap, List.mem_range, List.mem_map] at hm
  rcases hm with ⟨c00, h00, c01, h01, c10, h10, c11, h11,
    a0, ha0, a1, ha1, b0, hb0, b1, hb1, rfl⟩
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro count hcount
  have hcases : count = a0 ∨ count = a1 ∨ count = b0 ∨ count = b1 ∨
      count = c00 ∨ count = c01 ∨ count = c10 ∨ count = c11 := by
    simpa [configOfCounts] using hcount
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

noncomputable def exactRestriction (p : Params) (hp : p.valid = true) (n : Nat) :
    Array (Config × Rat) :=
  (closure n).map fun s => (s,
    Rhone.LinearAlgebra.Recursion.q
      (πA := fun (i : Fin 2) => p.piA.getD i.val 0)
      (πB := fun (j : Fin 2) => p.piB.getD j.val 0)
      ((Params.valid_iff p).mp hp).1 ((Params.valid_iff p).mp hp).2.1
      ((Params.valid_iff p).mp hp).2.2.1 (CheckerEncoding.decode s))

theorem exactRestriction_accepted (p : Params) (hp : p.valid = true) (n : Nat) :
    checkTable p n (exactRestriction p hp n) = true :=
  checkTable_complete p hp n

theorem exactRestriction_bounded (p : Params) (hp : p.valid = true) (n : Nat)
    (hn : n ≤ 65535) :
    ∀ row ∈ exactRestriction p hp n, BoundedConfig row.1 := by
  intro row hr
  simp only [exactRestriction, Array.mem_map] at hr
  obtain ⟨s, hs, rfl⟩ := hr
  exact closure_bounded hn hs

theorem requestAst_exactRestriction (p : Params) (hp : p.valid = true) (n : Nat)
    (hn : n ≤ 65535) :
    requestAst (encodeRequest p n (exactRestriction p hp n)) = .ok
      (stamp [("accepted", toJson true), ("bound", toJson n),
        ("row_count", toJson (exactRestriction p hp n).size)]) := by
  rw [requestAst_encode p hp n hn _ (exactRestriction_bounded p hp n hn),
    exactRestriction_accepted]

end Rhone.Computation.CheckerWire
