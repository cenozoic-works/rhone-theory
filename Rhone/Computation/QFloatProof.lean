/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.QFloat
public import Rhone.Computation.Float64KernelProof

/-! # Meaning of acceptance of the q binary64 check -/

@[expose] public section
namespace Rhone.Computation.QFloat
open Float64Kernel

theorem accepted_nearest {r : Request} (ha : r.accepted = true) {leaf : Rat × Rat}
    (hmem : leaf ∈ r.leaves.toList) :
    ∃ y : Rat, decodeFinite (nearestWord leaf.1) = some y ∧
      (∀ (other : Nat) (z : Rat), decodeFinite other = some z →
        |y - leaf.1| ≤ |z - leaf.1| ∧ |y - leaf.2| ≤ |z - leaf.2|) ∧
      |y - leaf.1| / leaf.1 ≤ 1 / (2 : Rat) ^ 53 := by
  simp only [Request.accepted, Bool.and_eq_true, cellsAccepted, List.all_eq_true,
    List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at ha
  obtain ⟨hex, hdec⟩ := ha
  have h1 := hex leaf hmem
  have h2 := hdec leaf hmem
  obtain ⟨y, hy⟩ := guarded_decode h1
  exact ⟨y, hy, fun other z hz => ⟨guarded_nearest h1 hy hz, guarded_nearest h2 hy hz⟩,
    guarded_relative h1 hy⟩

end Rhone.Computation.QFloat
