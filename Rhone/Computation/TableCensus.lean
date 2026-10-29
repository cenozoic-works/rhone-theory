/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Algebra.Order.Field.Rat
public import Rhone.Computation.GenericRows
/-! # Fully typed finite-alphabet table census -/

@[expose] public section
namespace Rhone.Computation.TableCensus
open LinearAlgebra.Recursion

def census (KA KB n : Nat) : List (Config KA KB) :=
  (GenericRows.keys KA KB n).filter (fun ξ => decide (ξ.a = 0 ∧ ξ.b = 0 ∧ ξ.n = n))

lemma mem_census_iff {KA KB n : Nat} (ξ : Config KA KB) :
    ξ ∈ census KA KB n ↔ ξ.a = 0 ∧ ξ.b = 0 ∧ ξ.n = n := by
  simp only [census, List.mem_filter, decide_eq_true_eq, GenericRows.mem_keys_iff]
  constructor
  · exact And.right
  · intro h
    refine ⟨?_, h⟩
    exact ⟨h.2.2 ▸ ξ.nA_le_n, h.2.2 ▸ ξ.nB_le_n⟩

lemma nodup_census (KA KB n : Nat) : (census KA KB n).Nodup := by
  exact List.Nodup.filter _ (List.nodup_dedup _)

end Rhone.Computation.TableCensus
