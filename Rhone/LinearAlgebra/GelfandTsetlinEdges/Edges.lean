/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.GelfandTsetlinEdges.EdgeData

/-! # The 253 tabulated edges satisfy the `β`-number sector law -/

@[expose] public section

namespace Rhone.LinearAlgebra.GelfandTsetlinEdges

set_option maxRecDepth 8000

theorem edges_length : edges.length = 253 := by decide

theorem edges_open58_length : (edges.filter fun e => e.open58).length = 58 := by decide

theorem edge_certificate : edges.all edgeOK = true := by decide

theorem edgeOK_of_mem {e : Edge} (he : e ∈ edges) : edgeOK e = true :=
  List.all_eq_true.mp edge_certificate e he

theorem edgeOKat_of_mem {e : Edge} (he : e ∈ edges) {d : ℕ} (hd : d < 3) :
    edgeOKat e (e.R + d) = true := by
  have h := edgeOK_of_mem he
  rw [edgeOK] at h
  exact List.all_eq_true.mp h d (List.mem_range.mpr hd)

theorem edge_law {e : Edge} (he : e ∈ edges) {d : ℕ} (hd : d < 3) :
    lawAt e (e.R + d) = measured e := by
  have h := edgeOKat_of_mem he hd
  rw [edgeOKat] at h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨⟨hD, hpd⟩, heq⟩ := h
  rw [lawAt, measured, div_eq_div_iff (Int.cast_ne_zero.mpr hD) (Nat.cast_ne_zero.mpr hpd)]
  exact_mod_cast heq.symm

end Rhone.LinearAlgebra.GelfandTsetlinEdges
