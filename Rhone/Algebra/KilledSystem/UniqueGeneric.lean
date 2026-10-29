/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.KilledSystem.UniqueLower
public import Rhone.Algebra.KilledSystem.UniqueUpper

/-! # Field-generic uniqueness of the killed-PIM system from the elimination pieces -/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Rhone.Algebra.KilledSystem

theorem unique_aux_generic {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St → F)
    (ne_lhs02 : (2 + 2 * thB : F) ≠ 0)
    (ne_lhs20 : (2 + 2 * thA : F) ≠ 0)
    (ne_lhs11 : (2 + thA + thB : F) ≠ 0)
    (ne_d1_12 : (2 + thA + 2 * thB + rhoL : F) ≠ 0)
    (ne_d1_21 : (2 + 2 * thA + thB + rhoL : F) ≠ 0)
    (ne_E12 : ((6 + thA + 2 * thB) * (2 + thA + 2 * thB + rhoL) - 4 * rhoL : F) ≠ 0)
    (ne_E21 : ((6 + 2 * thA + thB) * (2 + 2 * thA + thB + rhoL) - 4 * rhoL : F) ≠ 0)
    (ne_d2_22 : (2 + 2 * thA + 2 * thB + 2 * rhoL : F) ≠ 0)
    (ne_W22 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) : F) ≠ 0)
    (ne_W4_22 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL : F)
      ≠ 0)
    (ne_D22 : ((12 + 2 * thA + 2 * thB) * ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB +
      2 * rhoL) - 4 * rhoL) - 8 * rhoL * (2 + 2 * thA + 2 * thB + 2 * rhoL) : F) ≠ 0)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s) (hbd : ∀ s ∈ bdryStates, Δ s = 0) : ∀ s ∈ closureList, Δ s = 0 :=
      by
  have lower := unique_lower_blocks thA thB rhoL piA0 piA1 piB0 piB1 Δ ne_lhs02 ne_lhs20 ne_lhs11
    ne_E12 ne_d1_12 ne_E21 ne_d1_21 hrec hbd
  rcases lower with ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17,
    z18, z19, z20, z21, z22, z23, z24, z25, z26, z27, z28, z29, z30, z31, z32, z33, z34, z35, z36,
    z37, z38, z39, z40, z41, z42, z43, z44, z45⟩
  have upper := unique_upper_blocks thA thB rhoL piA0 piA1 piB0 piB1 Δ ne_d2_22 ne_W22 ne_W4_22
    ne_D22 hrec z7 z8 z9 z10 z18 z19 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31 z32 z33 z34 z35
    z36 z37 z38 z39 z40 z41 z42 z43 z44 z45
  rcases upper with ⟨z46, z47, z48, z49, z50, z51, z52, z53, z54, z55, z56, z57, z58, z59, z60, z61,
    z62, z63, z64, z65, z66, z67, z68, z69, z70, z71, z72, z73, z74, z75, z76, z77, z78, z79, z80⟩
  intro s hs
  simp only [closureList, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl
  exacts [z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18,
    z19, z20, z21, z22, z23, z24, z25, z26, z27, z28, z29, z30, z31, z32, z33, z34, z35, z36, z37,
    z38, z39, z40, z41, z42, z43, z44, z45, z46, z47, z48, z49, z50, z51, z52, z53, z54, z55, z56,
    z57, z58, z59, z60, z61, z62, z63, z64, z65, z66, z67, z68, z69, z70, z71, z72, z73, z74, z75,
    z76, z77, z78, z79, z80]

end Rhone.Algebra.KilledSystem
