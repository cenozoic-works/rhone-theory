/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.KilledSystem.UniqueEliminationTwoLineages
public import Rhone.Algebra.KilledSystem.UniqueEliminationOneATwoB
public import Rhone.Algebra.KilledSystem.UniqueEliminationTwoAOneB
public import Rhone.Algebra.KilledSystem.UniqueEliminationTwoLinkedLineages
public import Rhone.Algebra.KilledSystem.UniqueEliminationTwoUnlinkedOneLinked
public import Rhone.Algebra.KilledSystem.UniqueEliminationLinkedCombinations
public import Rhone.Algebra.KilledSystem.UniqueEliminationFourUnlinkedTypeOneA
public import Rhone.Algebra.KilledSystem.UniqueEliminationFourUnlinkedTypeZeroA
public import Rhone.Algebra.KilledSystem.UniqueEliminationTwoLinkedSameType

/-! # Exact upper-block assembly from separately checked elimination pieces -/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Rhone.Algebra.KilledSystem

theorem unique_upper_blocks {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St →
    F)
    (ne_d2_22 : (2 + 2 * thA + 2 * thB + 2 * rhoL : F) ≠ 0)
    (ne_W22 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) : F) ≠ 0)
    (ne_W4_22 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL : F)
      ≠ 0)
    (ne_D22 : ((12 + 2 * thA + 2 * thB) * ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB +
      2 * rhoL) - 4 * rhoL) - 8 * rhoL * (2 + 2 * thA + 2 * thB + 2 * rhoL) : F) ≠ 0)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (z7 : Δ ⟨0, 0, 0, 0, 0, 0, 0, 1⟩ = 0)
    (z8 : Δ ⟨0, 0, 0, 0, 0, 0, 1, 0⟩ = 0)
    (z9 : Δ ⟨0, 0, 0, 0, 0, 1, 0, 0⟩ = 0)
    (z10 : Δ ⟨0, 0, 0, 0, 1, 0, 0, 0⟩ = 0)
    (z18 : Δ ⟨0, 0, 0, 1, 0, 0, 0, 1⟩ = 0)
    (z19 : Δ ⟨0, 0, 0, 1, 0, 0, 1, 0⟩ = 0)
    (z20 : Δ ⟨0, 0, 0, 1, 0, 1, 0, 0⟩ = 0)
    (z21 : Δ ⟨0, 0, 0, 1, 1, 0, 0, 0⟩ = 0)
    (z22 : Δ ⟨0, 0, 1, 0, 0, 0, 0, 1⟩ = 0)
    (z23 : Δ ⟨0, 0, 1, 0, 0, 0, 1, 0⟩ = 0)
    (z24 : Δ ⟨0, 0, 1, 0, 0, 1, 0, 0⟩ = 0)
    (z25 : Δ ⟨0, 0, 1, 0, 1, 0, 0, 0⟩ = 0)
    (z26 : Δ ⟨0, 1, 0, 2, 0, 0, 0, 0⟩ = 0)
    (z27 : Δ ⟨0, 1, 1, 1, 0, 0, 0, 0⟩ = 0)
    (z28 : Δ ⟨0, 1, 2, 0, 0, 0, 0, 0⟩ = 0)
    (z29 : Δ ⟨1, 0, 0, 2, 0, 0, 0, 0⟩ = 0)
    (z30 : Δ ⟨1, 0, 1, 1, 0, 0, 0, 0⟩ = 0)
    (z31 : Δ ⟨1, 0, 2, 0, 0, 0, 0, 0⟩ = 0)
    (z32 : Δ ⟨0, 1, 0, 0, 0, 0, 0, 1⟩ = 0)
    (z33 : Δ ⟨0, 1, 0, 0, 0, 0, 1, 0⟩ = 0)
    (z34 : Δ ⟨0, 1, 0, 0, 0, 1, 0, 0⟩ = 0)
    (z35 : Δ ⟨0, 1, 0, 0, 1, 0, 0, 0⟩ = 0)
    (z36 : Δ ⟨0, 2, 0, 1, 0, 0, 0, 0⟩ = 0)
    (z37 : Δ ⟨0, 2, 1, 0, 0, 0, 0, 0⟩ = 0)
    (z38 : Δ ⟨1, 0, 0, 0, 0, 0, 0, 1⟩ = 0)
    (z39 : Δ ⟨1, 0, 0, 0, 0, 0, 1, 0⟩ = 0)
    (z40 : Δ ⟨1, 0, 0, 0, 0, 1, 0, 0⟩ = 0)
    (z41 : Δ ⟨1, 0, 0, 0, 1, 0, 0, 0⟩ = 0)
    (z42 : Δ ⟨1, 1, 0, 1, 0, 0, 0, 0⟩ = 0)
    (z43 : Δ ⟨1, 1, 1, 0, 0, 0, 0, 0⟩ = 0)
    (z44 : Δ ⟨2, 0, 0, 1, 0, 0, 0, 0⟩ = 0)
    (z45 : Δ ⟨2, 0, 1, 0, 0, 0, 0, 0⟩ = 0)
    : Δ ⟨0, 0, 0, 0, 0, 0, 0, 2⟩ = 0 ∧ Δ ⟨0, 0, 0, 0, 0, 0, 1, 1⟩ = 0 ∧ Δ ⟨0, 0, 0, 0, 0, 0, 2, 0⟩ =
      0 ∧ Δ ⟨0, 0, 0, 0, 0, 1, 0, 1⟩ = 0 ∧ Δ ⟨0, 0, 0, 0, 0, 1, 1, 0⟩ = 0 ∧ Δ ⟨0, 0, 0, 0, 0, 2, 0,
      0⟩ = 0 ∧ Δ ⟨0, 0, 0, 0, 1, 0, 0, 1⟩ = 0 ∧ Δ ⟨0, 0, 0, 0, 1, 0, 1, 0⟩ = 0 ∧ Δ ⟨0, 0, 0, 0, 1,
      1, 0, 0⟩ = 0 ∧ Δ ⟨0, 0, 0, 0, 2, 0, 0, 0⟩ = 0 ∧ Δ ⟨0, 1, 0, 1, 0, 0, 0, 1⟩ = 0 ∧ Δ ⟨0, 1, 0,
      1, 0, 0, 1, 0⟩ = 0 ∧ Δ ⟨0, 1, 0, 1, 0, 1, 0, 0⟩ = 0 ∧ Δ ⟨0, 1, 0, 1, 1, 0, 0, 0⟩ = 0 ∧ Δ ⟨0,
      1, 1, 0, 0, 0, 0, 1⟩ = 0 ∧ Δ ⟨0, 1, 1, 0, 0, 0, 1, 0⟩ = 0 ∧ Δ ⟨0, 1, 1, 0, 0, 1, 0, 0⟩ = 0 ∧ Δ
      ⟨0, 1, 1, 0, 1, 0, 0, 0⟩ = 0 ∧ Δ ⟨0, 2, 0, 2, 0, 0, 0, 0⟩ = 0 ∧ Δ ⟨0, 2, 1, 1, 0, 0, 0, 0⟩ = 0
      ∧ Δ ⟨0, 2, 2, 0, 0, 0, 0, 0⟩ = 0 ∧ Δ ⟨1, 0, 0, 1, 0, 0, 0, 1⟩ = 0 ∧ Δ ⟨1, 0, 0, 1, 0, 0, 1, 0⟩
      = 0 ∧ Δ ⟨1, 0, 0, 1, 0, 1, 0, 0⟩ = 0 ∧ Δ ⟨1, 0, 0, 1, 1, 0, 0, 0⟩ = 0 ∧ Δ ⟨1, 0, 1, 0, 0, 0,
      0, 1⟩ = 0 ∧ Δ ⟨1, 0, 1, 0, 0, 0, 1, 0⟩ = 0 ∧ Δ ⟨1, 0, 1, 0, 0, 1, 0, 0⟩ = 0 ∧ Δ ⟨1, 0, 1, 0,
      1, 0, 0, 0⟩ = 0 ∧ Δ ⟨1, 1, 0, 2, 0, 0, 0, 0⟩ = 0 ∧ Δ ⟨1, 1, 1, 1, 0, 0, 0, 0⟩ = 0 ∧ Δ ⟨1, 1,
      2, 0, 0, 0, 0, 0⟩ = 0 ∧ Δ ⟨2, 0, 0, 2, 0, 0, 0, 0⟩ = 0 ∧ Δ ⟨2, 0, 1, 1, 0, 0, 0, 0⟩ = 0 ∧ Δ
      ⟨2, 0, 2, 0, 0, 0, 0, 0⟩ = 0 := by
  have h56 := unique_piece_h56 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z26 z18 z36 z32
  have h46 := unique_piece_h46 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z7 z18 z32
  have st56 := unique_piece_st56 thA thB rhoL Δ h56 h46
  have h57 := unique_piece_h57 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z27 z19 z36 z33
  have h47 := unique_piece_h47 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z19 z22 z32 z33
  have st57 := unique_piece_st57 thA thB rhoL Δ h57 h47
  have h58 := unique_piece_h58 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z26 z20 z42 z34
  have h49 := unique_piece_h49 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z18 z20 z34 z38
  have st58 := unique_piece_st58 thA thB rhoL Δ h58 h49
  have h59 := unique_piece_h59 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z27 z21 z42 z35
  have h52 := unique_piece_h52 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z21 z22 z35 z38
  have st59 := unique_piece_st59 thA thB rhoL Δ h59 h52
  have h60 := unique_piece_h60 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z27 z22 z37 z32
  have st60 := unique_piece_st60 thA thB rhoL Δ h47 h60
  have h61 := unique_piece_h61 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z28 z23 z37 z33
  have h48 := unique_piece_h48 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z8 z23 z33
  have st61 := unique_piece_st61 thA thB rhoL Δ h61 h48
  have h62 := unique_piece_h62 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z27 z24 z43 z34
  have h50 := unique_piece_h50 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z19 z24 z34 z39
  have st62 := unique_piece_st62 thA thB rhoL Δ h62 h50
  have h63 := unique_piece_h63 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z28 z25 z43 z35
  have h53 := unique_piece_h53 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z23 z25 z35 z39
  have st63 := unique_piece_st63 thA thB rhoL Δ h63 h53
  have h67 := unique_piece_h67 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z29 z18 z42 z38
  have st67 := unique_piece_st67 thA thB rhoL Δ h49 h67
  have h68 := unique_piece_h68 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z30 z19 z42 z39
  have st68 := unique_piece_st68 thA thB rhoL Δ h50 h68
  have h69 := unique_piece_h69 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z29 z20 z44 z40
  have h51 := unique_piece_h51 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z9 z20 z40
  have st69 := unique_piece_st69 thA thB rhoL Δ h69 h51
  have h70 := unique_piece_h70 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z30 z21 z44 z41
  have h54 := unique_piece_h54 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z21 z24 z40 z41
  have st70 := unique_piece_st70 thA thB rhoL Δ h70 h54
  have h71 := unique_piece_h71 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z30 z22 z43 z38
  have st71 := unique_piece_st71 thA thB rhoL Δ h52 h71
  have h72 := unique_piece_h72 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z31 z23 z43 z39
  have st72 := unique_piece_st72 thA thB rhoL Δ h53 h72
  have h73 := unique_piece_h73 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z30 z24 z45 z40
  have st73 := unique_piece_st73 thA thB rhoL Δ h54 h73
  have h74 := unique_piece_h74 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z31 z25 z45 z41
  have h55 := unique_piece_h55 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z10 z25 z41
  have st74 := unique_piece_st74 thA thB rhoL Δ h74 h55
  have s256 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ
    ⟨0, 1, 0, 1, 0, 0, 0, 1⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨0, 2, 0, 2, 0, 0, 0,
    0⟩ = 0 := unique_scalar_zero ne_W22 (unique_piece_kw56 thA thB rhoL Δ st56)
  have s257 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ
    ⟨0, 1, 0, 1, 0, 0, 1, 0⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨0, 2, 1, 1, 0, 0, 0,
    0⟩ = 0 := unique_scalar_zero ne_W22 (unique_piece_kw57 thA thB rhoL Δ st57 st60)
  have s258 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ
    ⟨0, 1, 0, 1, 0, 1, 0, 0⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨1, 1, 0, 2, 0, 0, 0,
    0⟩ = 0 := unique_scalar_zero ne_W22 (unique_piece_kw58 thA thB rhoL Δ st58 st67)
  have s259 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ
    ⟨0, 1, 0, 1, 1, 0, 0, 0⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨1, 1, 1, 1, 0, 0, 0,
    0⟩ = 0 := unique_scalar_zero ne_W22 (unique_piece_kw59 thA thB rhoL Δ st59 st71)
  have s260 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ
    ⟨0, 1, 1, 0, 0, 0, 0, 1⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨0, 2, 1, 1, 0, 0, 0,
    0⟩ = 0 := unique_scalar_zero ne_W22 (unique_piece_kw60 thA thB rhoL Δ st57 st60)
  have s261 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ
    ⟨0, 1, 1, 0, 0, 0, 1, 0⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨0, 2, 2, 0, 0, 0, 0,
    0⟩ = 0 := unique_scalar_zero ne_W22 (unique_piece_kw61 thA thB rhoL Δ st61)
  have s262 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ
    ⟨0, 1, 1, 0, 0, 1, 0, 0⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨1, 1, 1, 1, 0, 0, 0,
    0⟩ = 0 := unique_scalar_zero ne_W22 (unique_piece_kw62 thA thB rhoL Δ st62 st68)
  have s263 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ
    ⟨0, 1, 1, 0, 1, 0, 0, 0⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨1, 1, 2, 0, 0, 0, 0,
    0⟩ = 0 := unique_scalar_zero ne_W22 (unique_piece_kw63 thA thB rhoL Δ st63 st72)
  have s267 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ
    ⟨1, 0, 0, 1, 0, 0, 0, 1⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨1, 1, 0, 2, 0, 0, 0,
    0⟩ = 0 := unique_scalar_zero ne_W22 (unique_piece_kw67 thA thB rhoL Δ st58 st67)
  have s268 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ
    ⟨1, 0, 0, 1, 0, 0, 1, 0⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨1, 1, 1, 1, 0, 0, 0,
    0⟩ = 0 := unique_scalar_zero ne_W22 (unique_piece_kw68 thA thB rhoL Δ st62 st68)
  have s269 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ
    ⟨1, 0, 0, 1, 0, 1, 0, 0⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨2, 0, 0, 2, 0, 0, 0,
    0⟩ = 0 := unique_scalar_zero ne_W22 (unique_piece_kw69 thA thB rhoL Δ st69)
  have s270 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ
    ⟨1, 0, 0, 1, 1, 0, 0, 0⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨2, 0, 1, 1, 0, 0, 0,
    0⟩ = 0 := unique_scalar_zero ne_W22 (unique_piece_kw70 thA thB rhoL Δ st70 st73)
  have s271 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ
    ⟨1, 0, 1, 0, 0, 0, 0, 1⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨1, 1, 1, 1, 0, 0, 0,
    0⟩ = 0 := unique_scalar_zero ne_W22 (unique_piece_kw71 thA thB rhoL Δ st59 st71)
  have s272 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ
    ⟨1, 0, 1, 0, 0, 0, 1, 0⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨1, 1, 2, 0, 0, 0, 0,
    0⟩ = 0 := unique_scalar_zero ne_W22 (unique_piece_kw72 thA thB rhoL Δ st63 st72)
  have s273 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ
    ⟨1, 0, 1, 0, 0, 1, 0, 0⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨2, 0, 1, 1, 0, 0, 0,
    0⟩ = 0 := unique_scalar_zero ne_W22 (unique_piece_kw73 thA thB rhoL Δ st70 st73)
  have s274 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ
    ⟨1, 0, 1, 0, 1, 0, 0, 0⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨2, 0, 2, 0, 0, 0, 0,
    0⟩ = 0 := unique_scalar_zero ne_W22 (unique_piece_kw74 thA thB rhoL Δ st74)
  have h64 := unique_piece_h64 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z26 z36
  have z64 : Δ ⟨0, 2, 0, 2, 0, 0, 0, 0⟩ = 0 := unique_scalar_zero ne_D22 (unique_piece_k64 thA thB
    rhoL Δ s256 h64)
  have h65 := unique_piece_h65 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z27 z36 z37
  have z65 : Δ ⟨0, 2, 1, 1, 0, 0, 0, 0⟩ = 0 := unique_scalar_zero ne_D22 (unique_piece_k65 thA thB
    rhoL Δ s257 s260 h65)
  have h66 := unique_piece_h66 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z28 z37
  have z66 : Δ ⟨0, 2, 2, 0, 0, 0, 0, 0⟩ = 0 := unique_scalar_zero ne_D22 (unique_piece_k66 thA thB
    rhoL Δ s261 h66)
  have h75 := unique_piece_h75 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z26 z29 z42
  have z75 : Δ ⟨1, 1, 0, 2, 0, 0, 0, 0⟩ = 0 := unique_scalar_zero ne_D22 (unique_piece_k75 thA thB
    rhoL Δ s258 s267 h75)
  have h76 := unique_piece_h76 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z27 z30 z42 z43
  have z76 : Δ ⟨1, 1, 1, 1, 0, 0, 0, 0⟩ = 0 := unique_scalar_zero ne_D22 (unique_piece_k76 thA thB
    rhoL Δ s259 s262 s268 s271 h76)
  have h77 := unique_piece_h77 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z28 z31 z43
  have z77 : Δ ⟨1, 1, 2, 0, 0, 0, 0, 0⟩ = 0 := unique_scalar_zero ne_D22 (unique_piece_k77 thA thB
    rhoL Δ s263 s272 h77)
  have h78 := unique_piece_h78 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z29 z44
  have z78 : Δ ⟨2, 0, 0, 2, 0, 0, 0, 0⟩ = 0 := unique_scalar_zero ne_D22 (unique_piece_k78 thA thB
    rhoL Δ s269 h78)
  have h79 := unique_piece_h79 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z30 z44 z45
  have z79 : Δ ⟨2, 0, 1, 1, 0, 0, 0, 0⟩ = 0 := unique_scalar_zero ne_D22 (unique_piece_k79 thA thB
    rhoL Δ s270 s273 h79)
  have h80 := unique_piece_h80 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z31 z45
  have z80 : Δ ⟨2, 0, 2, 0, 0, 0, 0, 0⟩ = 0 := unique_scalar_zero ne_D22 (unique_piece_k80 thA thB
    rhoL Δ s274 h80)
  have z56 : Δ ⟨0, 1, 0, 1, 0, 0, 0, 1⟩ = 0 := unique_scalar_zero ne_W4_22 (unique_piece_k56 thA thB
    rhoL Δ s256 z64)
  have z57 : Δ ⟨0, 1, 0, 1, 0, 0, 1, 0⟩ = 0 := unique_scalar_zero ne_W4_22 (unique_piece_k57 thA thB
    rhoL Δ s257 z65)
  have z58 : Δ ⟨0, 1, 0, 1, 0, 1, 0, 0⟩ = 0 := unique_scalar_zero ne_W4_22 (unique_piece_k58 thA thB
    rhoL Δ s258 z75)
  have z59 : Δ ⟨0, 1, 0, 1, 1, 0, 0, 0⟩ = 0 := unique_scalar_zero ne_W4_22 (unique_piece_k59 thA thB
    rhoL Δ s259 z76)
  have z60 : Δ ⟨0, 1, 1, 0, 0, 0, 0, 1⟩ = 0 := unique_scalar_zero ne_W4_22 (unique_piece_k60 thA thB
    rhoL Δ s260 z65)
  have z61 : Δ ⟨0, 1, 1, 0, 0, 0, 1, 0⟩ = 0 := unique_scalar_zero ne_W4_22 (unique_piece_k61 thA thB
    rhoL Δ s261 z66)
  have z62 : Δ ⟨0, 1, 1, 0, 0, 1, 0, 0⟩ = 0 := unique_scalar_zero ne_W4_22 (unique_piece_k62 thA thB
    rhoL Δ s262 z76)
  have z63 : Δ ⟨0, 1, 1, 0, 1, 0, 0, 0⟩ = 0 := unique_scalar_zero ne_W4_22 (unique_piece_k63 thA thB
    rhoL Δ s263 z77)
  have z67 : Δ ⟨1, 0, 0, 1, 0, 0, 0, 1⟩ = 0 := unique_scalar_zero ne_W4_22 (unique_piece_k67 thA thB
    rhoL Δ s267 z75)
  have z68 : Δ ⟨1, 0, 0, 1, 0, 0, 1, 0⟩ = 0 := unique_scalar_zero ne_W4_22 (unique_piece_k68 thA thB
    rhoL Δ s268 z76)
  have z69 : Δ ⟨1, 0, 0, 1, 0, 1, 0, 0⟩ = 0 := unique_scalar_zero ne_W4_22 (unique_piece_k69 thA thB
    rhoL Δ s269 z78)
  have z70 : Δ ⟨1, 0, 0, 1, 1, 0, 0, 0⟩ = 0 := unique_scalar_zero ne_W4_22 (unique_piece_k70 thA thB
    rhoL Δ s270 z79)
  have z71 : Δ ⟨1, 0, 1, 0, 0, 0, 0, 1⟩ = 0 := unique_scalar_zero ne_W4_22 (unique_piece_k71 thA thB
    rhoL Δ s271 z76)
  have z72 : Δ ⟨1, 0, 1, 0, 0, 0, 1, 0⟩ = 0 := unique_scalar_zero ne_W4_22 (unique_piece_k72 thA thB
    rhoL Δ s272 z77)
  have z73 : Δ ⟨1, 0, 1, 0, 0, 1, 0, 0⟩ = 0 := unique_scalar_zero ne_W4_22 (unique_piece_k73 thA thB
    rhoL Δ s273 z79)
  have z74 : Δ ⟨1, 0, 1, 0, 1, 0, 0, 0⟩ = 0 := unique_scalar_zero ne_W4_22 (unique_piece_k74 thA thB
    rhoL Δ s274 z80)
  have z46 : Δ ⟨0, 0, 0, 0, 0, 0, 0, 2⟩ = 0 := unique_scalar_zero ne_d2_22 (unique_piece_k46 thA thB
    rhoL Δ h46 z56)
  have z47 : Δ ⟨0, 0, 0, 0, 0, 0, 1, 1⟩ = 0 := unique_scalar_zero ne_d2_22 (unique_piece_k47 thA thB
    rhoL Δ h47 z57 z60)
  have z48 : Δ ⟨0, 0, 0, 0, 0, 0, 2, 0⟩ = 0 := unique_scalar_zero ne_d2_22 (unique_piece_k48 thA thB
    rhoL Δ h48 z61)
  have z49 : Δ ⟨0, 0, 0, 0, 0, 1, 0, 1⟩ = 0 := unique_scalar_zero ne_d2_22 (unique_piece_k49 thA thB
    rhoL Δ h49 z58 z67)
  have z50 : Δ ⟨0, 0, 0, 0, 0, 1, 1, 0⟩ = 0 := unique_scalar_zero ne_d2_22 (unique_piece_k50 thA thB
    rhoL Δ h50 z62 z68)
  have z51 : Δ ⟨0, 0, 0, 0, 0, 2, 0, 0⟩ = 0 := unique_scalar_zero ne_d2_22 (unique_piece_k51 thA thB
    rhoL Δ h51 z69)
  have z52 : Δ ⟨0, 0, 0, 0, 1, 0, 0, 1⟩ = 0 := unique_scalar_zero ne_d2_22 (unique_piece_k52 thA thB
    rhoL Δ h52 z59 z71)
  have z53 : Δ ⟨0, 0, 0, 0, 1, 0, 1, 0⟩ = 0 := unique_scalar_zero ne_d2_22 (unique_piece_k53 thA thB
    rhoL Δ h53 z63 z72)
  have z54 : Δ ⟨0, 0, 0, 0, 1, 1, 0, 0⟩ = 0 := unique_scalar_zero ne_d2_22 (unique_piece_k54 thA thB
    rhoL Δ h54 z70 z73)
  have z55 : Δ ⟨0, 0, 0, 0, 2, 0, 0, 0⟩ = 0 := unique_scalar_zero ne_d2_22 (unique_piece_k55 thA thB
    rhoL Δ h55 z74)
  exact ⟨z46, z47, z48, z49, z50, z51, z52, z53, z54, z55, z56, z57, z58, z59, z60, z61, z62, z63,
    z64, z65, z66, z67, z68, z69, z70, z71, z72, z73, z74, z75, z76, z77, z78, z79, z80⟩

end Rhone.Algebra.KilledSystem
