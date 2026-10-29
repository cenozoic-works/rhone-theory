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

/-! # Exact lower-block assembly from separately checked elimination pieces -/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Rhone.Algebra.KilledSystem

theorem unique_lower_blocks {F : Type*} [Field F] (thA thB rhoL piA0 piA1 piB0 piB1 : F) (Δ : St →
    F)
    (ne_lhs02 : (2 + 2 * thB : F) ≠ 0)
    (ne_lhs20 : (2 + 2 * thA : F) ≠ 0)
    (ne_lhs11 : (2 + thA + thB : F) ≠ 0)
    (ne_E12 : ((6 + thA + 2 * thB) * (2 + thA + 2 * thB + rhoL) - 4 * rhoL : F) ≠ 0)
    (ne_d1_12 : (2 + thA + 2 * thB + rhoL : F) ≠ 0)
    (ne_E21 : ((6 + 2 * thA + thB) * (2 + 2 * thA + thB + rhoL) - 4 * rhoL : F) ≠ 0)
    (ne_d1_21 : (2 + 2 * thA + thB + rhoL : F) ≠ 0)
    (hrec : ∀ s ∈ recStates, lhsC thA thB rhoL s * Δ s = rhsC 1 (thA * piA0) (thA * piA1) (thB *
      piB0) (thB * piB1) rhoL Δ s)
    (hbd : ∀ s ∈ bdryStates, Δ s = 0)
    : Δ ⟨0, 0, 0, 1, 0, 0, 0, 0⟩ = 0 ∧ Δ ⟨0, 0, 1, 0, 0, 0, 0, 0⟩ = 0 ∧ Δ ⟨0, 1, 0, 0, 0, 0, 0, 0⟩ =
      0 ∧ Δ ⟨1, 0, 0, 0, 0, 0, 0, 0⟩ = 0 ∧ Δ ⟨0, 0, 0, 2, 0, 0, 0, 0⟩ = 0 ∧ Δ ⟨0, 0, 1, 1, 0, 0, 0,
      0⟩ = 0 ∧ Δ ⟨0, 0, 2, 0, 0, 0, 0, 0⟩ = 0 ∧ Δ ⟨0, 0, 0, 0, 0, 0, 0, 1⟩ = 0 ∧ Δ ⟨0, 0, 0, 0, 0,
      0, 1, 0⟩ = 0 ∧ Δ ⟨0, 0, 0, 0, 0, 1, 0, 0⟩ = 0 ∧ Δ ⟨0, 0, 0, 0, 1, 0, 0, 0⟩ = 0 ∧ Δ ⟨0, 1, 0,
      1, 0, 0, 0, 0⟩ = 0 ∧ Δ ⟨0, 1, 1, 0, 0, 0, 0, 0⟩ = 0 ∧ Δ ⟨1, 0, 0, 1, 0, 0, 0, 0⟩ = 0 ∧ Δ ⟨1,
      0, 1, 0, 0, 0, 0, 0⟩ = 0 ∧ Δ ⟨0, 2, 0, 0, 0, 0, 0, 0⟩ = 0 ∧ Δ ⟨1, 1, 0, 0, 0, 0, 0, 0⟩ = 0 ∧ Δ
      ⟨2, 0, 0, 0, 0, 0, 0, 0⟩ = 0 ∧ Δ ⟨0, 0, 0, 1, 0, 0, 0, 1⟩ = 0 ∧ Δ ⟨0, 0, 0, 1, 0, 0, 1, 0⟩ = 0
      ∧ Δ ⟨0, 0, 0, 1, 0, 1, 0, 0⟩ = 0 ∧ Δ ⟨0, 0, 0, 1, 1, 0, 0, 0⟩ = 0 ∧ Δ ⟨0, 0, 1, 0, 0, 0, 0, 1⟩
      = 0 ∧ Δ ⟨0, 0, 1, 0, 0, 0, 1, 0⟩ = 0 ∧ Δ ⟨0, 0, 1, 0, 0, 1, 0, 0⟩ = 0 ∧ Δ ⟨0, 0, 1, 0, 1, 0,
      0, 0⟩ = 0 ∧ Δ ⟨0, 1, 0, 2, 0, 0, 0, 0⟩ = 0 ∧ Δ ⟨0, 1, 1, 1, 0, 0, 0, 0⟩ = 0 ∧ Δ ⟨0, 1, 2, 0,
      0, 0, 0, 0⟩ = 0 ∧ Δ ⟨1, 0, 0, 2, 0, 0, 0, 0⟩ = 0 ∧ Δ ⟨1, 0, 1, 1, 0, 0, 0, 0⟩ = 0 ∧ Δ ⟨1, 0,
      2, 0, 0, 0, 0, 0⟩ = 0 ∧ Δ ⟨0, 1, 0, 0, 0, 0, 0, 1⟩ = 0 ∧ Δ ⟨0, 1, 0, 0, 0, 0, 1, 0⟩ = 0 ∧ Δ
      ⟨0, 1, 0, 0, 0, 1, 0, 0⟩ = 0 ∧ Δ ⟨0, 1, 0, 0, 1, 0, 0, 0⟩ = 0 ∧ Δ ⟨0, 2, 0, 1, 0, 0, 0, 0⟩ = 0
      ∧ Δ ⟨0, 2, 1, 0, 0, 0, 0, 0⟩ = 0 ∧ Δ ⟨1, 0, 0, 0, 0, 0, 0, 1⟩ = 0 ∧ Δ ⟨1, 0, 0, 0, 0, 0, 1, 0⟩
      = 0 ∧ Δ ⟨1, 0, 0, 0, 0, 1, 0, 0⟩ = 0 ∧ Δ ⟨1, 0, 0, 0, 1, 0, 0, 0⟩ = 0 ∧ Δ ⟨1, 1, 0, 1, 0, 0,
      0, 0⟩ = 0 ∧ Δ ⟨1, 1, 1, 0, 0, 0, 0, 0⟩ = 0 ∧ Δ ⟨2, 0, 0, 1, 0, 0, 0, 0⟩ = 0 ∧ Δ ⟨2, 0, 1, 0,
      0, 0, 0, 0⟩ = 0 := by
  have z0 : Δ ⟨0, 0, 0, 1, 0, 0, 0, 0⟩ = 0 := hbd _ (by decide)
  have z1 : Δ ⟨0, 0, 1, 0, 0, 0, 0, 0⟩ = 0 := hbd _ (by decide)
  have z2 : Δ ⟨0, 1, 0, 0, 0, 0, 0, 0⟩ = 0 := hbd _ (by decide)
  have z3 : Δ ⟨1, 0, 0, 0, 0, 0, 0, 0⟩ = 0 := hbd _ (by decide)
  have z7 : Δ ⟨0, 0, 0, 0, 0, 0, 0, 1⟩ = 0 := hbd _ (by decide)
  have z8 : Δ ⟨0, 0, 0, 0, 0, 0, 1, 0⟩ = 0 := hbd _ (by decide)
  have z9 : Δ ⟨0, 0, 0, 0, 0, 1, 0, 0⟩ = 0 := hbd _ (by decide)
  have z10 : Δ ⟨0, 0, 0, 0, 1, 0, 0, 0⟩ = 0 := hbd _ (by decide)
  have h4 := unique_piece_h4 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z0
  have z4 : Δ ⟨0, 0, 0, 2, 0, 0, 0, 0⟩ = 0 := unique_scalar_zero ne_lhs02 (unique_piece_k4 thB Δ h4)
  have h5 := unique_piece_h5 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z0 z1
  have z5 : Δ ⟨0, 0, 1, 1, 0, 0, 0, 0⟩ = 0 := unique_scalar_zero ne_lhs02 (unique_piece_k5 thB Δ h5)
  have h6 := unique_piece_h6 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z1
  have z6 : Δ ⟨0, 0, 2, 0, 0, 0, 0, 0⟩ = 0 := unique_scalar_zero ne_lhs02 (unique_piece_k6 thB Δ h6)
  have h11 := unique_piece_h11 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z0 z2 z7
  have z11 : Δ ⟨0, 1, 0, 1, 0, 0, 0, 0⟩ = 0 := unique_scalar_zero ne_lhs11 (unique_piece_k11 thA thB
    Δ h11)
  have h12 := unique_piece_h12 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z1 z2 z8
  have z12 : Δ ⟨0, 1, 1, 0, 0, 0, 0, 0⟩ = 0 := unique_scalar_zero ne_lhs11 (unique_piece_k12 thA thB
    Δ h12)
  have h13 := unique_piece_h13 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z0 z3 z9
  have z13 : Δ ⟨1, 0, 0, 1, 0, 0, 0, 0⟩ = 0 := unique_scalar_zero ne_lhs11 (unique_piece_k13 thA thB
    Δ h13)
  have h14 := unique_piece_h14 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z1 z3 z10
  have z14 : Δ ⟨1, 0, 1, 0, 0, 0, 0, 0⟩ = 0 := unique_scalar_zero ne_lhs11 (unique_piece_k14 thA thB
    Δ h14)
  have h15 := unique_piece_h15 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z2
  have z15 : Δ ⟨0, 2, 0, 0, 0, 0, 0, 0⟩ = 0 := unique_scalar_zero ne_lhs20 (unique_piece_k15 thA Δ
    h15)
  have h16 := unique_piece_h16 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z2 z3
  have z16 : Δ ⟨1, 1, 0, 0, 0, 0, 0, 0⟩ = 0 := unique_scalar_zero ne_lhs20 (unique_piece_k16 thA Δ
    h16)
  have h17 := unique_piece_h17 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z3
  have z17 : Δ ⟨2, 0, 0, 0, 0, 0, 0, 0⟩ = 0 := unique_scalar_zero ne_lhs20 (unique_piece_k17 thA Δ
    h17)
  have h26 := unique_piece_h26 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z4 z11
  have h18 := unique_piece_h18 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z7 z4 z11
  have z26 : Δ ⟨0, 1, 0, 2, 0, 0, 0, 0⟩ = 0 := unique_scalar_zero ne_E12 (unique_piece_k26 thA thB
    rhoL Δ h26 h18)
  have h27 := unique_piece_h27 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z5 z11 z12
  have h19 := unique_piece_h19 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z8 z5 z11
  have h22 := unique_piece_h22 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z7 z5 z12
  have z27 : Δ ⟨0, 1, 1, 1, 0, 0, 0, 0⟩ = 0 := unique_scalar_zero ne_E12 (unique_piece_k27 thA thB
    rhoL Δ h27 h19 h22)
  have h28 := unique_piece_h28 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z6 z12
  have h23 := unique_piece_h23 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z8 z6 z12
  have z28 : Δ ⟨0, 1, 2, 0, 0, 0, 0, 0⟩ = 0 := unique_scalar_zero ne_E12 (unique_piece_k28 thA thB
    rhoL Δ h28 h23)
  have h29 := unique_piece_h29 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z4 z13
  have h20 := unique_piece_h20 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z9 z4 z13
  have z29 : Δ ⟨1, 0, 0, 2, 0, 0, 0, 0⟩ = 0 := unique_scalar_zero ne_E12 (unique_piece_k29 thA thB
    rhoL Δ h29 h20)
  have h30 := unique_piece_h30 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z5 z13 z14
  have h21 := unique_piece_h21 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z10 z5 z13
  have h24 := unique_piece_h24 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z9 z5 z14
  have z30 : Δ ⟨1, 0, 1, 1, 0, 0, 0, 0⟩ = 0 := unique_scalar_zero ne_E12 (unique_piece_k30 thA thB
    rhoL Δ h30 h21 h24)
  have h31 := unique_piece_h31 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z6 z14
  have h25 := unique_piece_h25 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z10 z6 z14
  have z31 : Δ ⟨1, 0, 2, 0, 0, 0, 0, 0⟩ = 0 := unique_scalar_zero ne_E12 (unique_piece_k31 thA thB
    rhoL Δ h31 h25)
  have z18 : Δ ⟨0, 0, 0, 1, 0, 0, 0, 1⟩ = 0 := unique_scalar_zero ne_d1_12 (unique_piece_k18 thA thB
    rhoL Δ h18 z26)
  have z19 : Δ ⟨0, 0, 0, 1, 0, 0, 1, 0⟩ = 0 := unique_scalar_zero ne_d1_12 (unique_piece_k19 thA thB
    rhoL Δ h19 z27)
  have z20 : Δ ⟨0, 0, 0, 1, 0, 1, 0, 0⟩ = 0 := unique_scalar_zero ne_d1_12 (unique_piece_k20 thA thB
    rhoL Δ h20 z29)
  have z21 : Δ ⟨0, 0, 0, 1, 1, 0, 0, 0⟩ = 0 := unique_scalar_zero ne_d1_12 (unique_piece_k21 thA thB
    rhoL Δ h21 z30)
  have z22 : Δ ⟨0, 0, 1, 0, 0, 0, 0, 1⟩ = 0 := unique_scalar_zero ne_d1_12 (unique_piece_k22 thA thB
    rhoL Δ h22 z27)
  have z23 : Δ ⟨0, 0, 1, 0, 0, 0, 1, 0⟩ = 0 := unique_scalar_zero ne_d1_12 (unique_piece_k23 thA thB
    rhoL Δ h23 z28)
  have z24 : Δ ⟨0, 0, 1, 0, 0, 1, 0, 0⟩ = 0 := unique_scalar_zero ne_d1_12 (unique_piece_k24 thA thB
    rhoL Δ h24 z30)
  have z25 : Δ ⟨0, 0, 1, 0, 1, 0, 0, 0⟩ = 0 := unique_scalar_zero ne_d1_12 (unique_piece_k25 thA thB
    rhoL Δ h25 z31)
  have h36 := unique_piece_h36 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z11 z15
  have h32 := unique_piece_h32 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z7 z11 z15
  have z36 : Δ ⟨0, 2, 0, 1, 0, 0, 0, 0⟩ = 0 := unique_scalar_zero ne_E21 (unique_piece_k36 thA thB
    rhoL Δ h36 h32)
  have h37 := unique_piece_h37 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z12 z15
  have h33 := unique_piece_h33 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z8 z12 z15
  have z37 : Δ ⟨0, 2, 1, 0, 0, 0, 0, 0⟩ = 0 := unique_scalar_zero ne_E21 (unique_piece_k37 thA thB
    rhoL Δ h37 h33)
  have h42 := unique_piece_h42 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z11 z13 z16
  have h34 := unique_piece_h34 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z9 z11 z16
  have h38 := unique_piece_h38 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z7 z13 z16
  have z42 : Δ ⟨1, 1, 0, 1, 0, 0, 0, 0⟩ = 0 := unique_scalar_zero ne_E21 (unique_piece_k42 thA thB
    rhoL Δ h42 h34 h38)
  have h43 := unique_piece_h43 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z12 z14 z16
  have h35 := unique_piece_h35 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z10 z12 z16
  have h39 := unique_piece_h39 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z8 z14 z16
  have z43 : Δ ⟨1, 1, 1, 0, 0, 0, 0, 0⟩ = 0 := unique_scalar_zero ne_E21 (unique_piece_k43 thA thB
    rhoL Δ h43 h35 h39)
  have h44 := unique_piece_h44 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z13 z17
  have h40 := unique_piece_h40 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z9 z13 z17
  have z44 : Δ ⟨2, 0, 0, 1, 0, 0, 0, 0⟩ = 0 := unique_scalar_zero ne_E21 (unique_piece_k44 thA thB
    rhoL Δ h44 h40)
  have h45 := unique_piece_h45 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z14 z17
  have h41 := unique_piece_h41 thA thB rhoL piA0 piA1 piB0 piB1 Δ hrec z10 z14 z17
  have z45 : Δ ⟨2, 0, 1, 0, 0, 0, 0, 0⟩ = 0 := unique_scalar_zero ne_E21 (unique_piece_k45 thA thB
    rhoL Δ h45 h41)
  have z32 : Δ ⟨0, 1, 0, 0, 0, 0, 0, 1⟩ = 0 := unique_scalar_zero ne_d1_21 (unique_piece_k32 thA thB
    rhoL Δ h32 z36)
  have z33 : Δ ⟨0, 1, 0, 0, 0, 0, 1, 0⟩ = 0 := unique_scalar_zero ne_d1_21 (unique_piece_k33 thA thB
    rhoL Δ h33 z37)
  have z34 : Δ ⟨0, 1, 0, 0, 0, 1, 0, 0⟩ = 0 := unique_scalar_zero ne_d1_21 (unique_piece_k34 thA thB
    rhoL Δ h34 z42)
  have z35 : Δ ⟨0, 1, 0, 0, 1, 0, 0, 0⟩ = 0 := unique_scalar_zero ne_d1_21 (unique_piece_k35 thA thB
    rhoL Δ h35 z43)
  have z38 : Δ ⟨1, 0, 0, 0, 0, 0, 0, 1⟩ = 0 := unique_scalar_zero ne_d1_21 (unique_piece_k38 thA thB
    rhoL Δ h38 z42)
  have z39 : Δ ⟨1, 0, 0, 0, 0, 0, 1, 0⟩ = 0 := unique_scalar_zero ne_d1_21 (unique_piece_k39 thA thB
    rhoL Δ h39 z43)
  have z40 : Δ ⟨1, 0, 0, 0, 0, 1, 0, 0⟩ = 0 := unique_scalar_zero ne_d1_21 (unique_piece_k40 thA thB
    rhoL Δ h40 z44)
  have z41 : Δ ⟨1, 0, 0, 0, 1, 0, 0, 0⟩ = 0 := unique_scalar_zero ne_d1_21 (unique_piece_k41 thA thB
    rhoL Δ h41 z45)
  exact ⟨z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17, z18, z19,
    z20, z21, z22, z23, z24, z25, z26, z27, z28, z29, z30, z31, z32, z33, z34, z35, z36, z37, z38,
    z39, z40, z41, z42, z43, z44, z45⟩

end Rhone.Algebra.KilledSystem
