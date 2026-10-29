/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Init.Data.Rat

/-!
# Executable Ohta-Kimura stationary ratio

Source: ohta_kimura1971_ld, eq. (9), p. 574. -/

@[expose] public section
namespace Rhone.Computation.OhtaKimura

def ldSigmaNumerator (m c u : Rat) : Rat :=
  m ^ 3 * (m ^ 3 - (m - 2) ^ 2 * (m - 1) * (1 - c) * (1 - 2 * u) ^ 4)

def ldSigmaDenominator (m c u : Rat) : Rat :=
  let k := (1 - c) * (1 - 2 * u) ^ 4
  let l := (1 - c) ^ 2 * (1 - 2 * u) ^ 4
  let q := m ^ 3 - (m - 2) ^ 2 * (m - 1) * k
  (m - 1) * (q * (m ^ 3 - (m ^ 3 - 3 * m ^ 2 + 4 * m - 4) * l) -
    4 * (m - 1) ^ 2 * (m - 2) ^ 2 * k * l)

def ldSigma (m c u : Rat) : Rat := ldSigmaNumerator m c u / ldSigmaDenominator m c u

def ldSigmaLimit (R : Rat) : Rat := (10 + R) / (22 + 13 * R + R ^ 2)

end Rhone.Computation.OhtaKimura
