/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Init.Data.Rat

/-!
# Executable two-locus pair-time covariance

Source: griffiths1981, sec. 6, p. 178; hudson1983, eq. (1), p. 186; mcvean2002, eq. (9)–(12), pp.
988–989; wilton_carmi_hobolth2015, eq. (5). -/

@[expose] public section
namespace Rhone.Computation.HudsonCovariance

def denom (ρ : Rat) : Rat := ρ ^ 2 + 13 * ρ + 18

def chainValue (ρ : Rat) : Nat → Rat
  | 0 => 4 / denom ρ
  | 1 => 6 / denom ρ
  | 2 => (ρ + 18) / denom ρ
  | _ => 0

def pairTimeCovariance (ρ : Rat) : Rat := (ρ + 18) / denom ρ

def pairTimeProduct (ρ : Rat) : Rat := 1 + pairTimeCovariance ρ

def sigmaCombination (ρ : Rat) : Rat :=
  (chainValue ρ 2 - 2 * chainValue ρ 1 + chainValue ρ 0) / (1 + chainValue ρ 0)

end Rhone.Computation.HudsonCovariance
