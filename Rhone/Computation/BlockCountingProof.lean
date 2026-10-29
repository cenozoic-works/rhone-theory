/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.BlockCounting
public import Rhone.Coalescent.KingmanChain
public import Mathlib.Basic.Real.Basic

/-!
# Executable block-counting generator equals the specification

Source: kingman1982, eq. (1.8)–(1.9). -/

@[expose] public section
namespace Rhone.Computation.BlockCounting

theorem rate_eq (k : Nat) : rate k = Rhone.Coalescent.coalRate k := by
  simp [rate, Rhone.Coalescent.coalRate]

theorem entry_eq (n : Nat) (k j : Fin (n + 1)) :
    ((entry k j : Rat) : ℝ) = (Rhone.Coalescent.blockChain n).Q k j := by
  rw [Rhone.Coalescent.blockChain_Q, Rhone.Coalescent.blockQ, entry, rate_eq]
  simp only [Rat.cast_mul, Rat.cast_sub, Fin.ext_iff]
  split_ifs <;> simp

theorem rate_eq_chain_rate (n : Nat) (k : Fin (n + 1)) :
    ((rate k : Rat) : ℝ) = (Rhone.Coalescent.blockChain n).rate k := by
  rw [Rhone.Coalescent.blockChain_rate, rate_eq]

theorem generator_getD (n : Nat) (k j : Fin (n + 1)) :
    ((generator n).getD k [] ).getD j 0 = entry k j := by
  simp [generator, row, List.getD_eq_getElem?_getD, List.getElem?_range k.2,
    List.getElem?_range j.2]

theorem generator_getD_eq (n : Nat) (k j : Fin (n + 1)) :
    ((((generator n).getD k []).getD j 0 : Rat) : ℝ) = (Rhone.Coalescent.blockChain n).Q k j := by
  rw [generator_getD, entry_eq]

end Rhone.Computation.BlockCounting
