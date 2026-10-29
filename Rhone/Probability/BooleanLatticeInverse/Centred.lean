/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.BooleanLatticeInverse.SamplingDefs
public import Rhone.Probability.Multilinear.Basic

/-! # The centred test vectors -/

@[expose] public section

namespace Rhone.Probability.BooleanLatticeInverse

open Finset LinearAlgebra.Recursion LinearAlgebra.Multilinear Multilinear

variable {KA : ℕ} {F : Type*} [Field F]

def fA (πA : Fin KA → F) (p : Fin KA) : Fin KA → F := Pi.single p 1 - πA p • 1

def gB (πB : Fin 2 → F) : Fin 2 → F := Pi.single 0 1 - πB 0 • 1

theorem single_eq_fA (πA : Fin KA → F) (p : Fin KA) :
    (Pi.single p 1 : Fin KA → F) = πA p • 1 + fA πA p := by
  simp [fA]

theorem fA_mul_fA (πA : Fin KA → F) (p p' : Fin KA) :
    fA πA p * fA πA p' = LinearAlgebra.BooleanLatticeInverse.kapA πA p p' • (1 : Fin KA → F)
      + ((if p = p' then (1 : F) else 0) - πA p') • fA πA p - πA p • fA πA p' := by
  funext k
  unfold LinearAlgebra.BooleanLatticeInverse.kapA
  by_cases h : p = p'
  · subst h
    by_cases hk : k = p
    · subst hk; simp [fA]; ring
    · simp [fA, hk]; ring
  · by_cases hk : k = p
    · subst hk; simp [fA, h]; ring
    · by_cases hk' : k = p'
      · subst hk'; simp [fA, hk, h]; ring
      · simp [fA, hk, hk', h]; ring

theorem mean_fA {πA : Fin KA → F} (hπA : ∑ i, πA i = 1) (p : Fin KA) :
    mean πA (fA πA p) = 0 := by
  simp only [mean, fA, Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one, mul_sub,
    Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, ← Finset.sum_mul, hπA]
  ring

section Biallelic

variable {πB : Fin 2 → F} (hπB : πB 0 + πB 1 = 1)
include hπB

theorem single_eq_gB (b : Fin 2) :
    (Pi.single b 1 : Fin 2 → F) = πB b • 1 + LinearAlgebra.BooleanLatticeInverse.sgnB (F := F) b •
        gB πB := by
  have h1 : πB 1 = 1 - πB 0 := by linear_combination hπB
  funext k
  fin_cases b <;> fin_cases k <;> simp [gB, LinearAlgebra.BooleanLatticeInverse.sgnB, h1]

theorem gB_mul_gB : gB πB * gB πB = LinearAlgebra.BooleanLatticeInverse.kapB πB • (1 : Fin 2 → F) +
    LinearAlgebra.BooleanLatticeInverse.gamB πB • gB πB := by
  have h1 : πB 1 = 1 - πB 0 := by linear_combination hπB
  funext k
  fin_cases k <;> simp
      [gB, LinearAlgebra.BooleanLatticeInverse.kapB, LinearAlgebra.BooleanLatticeInverse.gamB,
      h1] <;> ring

theorem mean_gB : mean πB (gB πB) = 0 := by
  have h1 : πB 1 = 1 - πB 0 := by linear_combination hπB
  simp [mean, Fin.sum_univ_two, gB, h1]
  ring

end Biallelic

end Rhone.Probability.BooleanLatticeInverse
