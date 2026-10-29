/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.GeneralMutation.Block

/-! # The stationary weight of the two-locus general-mutation-matrix system -/

@[expose] public section

namespace Rhone.MarkovChain.GeneralMutation

open Finset LinearAlgebra.Recursion

variable {KA KB : ℕ} {F : Type*} [Field F]
variable {νA : Fin KA → F} {νB : Fin KB → F}

def wtC (νA : Fin KA → F) (νB : Fin KB → F) (ξ : Config KA KB) : F :=
  Biallelic.wt νA ξ.mA * Biallelic.wt νB ξ.mB

theorem wtC_pos [LinearOrder F] [IsStrictOrderedRing F] (hνA : ∀ i, 0 < νA i)
    (hνB : ∀ j, 0 < νB j) (ξ : Config KA KB) : 0 < wtC νA νB ξ :=
  mul_pos (Biallelic.wt_pos hνA _) (Biallelic.wt_pos hνB _)

variable (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) (k : Fin KA) (l : Fin KB)

theorem wtC_mergeAB (ha : ξ.a i ≠ 0) (hb : ξ.b j ≠ 0) :
    wtC νA νB (ξ.mergeAB i j) = wtC νA νB ξ := by
  rw [wtC, wtC, Config.mA_mergeAB ξ j ha, Config.mB_mergeAB ξ i hb]

theorem wtC_split (hc : ξ.c i j ≠ 0) : wtC νA νB (ξ.split i j) = wtC νA νB ξ := by
  rw [wtC, wtC, Config.mA_split ξ hc, Config.mB_split ξ hc]

theorem wtC_mutA (ha : ξ.a i ≠ 0) :
    wtC νA νB (mutA ξ i k) * νA i = wtC νA νB ξ * νA k := by
  have hmA : ξ.mA i ≠ 0 := by simp only [Config.mA]; omega
  rw [wtC, wtC, mA_mutA ξ i k ha, mB_mutA ξ i k, mul_right_comm,
    Biallelic.wt_incf_decf k hmA, mul_right_comm]

theorem wtC_mutB (hb : ξ.b j ≠ 0) :
    wtC νA νB (mutB ξ j l) * νB j = wtC νA νB ξ * νB l := by
  have hmB : ξ.mB j ≠ 0 := by simp only [Config.mB]; omega
  rw [wtC, wtC, mB_mutB ξ j l hb, mA_mutB ξ j l, mul_assoc,
    Biallelic.wt_incf_decf l hmB, mul_assoc]

theorem wtC_mutCA (hc : ξ.c i j ≠ 0) :
    wtC νA νB (mutCA ξ i j k) * νA i = wtC νA νB ξ * νA k := by
  have hmA : ξ.mA i ≠ 0 := by
    have := Config.cRow_ne_zero ξ i j hc
    simp only [Config.mA]; omega
  rw [wtC, wtC, mA_mutCA ξ i j k hc, mB_mutCA ξ i j k hc, mul_right_comm,
    Biallelic.wt_incf_decf k hmA, mul_right_comm]

theorem wtC_mutCB (hc : ξ.c i j ≠ 0) :
    wtC νA νB (mutCB ξ i j l) * νB j = wtC νA νB ξ * νB l := by
  have hmB : ξ.mB j ≠ 0 := by
    have := Config.cCol_ne_zero ξ i j hc
    simp only [Config.mB]; omega
  rw [wtC, wtC, mB_mutCB ξ i j l hc, mA_mutCB ξ i j l hc, mul_assoc,
    Biallelic.wt_incf_decf l hmB, mul_assoc]

end Rhone.MarkovChain.GeneralMutation
