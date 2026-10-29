/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.TwoGameteBridge.Config

/-! # The finite system's 28 terms equal the general killed-PIM recursion -/

@[expose] public section

namespace Rhone.Algebra.TwoGameteBridge

open KilledSystem LinearAlgebra.Recursion

variable {R : Type*} [CommRing R]

theorem diag_toConfig (θA θB ρ : R) (s : St) :
    diag θA θB ρ (toConfig s) = lhsC θA θB ρ s := by
  simp only [diag, lhsC, n_toConfig, nA_toConfig, nB_toConfig, t_toConfig]

theorem rhs_toConfig (θA θB ρ : R) (πA πB : Fin 2 → R) (q : St → R) (s : St) :
    rhs θA θB ρ πA πB (fun ξ => q (ofConfig ξ)) (toConfig s) =
      rhsC 1 (θA * πA 0) (θA * πA 1) (θB * πB 0) (θB * πB 1) ρ q s := by
  simp [rhs, rhsC, rterms, pfac, Fin.sum_univ_two, Config.coalA, Config.coalB,
    Config.coalC, Config.coalAB, Config.cRow, Config.cCol, Config.dropA, Config.dropB,
    Config.dropC, Config.mergeAB, Config.killA, Config.killB, Config.split,
    Config.decC, Config.incC, decf, incf, toConfig, ofConfig, St.cr0, St.cr1, St.cc0, St.cc1]
  ring

theorem rhs_restrict (θA θB ρ : R) (πA πB : Fin 2 → R)
    (Q : Config 2 2 → R) (s : St) :
    rhs θA θB ρ πA πB Q (toConfig s) =
      rhsC 1 (θA * πA 0) (θA * πA 1) (θB * πB 0) (θB * πB 1) ρ
        (fun s => Q (toConfig s)) s := by
  simpa only [toConfig_ofConfig] using
    rhs_toConfig θA θB ρ πA πB (fun s => Q (toConfig s)) s

end Rhone.Algebra.TwoGameteBridge
