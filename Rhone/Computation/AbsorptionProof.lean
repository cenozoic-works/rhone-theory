/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.AbsorptionCoreProof

/-! # Complete WF and selected Moran tables target their existing trajectory laws -/

@[expose] public section
namespace Rhone.Computation.Absorption
open MarkovChain MeasureTheory

theorem checkWf_iff_absorbTime (n : Nat) (hn : 0 < n) (table : Array Rat) :
    checkWf n table = true ↔ table.size = n + 1 ∧
      ∀ i : Fin (n + 1), (table.getD i 0 : Real) =
        (wfChain n).absorbTime (fixationBoundary n) i :=
  check_iff_absorbTime n (Drift.wfRow n) (wfChain n)
    (Drift.wfChain_P_eq n) (wfChain_isAbsorbingSet hn) (wfChain_reaches n) table

theorem checkMoran_iff_absorbTime (n : Nat) (_hn : 0 < n) (r : Rat)
    (hr : 0 < (r : Real)) (table : Array Rat) :
    checkMoran n r table = true ↔ table.size = n + 1 ∧
      ∀ i : Fin (n + 1), (table.getD i 0 : Real) =
        (moranChain n (r : Real) hr).absorbTime (fixationBoundary n) i :=
  check_iff_absorbTime n (Drift.moranRow n r) (moranChain n (r : Real) hr)
    (Drift.moranChain_P_eq n r hr) (moranChain_isAbsorbingSet n hr)
    (moranChain_reaches n hr) table

theorem checkWf_lintegral_hitTime (n : Nat) (hn : 0 < n) (table : Array Rat)
    (ht : checkWf n table = true) (i : Fin (n + 1)) :
    ∫⁻ ω, (hitTime (fixationBoundary n) ω : ENNReal) ∂(wfChain n).pathLaw i =
      ENNReal.ofReal (table.getD i 0 : Real) := by
  rw [FinChain.lintegral_hitTime (wfChain_isAbsorbingSet hn) (wfChain_reaches n)]
  exact congrArg ENNReal.ofReal (((checkWf_iff_absorbTime n hn table).1 ht).2 i).symm

theorem checkMoran_lintegral_hitTime (n : Nat) (hn : 0 < n) (r : Rat)
    (hr : 0 < (r : Real)) (table : Array Rat) (ht : checkMoran n r table = true)
    (i : Fin (n + 1)) :
    ∫⁻ ω, (hitTime (fixationBoundary n) ω : ENNReal)
      ∂(moranChain n (r : Real) hr).pathLaw i = ENNReal.ofReal (table.getD i 0 : Real) := by
  rw [FinChain.lintegral_hitTime (moranChain_isAbsorbingSet n hr) (moranChain_reaches n hr)]
  exact congrArg ENNReal.ofReal (((checkMoran_iff_absorbTime n hn r hr table).1 ht).2 i).symm

theorem checkWfReport_iff (n : Nat) (hn : 0 < n) (kernel : Array (Array Rat))
    (table : Array Rat) :
    checkWfReport n kernel table = true ↔ kernel = wfKernel n ∧ table.size = n + 1 ∧
      ∀ i : Fin (n + 1), (table.getD i 0 : Real) =
        (wfChain n).absorbTime (fixationBoundary n) i := by
  simp [checkWfReport, checkWf_iff_absorbTime n hn]

theorem checkMoranReport_iff (n : Nat) (hn : 0 < n) (r : Rat)
    (hr : 0 < (r : Real)) (kernel : Array (Array Rat)) (table : Array Rat) :
    checkMoranReport n r kernel table = true ↔ kernel = moranKernel n r ∧
      table.size = n + 1 ∧ ∀ i : Fin (n + 1), (table.getD i 0 : Real) =
        (moranChain n (r : Real) hr).absorbTime (fixationBoundary n) i := by
  simp [checkMoranReport, checkMoran_iff_absorbTime n hn r hr]

end Rhone.Computation.Absorption
