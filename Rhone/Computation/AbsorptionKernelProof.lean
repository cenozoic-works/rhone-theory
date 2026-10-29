/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.AbsorptionProof

/-! # Complete accepted kernel slots identify the entries of the mathematical chain -/

@[expose] public section
namespace Rhone.Computation.Absorption
open MarkovChain

theorem wfKernel_getD_eq (n : Nat) (i j : Fin (n + 1)) :
    (((wfKernel n).getD i #[]).getD j 0 : Real) = (wfChain n).P i j := by
  have hrow : (wfKernel n).getD i #[] = Drift.wfTransition n i := by
    simp [wfKernel, Array.getD, i.isLt, List.getElem_toArray,
      List.getElem_map, List.getElem_range]
  rw [hrow]
  exact Drift.wfTransition_getD_eq n i j

theorem moranKernel_getD_eq (n : Nat) (r : Rat) (hr : 0 < (r : Real))
    (i j : Fin (n + 1)) :
    (((moranKernel n r).getD i #[]).getD j 0 : Real) =
      (moranChain n (r : Real) hr).P i j := by
  have hrow : (moranKernel n r).getD i #[] = Drift.moranTransition n r i := by
    simp [moranKernel, Array.getD, i.isLt, List.getElem_toArray,
      List.getElem_map, List.getElem_range]
  rw [hrow]
  exact Drift.moranTransition_getD_eq n r hr i j

theorem checkWfReport_kernel_eq (n : Nat) (hn : 0 < n) (kernel : Array (Array Rat))
    (table : Array Rat) (ht : checkWfReport n kernel table = true)
    (i j : Fin (n + 1)) :
    (((kernel.getD i #[]).getD j 0 : Rat) : Real) = (wfChain n).P i j := by
  rw [((checkWfReport_iff n hn kernel table).1 ht).1]
  exact wfKernel_getD_eq n i j

theorem checkMoranReport_kernel_eq (n : Nat) (hn : 0 < n) (r : Rat)
    (hr : 0 < (r : Real)) (kernel : Array (Array Rat)) (table : Array Rat)
    (ht : checkMoranReport n r kernel table = true) (i j : Fin (n + 1)) :
    (((kernel.getD i #[]).getD j 0 : Rat) : Real) =
      (moranChain n (r : Real) hr).P i j := by
  rw [((checkMoranReport_iff n hn r hr kernel table).1 ht).1]
  exact moranKernel_getD_eq n r hr i j

end Rhone.Computation.Absorption
