/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanShapeFibreAssemblyRecovery
public import Rhone.Coalescent.KingmanShapeRootFibreInverse
/-!
# Ranked root-fibre inverse identities from chronological daughter recovery

Source: andre1881, §II no. 6, pp. 170–171. -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
/-- Source: andre1881, §II no. 6, pp. 170–171. -/
theorem rankedShapeRootFibreMap_right_inverse (n : ℕ) (hn : 3 ≤ n)
    (k : {k : ℕ // k ∈ Ico 2 n}) :
    Function.RightInverse (rankedShapeRootFibreInverse n hn k)
      (rankedShapeRootFibreMap n hn k) := by
  intro p
  rcases p with ⟨⟨x, y⟩, s⟩
  rw [rankedShapeRootFibreMap_representative n hn k _
    (firstRootHistoryAssemble n hn k x.out y.out s)
    (firstMergerRoot_card_firstRootHistoryAssemble n hn k x.out y.out s) rfl,
    rootHistoryFibreData_assembly]
  exact Prod.ext (Prod.ext (Quotient.out_eq x) (Quotient.out_eq y)) rfl
end Rhone.Coalescent
