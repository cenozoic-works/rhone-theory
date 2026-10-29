/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.Recursion.Block

/-! # The two within-block moves preserve the marginal counts -/

@[expose] public section

namespace Rhone.MarkovChain.ClosedForms

alias mA_mergeAB := Rhone.LinearAlgebra.Recursion.Config.mA_mergeAB

alias mB_split := Rhone.LinearAlgebra.Recursion.Config.mB_split

end Rhone.MarkovChain.ClosedForms
