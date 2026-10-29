/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.Price

/-!
# Executable Robertson-Price identity

Source: robertson1966, p. 97, eq. (4), p. 99; frank1995_price, p. 374, eq. (1); price1970, p. 520,
eq. (1). -/

@[expose] public section
namespace Rhone.Computation.Robertson
open Price

def robertsonChange (l : List Parent) : Option Rat :=
  if mean (fun p => p.w) l = 0 then none
  else some (cov (fun p => p.w) (fun p => p.z) l / mean (fun p => p.w) l)

end Rhone.Computation.Robertson
