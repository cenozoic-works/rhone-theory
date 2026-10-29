/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.KilledSystem.Recursion

/-! # Exact scalar cancellation -/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Rhone.Algebra.KilledSystem

theorem unique_scalar_zero {F : Type*} [Field F] {A x : F}
    (hA : A ≠ 0) (h : A * x = 0) : x = 0 :=
  (mul_eq_zero.mp h).resolve_left hA

end Rhone.Algebra.KilledSystem
