/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.Tridiag.Defs
public import Rhone.Algebra.SymbolicFrequencies.NoFormula

/-! # The obstruction at symbolic `π` is the block generator's determinant -/
set_option linter.style.longLine false

@[expose] public section

namespace Rhone.Algebra.SymbolicFrequencies

open Polynomial

noncomputable def thAP : GenericField.P Kpi := C ((GenericField.uu Kpi + GenericField.vv Kpi) / 2)

noncomputable def thBP : GenericField.P Kpi := C ((GenericField.uu Kpi - GenericField.vv Kpi) / 2)

theorem thAP_add_thBP : thAP + thBP = C (GenericField.uu Kpi) := by
  rw [thAP, thBP, ← map_add]
  congr 1
  ring

theorem thAP_mul_two_add_thBP_mul_two : thAP * 2 + thBP * 2 = C (2 * GenericField.uu Kpi) := by
  rw [map_mul, map_ofNat]
  linear_combination 2 * thAP_add_thBP

noncomputable def T22π : Matrix (Fin 3) (Fin 3) (GenericField.P Kpi) :=
  !![C (2 * GenericField.uu Kpi) + 12, -8, 0;
     -X, C (2 * GenericField.uu Kpi) + 6 + X, -2;
     0, -2 * X, C (2 * GenericField.uu Kpi) + 2 + 2 * X]

theorem T_two_two_pi : LinearAlgebra.Tridiag.T (GenericField.P Kpi) 2 2 thAP thBP X = T22π := by
  have h := thAP_mul_two_add_thBP_mul_two
  rw [LinearAlgebra.Tridiag.T_two_two_generic, T22π,
    show (12 : GenericField.P Kpi) + thAP * 2 + thBP * 2 = C (2 * GenericField.uu Kpi) + 12 from by
      linear_combination h,
    show (6 : GenericField.P Kpi) + thAP * 2 + thBP * 2 + X = C (2 * GenericField.uu Kpi) + 6 + X
        from by
      linear_combination h,
    show (2 : GenericField.P Kpi) + thAP * 2 + thBP * 2 + X * 2 = C (2 * GenericField.uu Kpi) + 2 +
        2 * X from by
      linear_combination h,
    show -(X * 2) = -2 * (X : GenericField.P Kpi) from by ring]

theorem T22π_det : T22π.det = 4 * GenericField.E22 Kpi := by
  simp [T22π, Matrix.det_fin_three, GenericField.E22, GenericField.E22a, GenericField.E22b,
      GenericField.E22c, map_add, map_mul,
    map_ofNat]
  ring

theorem E_two_two_pi : LinearAlgebra.Tridiag.E (GenericField.P Kpi) 2 2 thAP thBP X = 4 *
    GenericField.E22 Kpi := by
  rw [LinearAlgebra.Tridiag.E, T_two_two_pi, T22π_det]

theorem E_two_two_pi_ne_zero : LinearAlgebra.Tridiag.E (GenericField.P Kpi) 2 2 thAP thBP X ≠ 0 :=
    by
  rw [E_two_two_pi]
  exact mul_ne_zero (by norm_num) (GenericField.E22_ne_zero Kpi)

theorem E_two_two_pi_dvd_q22π_denom :
    LinearAlgebra.Tridiag.E (GenericField.P Kpi) 2 2 thAP thBP X ∣ q22π.denom := by
  obtain ⟨w, hw⟩ := E22_dvd_q22π_denom
  have h4 : (4 : GenericField.P Kpi) * C (4 : GenericField.Fuv Kpi)⁻¹ = 1 := by
    rw [show (4 : GenericField.P Kpi) = C (4 : GenericField.Fuv Kpi) from (map_ofNat _ 4).symm, ←
        map_mul,
      mul_inv_cancel₀ (by norm_num : (4 : GenericField.Fuv Kpi) ≠ 0), map_one]
  refine ⟨C (4 : GenericField.Fuv Kpi)⁻¹ * w, ?_⟩
  rw [E_two_two_pi, hw]
  calc GenericField.E22 Kpi * w = (4 * C (4 : GenericField.Fuv Kpi)⁻¹) * (GenericField.E22 Kpi * w) := by
        rw [h4, one_mul]
    _ = 4 * GenericField.E22 Kpi * (C (4 : GenericField.Fuv Kpi)⁻¹ * w) := by ring

end Rhone.Algebra.SymbolicFrequencies
