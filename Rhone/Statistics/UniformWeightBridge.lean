/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Dynamics.HaploidSelection
public import Rhone.Statistics.Price

/-! # Uniform weights and finite-population moments -/

@[expose] public section

namespace Rhone.Statistics

variable {ι : Type*} [Fintype ι] {F : Type*} [Field F]

theorem wMean_uniform_eq_popMean (f : ι → F) :
    Rhone.Dynamics.wMean (fun _ => 1 / (Fintype.card ι : F)) f = popMean f := by
  unfold Rhone.Dynamics.wMean popMean
  rw [← Finset.mul_sum, one_div, div_eq_mul_inv]
  exact mul_comm ((Fintype.card ι : F)⁻¹) (∑ i, f i)

theorem wCov_uniform_eq_popCov (f g : ι → F) :
    Rhone.Dynamics.wCov (fun _ => 1 / (Fintype.card ι : F)) f g = popCov f g := by
  simp only [Rhone.Dynamics.wCov, popCov, wMean_uniform_eq_popMean]

end Rhone.Statistics
