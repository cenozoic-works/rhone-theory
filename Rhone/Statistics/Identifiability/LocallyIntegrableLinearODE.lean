/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.VolterraL1Bounds
public import Rhone.Statistics.Identifiability.VolterraSeriesSolution

/-! # Global linear ODEs with locally Bochner-integrable coefficients -/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology Nat

namespace Rhone.Statistics.Identifiability.LocallyIntegrableLinearODE
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {A : ℝ → E →L[ℝ] E}

theorem solution_tendstoUniformlyOn (hA : LocallyIntegrable A volume) (x : E) (a b : ℝ) :
    TendstoUniformlyOn
      (fun F : Finset ℕ => fun t => ∑ n ∈ F, PeanoBaker.term A x n t)
      (PeanoBaker.solution A x) atTop (uIcc a b) := by
  obtain ⟨u, hu, hub⟩ := LocallyIntegrablePeanoBaker.exists_summable_compact_bound hA x a b
  exact tendstoUniformlyOn_tsum hu hub

theorem solution_zero (hA : LocallyIntegrable A volume) (x : E) :
    PeanoBaker.solution A x 0 = x :=
  VolterraSeriesSolution.solution_zero
    (LocallyIntegrablePeanoBaker.exists_summable_compact_bound hA x)

theorem solution_continuous (hA : LocallyIntegrable A volume) (x : E) :
    Continuous (PeanoBaker.solution A x) :=
  VolterraSeriesSolution.solution_continuous hA
    (LocallyIntegrablePeanoBaker.exists_summable_compact_bound hA x)

theorem solution_integral_eq (hA : LocallyIntegrable A volume) (x : E) (t : ℝ) :
    PeanoBaker.solution A x t = x + ∫ s in (0 : ℝ)..t, A s (PeanoBaker.solution A x s) :=
  VolterraSeriesSolution.solution_integral_eq hA
    (LocallyIntegrablePeanoBaker.exists_summable_compact_bound hA x) t

theorem solution_ae_hasDerivAt (hA : LocallyIntegrable A volume) (x : E) :
    ∀ᵐ t, HasDerivAt (PeanoBaker.solution A x) (A t (PeanoBaker.solution A x t)) t :=
  VolterraSeriesSolution.solution_ae_hasDerivAt hA
    (LocallyIntegrablePeanoBaker.exists_summable_compact_bound hA x)

theorem solution_absolutelyContinuousOnInterval (hA : LocallyIntegrable A volume)
    (x : E) (a b : ℝ) : AbsolutelyContinuousOnInterval (PeanoBaker.solution A x) a b :=
  VolterraSeriesSolution.solution_absolutelyContinuousOnInterval hA
    (LocallyIntegrablePeanoBaker.exists_summable_compact_bound hA x) a b

theorem exists_global_solution (A : ℝ → E →L[ℝ] E)
    (hA : LocallyIntegrable A volume) (x : E) :
    ∃ X : ℝ → E, X 0 = x ∧ Continuous X ∧
      (∀ a b, AbsolutelyContinuousOnInterval X a b) ∧
      (∀ t, X t = x + ∫ s in (0 : ℝ)..t, A s (X s)) ∧
      ∀ᵐ t, HasDerivAt X (A t (X t)) t :=
  ⟨PeanoBaker.solution A x, solution_zero hA x, solution_continuous hA x,
    solution_absolutelyContinuousOnInterval hA x, solution_integral_eq hA x,
    solution_ae_hasDerivAt hA x⟩

end Rhone.Statistics.Identifiability.LocallyIntegrableLinearODE
