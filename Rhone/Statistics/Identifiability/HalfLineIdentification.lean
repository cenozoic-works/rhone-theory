/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.FullPanLaw

/-! # Continuous values and derivatives identified from positive-time observations -/

@[expose] public section

open Set Filter
open scoped Topology
namespace Rhone.Statistics.Identifiability

theorem eqOn_closed_halfline {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (he : EqOn f g (Ioi 0)) : EqOn f g (Ici 0) := by
  simpa only [closure_Ioi] using he.closure hf hg

theorem eqOn_halfline_derivatives {f g f' g' : ℝ → ℝ}
    (hf' : Continuous f') (hg' : Continuous g')
    (hfd : ∀ t, 0 ≤ t → HasDerivAt f (f' t) t)
    (hgd : ∀ t, 0 ≤ t → HasDerivAt g (g' t) t)
    (he : EqOn f g (Ioi 0)) : EqOn f' g' (Ici 0) := by
  apply eqOn_closed_halfline hf' hg'
  intro t ht
  have hl : g =ᶠ[𝓝 t] f := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx
    exact (he hx).symm
  exact ((hfd t ht.le).congr_of_eventuallyEq hl).unique (hgd t ht.le)

theorem rate_nonneg_of_positive_time (rate : ℝ → ℝ) (hr : Continuous rate)
    (hp : ∀ t, 0 < t → 0 < rate t) : ∀ t, 0 ≤ t → 0 ≤ rate t := by
  have hs : Ioi (0 : ℝ) ⊆ {t | 0 ≤ rate t} := fun t ht => (hp t ht).le
  have hc := closure_minimal hs (isClosed_le continuous_const hr)
  rw [closure_Ioi] at hc
  exact fun t ht => hc ht

end Rhone.Statistics.Identifiability
