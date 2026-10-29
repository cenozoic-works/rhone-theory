/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.FullPanLaw

/-! # `C¹` gluing at a single time boundary -/

@[expose] public section

open Set Filter
open scoped Topology
namespace Rhone.Statistics.Identifiability

noncomputable def joinAt (b : ℝ) (f g : ℝ → ℝ) (t : ℝ) : ℝ :=
  if t ≤ b then f t else g t

theorem joinAt_continuous (b : ℝ) (f g : ℝ → ℝ)
    (hf : Continuous f) (hg : Continuous g) (he : f b = g b) : Continuous (joinAt b f g) := by
  apply Continuous.if_le hf hg continuous_id continuous_const
  intro x hx
  change x = b at hx
  simpa only [hx] using he

theorem joinAt_hasDerivAt_left (b : ℝ) (f g : ℝ → ℝ) {t a : ℝ}
    (ht : t < b) (hf : HasDerivAt f a t) : HasDerivAt (joinAt b f g) a t := by
  apply hf.congr_of_eventuallyEq
  filter_upwards [isOpen_Iio.mem_nhds ht] with x hx
  exact ite_eq_left (le_of_lt hx)

theorem joinAt_hasDerivAt_right (b : ℝ) (f g : ℝ → ℝ) {t a : ℝ}
    (ht : b < t) (hg : HasDerivAt g a t) : HasDerivAt (joinAt b f g) a t := by
  apply hg.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx
  exact ite_eq_right (not_le_of_gt hx)

theorem joinAt_hasDerivAt_boundary (b : ℝ) (f g : ℝ → ℝ) (a : ℝ)
    (he : f b = g b) (hf : HasDerivAt f a b) (hg : HasDerivAt g a b) :
    HasDerivAt (joinAt b f g) a b := by
  have hl : HasDerivWithinAt (joinAt b f g) a (Iic b) b := by
    apply hf.hasDerivWithinAt.congr
    · intro x hx
      exact ite_eq_left hx
    · exact ite_eq_left le_rfl
  have hr : HasDerivWithinAt (joinAt b f g) a (Ici b) b := by
    apply hg.hasDerivWithinAt.congr
    · intro x hx
      by_cases hxb : x ≤ b
      · have hx' : x = b := le_antisymm hxb hx
        subst x
        simpa [joinAt] using he
      · exact ite_eq_right hxb
    · simpa [joinAt] using he
  have hu := hl.union hr
  simpa only [Iic_union_Ici,hasDerivWithinAt_univ] using hu

theorem joinAt_derivative (b : ℝ) (f g df dg : ℝ → ℝ)
    (hf : ∀ t, HasDerivAt f (df t) t) (hg : ∀ t, HasDerivAt g (dg t) t)
    (he : f b = g b) (hd : df b = dg b) (t : ℝ) :
    HasDerivAt (joinAt b f g) (joinAt b df dg t) t := by
  rcases lt_trichotomy t b with ht | ht | ht
  · simpa only [joinAt,ite_eq_left ht.le] using joinAt_hasDerivAt_left b f g ht (hf t)
  · subst t
    have hh := joinAt_hasDerivAt_boundary b f g (df b) he (hf b)
      (by simpa only [hd] using hg b)
    simpa only [joinAt,ite_eq_left le_rfl] using hh
  · simpa only [joinAt,ite_eq_right (not_le_of_gt ht)] using joinAt_hasDerivAt_right b f g ht (hg t)

end Rhone.Statistics.Identifiability
