/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.FiniteIntervalMaterialSampler
public import Rhone.Coalescent.FiniteIntervalMaterialArrays

/-! # Measurability of the concrete finite cumulative-rate selector -/
@[expose] public section

namespace Rhone.Coalescent.IntervalProcess

theorem chooseByRate_measurable {δ α : Type*} [MeasurableSpace δ]
    [MeasurableSpace α] [MeasurableSpace (Option α)]
    (rate : α → δ → ℝ) (hr : ∀ a, Measurable (rate a)) (l : List α)
    (selector : δ → ℝ) (hs : Measurable selector) :
    Measurable (fun x => chooseByRate (fun a => rate a x) l (selector x)) := by
  induction l generalizing selector with
  | nil => exact measurable_const
  | cons a rest ih =>
    change Measurable (fun x => if selector x < rate a x then some a
      else chooseByRate (fun b => rate b x) rest (selector x - rate a x))
    exact measurable_const.piecewise (measurableSet_lt hs (hr a))
      (ih (fun x => selector x - rate a x) (hs.sub (hr a)))

end Rhone.Coalescent.IntervalProcess
