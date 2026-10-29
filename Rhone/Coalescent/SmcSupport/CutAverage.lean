/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcSupport.ConcretePrefix
public import Rhone.Coalescent.FiniteIntervalMaterialMarked

/-! # Averaging the first-daughter loss recursion over the uniform cut -/
@[expose] public section
namespace Rhone.Coalescent.SmcSupport
open IntervalProcess SmcBound MeasureTheory
open scoped ENNReal

noncomputable def firstCutLoss (R : ℝ) (n : ℕ) (s : CountState n)
    (hs : ZeroSplitReachable s.val) (i : Fin s.val.2.2.1) (x : ℝ) : ℝ≥0∞ :=
  if hx : 0 < x ∧ x < 1 then
    ENNReal.ofReal (coalPrefixFailure R (n + 1)
      (firstSplitNext n s hs i x hx.1 hx.2))
  else 0

theorem firstCutLoss_le (R : ℝ) (hR : 0 ≤ R) (n : ℕ)
    (s : CountState n) (hs : ZeroSplitReachable s.val)
    (i : Fin s.val.2.2.1) (x : ℝ) :
    firstCutLoss R n s hs i x ≤ ENNReal.ofReal (raceBound (hazard R) (n + 1)) := by
  unfold firstCutLoss
  split_ifs with hx
  · exact ENNReal.ofReal_le_ofReal (firstSplit_prefixFailure_le R hR n s hs i x hx.1 hx.2)
  · exact bot_le

theorem firstCutLoss_integral_le (R : ℝ) (hR : 0 ≤ R) (n : ℕ)
    (s : CountState n) (hs : ZeroSplitReachable s.val)
    (i : Fin s.val.2.2.1) :
    (∫⁻ x, firstCutLoss R n s hs i x ∂unitUniform) ≤
      ENNReal.ofReal (raceBound (hazard R) (n + 1)) := by
  calc
    _ ≤ ∫⁻ _x, ENNReal.ofReal (raceBound (hazard R) (n + 1)) ∂unitUniform :=
      lintegral_mono (firstCutLoss_le R hR n s hs i)
    _ = _ := by simp

end Rhone.Coalescent.SmcSupport
