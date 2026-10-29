/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcSupport.SingleCutExposure
public import Rhone.Coalescent.SmcSupport.StateSupport

/-!
# Successor reachability gives the single-cut carrier exposure decomposition

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
@[expose] public section
namespace Rhone.Coalescent.SmcSupport
open IntervalProcess
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem one_split_tagged (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    {s : State} (hs : OneSplitReachable x s) :
    AllMaterials (fun a => ∃ u, Tagged x a u) s := by
  induction hs with
  | clock hs t ih => exact ih
  | @split s hs i =>
    have hf := zeroSplit_full hs
    obtain ⟨hl, hr⟩ := first_split_atoms _ (hf i) x hx0 hx1
    apply splitSuccessor_all (fun a => ∃ u, Tagged x a u) s
      (fun j => ⟨.full, Tagged.full _ (hf j)⟩) i x
    · exact ⟨.left, Tagged.left _ hl⟩
    · exact ⟨.right, Tagged.right _ hr⟩
  | coal hs i j ih =>
    apply coalSuccessor_all (fun a => ∃ u, Tagged x a u) _ ih _ i j
    rintro a b ⟨u, hu⟩ ⟨v, hv⟩
    exact ⟨_, Tagged.merge hu hv⟩

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem one_split_total_hull_span_carriers (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    {s : State} (hs : OneSplitReachable x s) :
    totalHullSpan s = x * (∑ i, if materialContains (s.2.2.2 i).2 0 then 1 else 0) +
      (1 - x) * (∑ i, if materialContains (s.2.2.2 i).2 x then 1 else 0) := by
  classical
  have htag := one_split_tagged x hx0 hx1 hs
  choose u hu using htag
  exact total_hull_span_carriers x hx0 hx1 s u hu

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem pre_second_hull_exposure_carriers {n : ℕ} (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    (s : Fin n → State) (δ : Fin n → ℝ)
    (hs : ∀ j, ZeroSplitReachable (s j) ∨ OneSplitReachable x (s j)) :
    argHullExposure s δ =
      x * (∑ j, (∑ i, if materialContains ((s j).2.2.2 i).2 0 then 1 else 0) * δ j) +
      (1 - x) * (∑ j, (∑ i, if materialContains ((s j).2.2.2 i).2 x then 1 else 0) * δ j) := by
  classical
  have htag : ∀ j i, ∃ u, Tagged x ((s j).2.2.2 i).2 u := by
    intro j
    rcases hs j with hz | ho
    · intro i
      exact ⟨.full, Tagged.full _ (zeroSplit_full hz i)⟩
    · exact one_split_tagged x hx0 hx1 ho
  choose u hu using htag
  exact arg_hull_exposure_carriers x hx0 hx1 s δ u hu

end Rhone.Coalescent.SmcSupport
