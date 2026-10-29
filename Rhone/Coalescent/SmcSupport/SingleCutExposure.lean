/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.FiniteIntervalGenealogyMaterial
public import Rhone.Coalescent.SmcSupport.StateSpanControl
public import Rhone.Coalescent.SmcSupport.ARGClockProduct
public import Mathlib.Tactic

/-!
# Material carrier decomposition at one genomic cut

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/
@[expose] public section
namespace Rhone.Coalescent.SmcSupport
open IntervalProcess
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem tagged_contains (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    {a : Material} {u : Rhone.Coalescent.SmcSpan.Span} (h : Tagged x a u) (q : ℝ) :
    materialContains a q ↔ Rhone.Coalescent.SmcSpan.lo x u ≤ q ∧
      q < Rhone.Coalescent.SmcSpan.hi x u := by
  induction h with
  | full a ha => simp [FullAtoms] at ha; simp [materialContains, ha,
      Rhone.Coalescent.SmcSpan.lo, Rhone.Coalescent.SmcSpan.hi]
  | left a ha => simp [materialContains, ha,
      Rhone.Coalescent.SmcSpan.lo, Rhone.Coalescent.SmcSpan.hi]
  | right a ha => simp [materialContains, ha,
      Rhone.Coalescent.SmcSpan.lo, Rhone.Coalescent.SmcSpan.hi]
  | @merge a b u v ha hb iha ihb =>
    rw [materialContains_merge, iha, ihb]
    cases u <;> cases v <;>
      simp only [Rhone.Coalescent.SmcSpan.lo, Rhone.Coalescent.SmcSpan.hi,
        Rhone.Coalescent.SmcSpan.merge] <;> grind

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem tagged_hull_length_carriers (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    {a : Material} {u : Rhone.Coalescent.SmcSpan.Span} (h : Tagged x a u) :
    hullLength a = x * (if materialContains a 0 then 1 else 0) +
      (1 - x) * (if materialContains a x then 1 else 0) := by
  classical
  obtain ⟨hlo, hhi⟩ := tagged_hull x hx0 hx1 h
  rw [hullLength, hlo, hhi]
  simp only [tagged_contains x hx0 hx1 h]
  cases u <;> simp [Rhone.Coalescent.SmcSpan.lo, Rhone.Coalescent.SmcSpan.hi,
    hx0, hx0.le, hx1, sub_nonneg.mpr hx1.le]

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem total_hull_span_carriers (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    (s : State) (u : Fin s.2.2.1 → Rhone.Coalescent.SmcSpan.Span)
    (h : ∀ i, Tagged x (s.2.2.2 i).2 (u i)) :
    totalHullSpan s = x * (∑ i, if materialContains (s.2.2.2 i).2 0 then 1 else 0) +
      (1 - x) * (∑ i, if materialContains (s.2.2.2 i).2 x then 1 else 0) := by
  classical
  simp only [totalHullSpan, tagged_hull_length_carriers x hx0 hx1 (h _),
    Finset.sum_add_distrib, ← Finset.mul_sum]

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem arg_hull_exposure_carriers {n : ℕ} (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    (s : Fin n → State) (δ : Fin n → ℝ)
    (u : (j : Fin n) → Fin (s j).2.2.1 → Rhone.Coalescent.SmcSpan.Span)
    (h : ∀ j i, Tagged x ((s j).2.2.2 i).2 (u j i)) :
    argHullExposure s δ =
      x * (∑ j, (∑ i, if materialContains ((s j).2.2.2 i).2 0 then 1 else 0) * δ j) +
      (1 - x) * (∑ j, (∑ i, if materialContains ((s j).2.2.2 i).2 x then 1 else 0) * δ j) := by
  classical
  unfold argHullExposure
  simp only [tagged_hull_length_carriers x hx0 hx1 (h _ _), Finset.sum_add_distrib,
    ← Finset.mul_sum, add_mul, mul_assoc]

end Rhone.Coalescent.SmcSupport
