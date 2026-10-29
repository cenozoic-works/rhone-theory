/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Affine.Convex
public import Mathlib.Analysis.Normed.Operator.NNNorm
public import Mathlib.Tactic

/-! # Stable finite convex representations -/

@[expose] public section

open Set Filter
open scoped Topology BigOperators

namespace Rhone.Algebra.FinitePanelGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_pos_half_norm_lt_apply (f : E →L[ℝ] ℝ) (hf : f ≠ 0) :
    ∃ y : E, ‖y‖ < 1 ∧ ‖f‖ / 2 < f y := by
  have hn : 0 < ‖f‖ := norm_pos_iff.mpr hf
  obtain ⟨y, hy, hfy⟩ := f.exists_lt_apply_of_lt_opNorm (by linarith : ‖f‖ / 2 < ‖f‖)
  by_cases h : 0 ≤ f y
  · exact ⟨y, hy, by simpa only [Real.norm_eq_abs, abs_of_nonneg h] using hfy⟩
  · refine ⟨-y, by simpa using hy, ?_⟩
    simpa only [map_neg, Real.norm_eq_abs, abs_of_neg (lt_of_not_ge h)] using hfy

theorem ball_subset_convexHull_of_vertex_perturbation {ι : Type*} [Finite ι]
    (p q : ι → E) (m : E) {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball m r ⊆ convexHull ℝ (range p))
    (hclose : ∀ i, ‖q i - p i‖ ≤ r / 4) :
    Metric.ball m (r / 4) ⊆ convexHull ℝ (range q) := by
  classical
  have hm : m ∈ convexHull ℝ (range p) := hball (Metric.mem_ball_self hr)
  obtain ⟨_, ⟨i, rfl⟩⟩ := convexHull_nonempty_iff.mp ⟨m, hm⟩
  intro x hx
  by_contra hout
  obtain ⟨f, a, hsep, hax⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ (range q)) ((finite_range q).isClosed_convexHull ℝ) hout
  have hf : f ≠ 0 := by
    intro hzero
    have hi := hsep (q i) (subset_convexHull ℝ (range q) (mem_range_self i))
    simp only [hzero, zero_apply] at hi hax
    linarith
  have hn : 0 < ‖f‖ := norm_pos_iff.mpr hf
  have hp : ∀ j, f (p j) ≤ f x + ‖f‖ * (r / 4) := by
    intro j
    have hj := (hsep (q j) (subset_convexHull ℝ (range q) (mem_range_self j))).trans hax
    have he : f (p j) - f (q j) ≤ ‖f‖ * (r / 4) := by
      calc
        f (p j) - f (q j) = f (p j - q j) := (map_sub f _ _).symm
        _ ≤ ‖f (p j - q j)‖ := le_abs_self _
        _ ≤ ‖f‖ * ‖p j - q j‖ := f.le_opNorm _
        _ ≤ ‖f‖ * (r / 4) := by
          gcongr
          simpa only [norm_sub_rev] using hclose j
    linarith
  have hh : convexHull ℝ (range p) ⊆ {z | f z ≤ f x + ‖f‖ * (r / 4)} := by
    apply convexHull_min
    · rintro _ ⟨j, rfl⟩
      exact hp j
    · exact convex_halfSpace_le f.toLinearMap.isLinear _
  obtain ⟨y, hy, hfy⟩ := exists_pos_half_norm_lt_apply f hf
  have hz : m + r • y ∈ Metric.ball m r := by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos hr]
    nlinarith
  have hbound := hh (hball hz)
  change f (m + r • y) ≤ f x + ‖f‖ * (r / 4) at hbound
  rw [map_add, map_smul, smul_eq_mul] at hbound
  have hxm : f x - f m < ‖f‖ * (r / 4) := by
    calc
      f x - f m = f (x - m) := (map_sub f _ _).symm
      _ ≤ ‖f (x - m)‖ := le_abs_self _
      _ ≤ ‖f‖ * ‖x - m‖ := f.le_opNorm _
      _ < ‖f‖ * (r / 4) := by
        apply mul_lt_mul_of_pos_left _ hn
        simpa only [Metric.mem_ball, dist_eq_norm] using hx
  nlinarith

theorem finite_polytope_interior_stable {ι : Type*} [Finite ι]
    (p : ι → E) {m : E} (hm : m ∈ interior (convexHull ℝ (range p))) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ q : ι → E, (∀ i, ‖q i - p i‖ ≤ ε) →
      m ∈ interior (convexHull ℝ (range q)) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hm)
  refine ⟨r / 4, by positivity, fun q hq => ?_⟩
  exact mem_interior_iff_mem_nhds.mpr (Metric.mem_nhds_iff.mpr
    ⟨r / 4, by positivity, ball_subset_convexHull_of_vertex_perturbation p q m hr hball hq⟩)

theorem eventually_mem_interior_convexHull {ι κ : Type*} [Finite ι]
    {l : Filter κ} (p : ι → E) (q : κ → ι → E) {m : E}
    (hm : m ∈ interior (convexHull ℝ (range p)))
    (hq : ∀ i, Tendsto (fun n => q n i) l (𝓝 (p i))) :
    ∀ᶠ n in l, m ∈ interior (convexHull ℝ (range (q n))) := by
  obtain ⟨ε, hε, hstable⟩ := finite_polytope_interior_stable p hm
  have he : ∀ i, ∀ᶠ n in l, ‖q n i - p i‖ < ε := by
    intro i
    have ht := (hq i).sub (tendsto_const_nhds (x := p i))
    have hn : Tendsto (fun n => ‖q n i - p i‖) l (𝓝 0) := by
      simpa only [sub_self, norm_zero] using ht.norm
    exact hn.eventually (eventually_lt_nhds hε)
  filter_upwards [Filter.eventually_all.mpr he] with n hn
  exact hstable (q n) (fun i => (hn i).le)

theorem exists_finite_inscribed_polytope [FiniteDimensional ℝ E]
    {s : Set E} {m : E} (hm : m ∈ interior (convexHull ℝ s)) :
    ∃ t : Finset E, (↑t : Set E) ⊆ s ∧ m ∈ interior (convexHull ℝ (↑t : Set E)) := by
  classical
  obtain ⟨b, hbm, hbs⟩ := exists_mem_interior_convexHull_affineBasis
    (mem_interior_iff_mem_nhds.mp hm)
  have hb : ∀ i, ∃ t : Finset E, (↑t : Set E) ⊆ s ∧ b i ∈ convexHull ℝ (↑t : Set E) := by
    intro i
    have hi := hbs (subset_convexHull ℝ (range b) (mem_range_self i))
    simpa only [convexHull_eq_union_convexHull_finite_subsets s, mem_iUnion,
      exists_prop] using hi
  choose t hts hbt using hb
  let u : Finset E := Finset.univ.biUnion t
  have htu : ∀ i, (↑(t i) : Set E) ⊆ (↑u : Set E) := by
    intro i x hx
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩
  refine ⟨u, ?_, interior_mono ?_ hbm⟩
  · intro x hx
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
    exact hts i hi
  · apply convexHull_min
    · rintro _ ⟨i, rfl⟩
      exact convexHull_mono (htu i) (hbt i)
    · exact convex_convexHull ℝ _

theorem exists_positive_small_convex_combination [FiniteDimensional ℝ E]
    {s : Set E} {m : E} (hm : m ∈ convexHull ℝ s) :
    ∃ (t : Finset E) (w : E → ℝ), (↑t : Set E) ⊆ s ∧ t.Nonempty ∧
      t.card ≤ Module.finrank ℝ E + 1 ∧ (∀ y ∈ t, 0 < w y) ∧
      ∑ y ∈ t, w y = 1 ∧ ∑ y ∈ t, w y • y = m := by
  classical
  rw [convexHull_eq_union] at hm
  simp only [mem_iUnion, exists_prop] at hm
  obtain ⟨t, ht, ha, hm⟩ := hm
  obtain ⟨w, hw, hws, hwm⟩ := Finset.mem_convexHull'.mp hm
  let u := t.filter (fun y => w y ≠ 0)
  have hsub : u ⊆ t := Finset.filter_subset _ _
  have hus : ∑ y ∈ u, w y = 1 := by
    simpa only [u, Finset.sum_filter_ne_zero] using hws
  refine ⟨u, w, fun _ hy => ht (hsub hy), ?_, ?_, ?_, hus, ?_⟩
  · by_contra h
    have he : u = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp only [he, Finset.sum_empty] at hus
    norm_num at hus
  · calc
      u.card ≤ t.card := Finset.card_le_card hsub
      _ ≤ Module.finrank ℝ (vectorSpan ℝ (range ((↑) : t → E))) + 1 := by
        simpa only [Fintype.card_coe] using ha.card_le_finrank_succ
      _ ≤ Module.finrank ℝ E + 1 := Nat.add_le_add_right (Submodule.finrank_le _) 1
  · intro y hy
    have hy' := Finset.mem_filter.mp hy
    exact (hw y hy'.1).lt_of_ne hy'.2.symm
  · change (∑ y ∈ t.filter (fun y => w y ≠ 0), w y • y) = m
    rw [Finset.sum_filter_of_ne]
    · exact hwm
    · intro y _ hy hzero
      exact hy (by simp only [hzero, zero_smul])

theorem eventually_exists_positive_convex_combination [FiniteDimensional ℝ E]
    {ι : Type*} [Finite ι] (p : ι → E) (q : ℕ → ι → E) {m : E}
    (hm : m ∈ interior (convexHull ℝ (range p)))
    (hq : ∀ i, Tendsto (fun n => q n i) atTop (𝓝 (p i))) :
    ∀ᶠ n in atTop, ∃ (t : Finset E) (w : E → ℝ), (↑t : Set E) ⊆ range (q n) ∧
      t.Nonempty ∧ t.card ≤ Module.finrank ℝ E + 1 ∧ (∀ y ∈ t, 0 < w y) ∧
      ∑ y ∈ t, w y = 1 ∧ ∑ y ∈ t, w y • y = m := by
  filter_upwards [eventually_mem_interior_convexHull p q hm hq] with n hn
  exact exists_positive_small_convex_combination (interior_subset hn)

theorem curve_eventually_exists_positive_exact_match [FiniteDimensional ℝ E]
    {α : Type*} (p : α → E) (q : ℕ → α → E) {m : E}
    (hm : m ∈ interior (convexHull ℝ (range p)))
    (hq : ∀ x, Tendsto (fun n => q n x) atTop (𝓝 (p x))) :
    ∀ᶠ n in atTop, ∃ (t : Finset E) (w : E → ℝ), (↑t : Set E) ⊆ range (q n) ∧
      t.Nonempty ∧ t.card ≤ Module.finrank ℝ E + 1 ∧ (∀ y ∈ t, 0 < w y) ∧
      ∑ y ∈ t, w y = 1 ∧ ∑ y ∈ t, w y • y = m := by
  classical
  obtain ⟨t, ht, htm⟩ := exists_finite_inscribed_polytope hm
  have hrep : ∀ y : t, ∃ x : α, p x = (y : E) := fun y => ht y.property
  choose a ha using hrep
  have hrange : range (fun y : t => p (a y)) = (↑t : Set E) := by
    simp only [ha, Subtype.range_coe_subtype]
    rfl
  have hp : m ∈ interior (convexHull ℝ (range (fun y : t => p (a y)))) := by
    rwa [hrange]
  filter_upwards [eventually_exists_positive_convex_combination
    (fun y : t => p (a y)) (fun n y => q n (a y)) hp (fun y => hq (a y))] with n hn
  obtain ⟨u, w, hu, hne, hcard, hpos, hsum, heq⟩ := hn
  refine ⟨u, w, ?_, hne, hcard, hpos, hsum, heq⟩
  intro y hy
  obtain ⟨z, rfl⟩ := hu hy
  exact mem_range_self (a z)

end Rhone.Algebra.FinitePanelGeometry
