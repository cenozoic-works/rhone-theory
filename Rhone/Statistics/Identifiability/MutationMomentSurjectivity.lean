/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.OpenPartialHomeomorph.Defs
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Topology.UniformSpace.UniformConvergence
public import Mathlib.Tactic

/-! # The deterministic moment-coordinate bridge -/

@[expose] public section

open Set Metric
open scoped Topology ContDiff NNReal

namespace Rhone.Statistics.Identifiability.MutationMomentSurjectivity

def parameterDomain (L : ℝ) : Set (ℝ × ℝ) :=
  {x | 0 < x.1 ∧ x.1 < 1 ∧ 0 < x.2 ∧ x.2 < L}

def momentDomain (L : ℝ) : Set (ℝ × ℝ) :=
  {y | 0 < y.1 ∧ y.1 < L ∧ y.1 ^ 2 < y.2 ∧ y.2 < L * y.1}

def momentMap (x : ℝ × ℝ) : ℝ × ℝ := (x.1 * x.2, x.1 * x.2 ^ 2)

noncomputable def momentInverse (y : ℝ × ℝ) : ℝ × ℝ :=
  (y.1 ^ 2 / y.2, y.2 / y.1)

theorem momentMap_mem {L : ℝ} {x : ℝ × ℝ} (hx : x ∈ parameterDomain L) :
    momentMap x ∈ momentDomain L := by
  rcases hx with ⟨hw, hw1, hz, hzL⟩
  have hwz : 0 < x.1 * x.2 := mul_pos hw hz
  have hwz_z : x.1 * x.2 < x.2 := by nlinarith
  have hlow := mul_lt_mul_of_pos_left hwz_z hwz
  have hupp := mul_lt_mul_of_pos_left hzL hwz
  dsimp [momentDomain, momentMap]
  refine ⟨hwz, lt_trans hwz_z hzL, ?_, ?_⟩ <;> nlinarith

theorem moment_second_pos {L : ℝ} {y : ℝ × ℝ} (hy : y ∈ momentDomain L) :
    0 < y.2 := lt_trans (sq_pos_of_pos hy.1) hy.2.2.1

theorem momentInverse_mem {L : ℝ} {y : ℝ × ℝ} (hy : y ∈ momentDomain L) :
    momentInverse y ∈ parameterDomain L := by
  have hp := hy.1
  have hq := moment_second_pos hy
  dsimp [momentInverse, parameterDomain]
  refine ⟨div_pos (sq_pos_of_pos hp) hq, ?_, div_pos hq hp, ?_⟩
  · exact (div_lt_one hq).2 hy.2.2.1
  · exact (div_lt_iff₀ hp).2 hy.2.2.2

theorem momentMap_inverse {L : ℝ} {y : ℝ × ℝ} (hy : y ∈ momentDomain L) :
    momentMap (momentInverse y) = y := by
  have hp : y.1 ≠ 0 := ne_of_gt hy.1
  have hq : y.2 ≠ 0 := ne_of_gt (moment_second_pos hy)
  ext <;> dsimp [momentMap, momentInverse] <;> field_simp

theorem momentInverse_map {L : ℝ} {x : ℝ × ℝ} (hx : x ∈ parameterDomain L) :
    momentInverse (momentMap x) = x := by
  have hw : x.1 ≠ 0 := ne_of_gt hx.1
  have hz : x.2 ≠ 0 := ne_of_gt hx.2.2.1
  ext <;> dsimp [momentMap, momentInverse] <;> field_simp

theorem momentMap_image (L : ℝ) : momentMap '' parameterDomain L = momentDomain L := by
  apply Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact momentMap_mem hx
  · intro y hy
    exact ⟨momentInverse y, momentInverse_mem hy, momentMap_inverse hy⟩

theorem momentMap_injOn (L : ℝ) : InjOn momentMap (parameterDomain L) := by
  intro x hx x' hx' heq
  have := congrArg momentInverse heq
  simpa only [momentInverse_map hx, momentInverse_map hx'] using this

theorem parameterDomain_isOpen (L : ℝ) : IsOpen (parameterDomain L) := by
  exact (isOpen_lt continuous_const continuous_fst).inter
    ((isOpen_lt continuous_fst continuous_const).inter
      ((isOpen_lt continuous_const continuous_snd).inter
        (isOpen_lt continuous_snd continuous_const)))

theorem momentDomain_isOpen (L : ℝ) : IsOpen (momentDomain L) := by
  exact (isOpen_lt continuous_const continuous_fst).inter
    ((isOpen_lt continuous_fst continuous_const).inter
      ((isOpen_lt (continuous_fst.pow 2) continuous_snd).inter
        (isOpen_lt continuous_snd (continuous_const.mul continuous_fst))))

theorem momentMap_contDiff : ContDiff ℝ ∞ momentMap := by
  unfold momentMap
  fun_prop

theorem momentInverse_contDiffOn (L : ℝ) :
    ContDiffOn ℝ ∞ momentInverse (momentDomain L) := by
  apply ContDiffOn.prodMk
  · exact (contDiff_fst.pow 2).contDiffOn.div contDiff_snd.contDiffOn
      (fun y hy => ne_of_gt (moment_second_pos hy))
  · exact contDiff_snd.contDiffOn.div contDiff_fst.contDiffOn
      (fun y hy => ne_of_gt hy.1)

theorem momentMap_diffeomorphism_data (L : ℝ) :
    BijOn momentMap (parameterDomain L) (momentDomain L) ∧
    ContDiffOn ℝ ∞ momentMap (parameterDomain L) ∧
    ContDiffOn ℝ ∞ momentInverse (momentDomain L) ∧
    LeftInvOn momentInverse momentMap (parameterDomain L) ∧
    RightInvOn momentInverse momentMap (momentDomain L) := by
  refine ⟨⟨fun x hx => momentMap_mem hx, momentMap_injOn L, ?_⟩,
    momentMap_contDiff.contDiffOn, momentInverse_contDiffOn L,
    fun x hx => momentInverse_map hx, fun y hy => momentMap_inverse hy⟩
  intro y hy
  exact ⟨momentInverse y, momentInverse_mem hy, momentMap_inverse hy⟩

noncomputable def momentOpenPartialHomeomorph (L : ℝ) :
    OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) where
  toFun := momentMap
  invFun := momentInverse
  source := parameterDomain L
  target := momentDomain L
  map_source' := fun _ hx => momentMap_mem hx
  map_target' := fun _ hx => momentInverse_mem hx
  left_inv' := fun _ hx => momentInverse_map hx
  right_inv' := fun _ hx => momentMap_inverse hx
  continuousOn_toFun := momentMap_contDiff.continuous.continuousOn
  continuousOn_invFun := (momentInverse_contDiffOn L).continuousOn
  open_source := parameterDomain_isOpen L
  open_target := momentDomain_isOpen L

theorem exists_compact_coordinate_ball {L : ℝ} {y : ℝ × ℝ}
    (hy : y ∈ momentDomain L) :
    ∃ r > 0, closedBall y r ⊆ momentDomain L ∧
      IsCompact (momentInverse '' closedBall y r) ∧
      momentInverse '' closedBall y r ⊆ parameterDomain L := by
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp ((momentDomain_isOpen L).mem_nhds hy)
  have hr : 0 < ε / 2 := half_pos hε
  have hball : closedBall y (ε / 2) ⊆ momentDomain L :=
    (closedBall_subset_ball (half_lt_self hε)).trans hsub
  refine ⟨ε / 2, hr, hball, ?_, ?_⟩
  · exact (isCompact_closedBall y (ε / 2)).image_of_continuousOn
      ((momentInverse_contDiffOn L).continuousOn.mono hball)
  · rintro x ⟨v, hv, rfl⟩
    exact momentInverse_mem (hball hv)

section NearIdentity

variable {E : Type*} [NormedAddCommGroup E]

def BallFixedPointProperty (y : E) (r : ℝ) : Prop :=
  ∀ H : E → E, ContinuousOn H (closedBall y r) →
    MapsTo H (closedBall y r) (closedBall y r) →
    ∃ x ∈ closedBall y r, H x = x

theorem correction_mapsTo {G : E → E} {y : E} {r : ℝ}
    (hnear : ∀ x ∈ closedBall y r, ‖G x - x‖ ≤ r) :
    MapsTo (fun x => y + x - G x) (closedBall y r) (closedBall y r) := by
  intro x hx
  rw [mem_closedBall, dist_eq_norm]
  have heq : y + x - G x - y = -(G x - x) := by abel
  simpa only [heq, norm_neg] using hnear x hx

theorem correction_fixed_iff {G : E → E} {y x : E} :
    y + x - G x = x ↔ G x = y := by
  constructor
  · intro h
    have heq : x + y = x + G x := by
      simpa only [add_comm y x] using (sub_eq_iff_eq_add.mp h)
    exact (add_left_cancel heq).symm
  · intro h
    rw [h]
    abel

theorem near_identity_surjective_of_fixedPointProperty {G : E → E} {y : E} {r : ℝ}
    (hfix : BallFixedPointProperty y r)
    (hG : ContinuousOn G (closedBall y r))
    (hnear : ∀ x ∈ closedBall y r, ‖G x - x‖ ≤ r) :
    ∃ x ∈ closedBall y r, G x = y := by
  obtain ⟨x, hx, hfixed⟩ := hfix (fun x => y + x - G x)
    ((continuousOn_const.add continuousOn_id).sub hG) (correction_mapsTo hnear)
  exact ⟨x, hx, correction_fixed_iff.mp hfixed⟩

theorem near_identity_surjective_of_lipschitz_error [CompleteSpace E]
    {G : E → E} {y : E} {r : ℝ} {K : ℝ≥0}
    (hr : 0 ≤ r) (hK : K < 1)
    (herror : LipschitzOnWith K (fun x => G x - x) (closedBall y r))
    (hnear : ∀ x ∈ closedBall y r, ‖G x - x‖ ≤ r) :
    ∃ x ∈ closedBall y r, G x = y := by
  let H : E → E := fun x => y + x - G x
  have hmaps : MapsTo H (closedBall y r) (closedBall y r) := correction_mapsTo hnear
  have hcontract : ContractingWith K (hmaps.restrict H (closedBall y r) (closedBall y r)) := by
    refine ⟨hK, ?_⟩
    apply LipschitzWith.of_dist_le_mul
    intro a b
    have herr := herror.dist_le_mul a a.property b b.property
    change dist (H a) (H b) ≤ (K : ℝ) * dist (a : E) (b : E)
    have heq : H a - H b = -((G a - a) - (G b - b)) := by dsimp [H]; abel
    simpa only [dist_eq_norm, heq, norm_neg] using herr
  obtain ⟨x, hx, hfixed, _⟩ := ContractingWith.exists_fixedPoint'
    isClosed_closedBall.isComplete hmaps hcontract (mem_closedBall_self hr) (edist_ne_top _ _)
  exact ⟨x, hx, correction_fixed_iff.mp hfixed⟩

theorem near_identity_surjective_of_fderiv_error [CompleteSpace E] [NormedSpace ℝ E]
    {G : E → E} {y : E} {r : ℝ} {K : ℝ≥0}
    (hr : 0 ≤ r) (hK : K < 1)
    (hG : ∀ x ∈ closedBall y r, DifferentiableAt ℝ G x)
    (hderiv : ∀ x ∈ closedBall y r,
      ‖fderiv ℝ G x - ContinuousLinearMap.id ℝ E‖₊ ≤ K)
    (hnear : ∀ x ∈ closedBall y r, ‖G x - x‖ ≤ r) :
    ∃ x ∈ closedBall y r, G x = y := by
  apply near_identity_surjective_of_lipschitz_error hr hK ?_ hnear
  apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le
    (fun x hx => (hG x hx).sub differentiableAt_id) ?_ (convex_closedBall y r)
  intro x hx
  simpa only [fderiv_sub (hG x hx) differentiableAt_id, fderiv_id] using hderiv x hx

theorem eventually_near_identity_surjective_of_c1_convergence
    [CompleteSpace E] [NormedSpace ℝ E]
    {G : ℕ → E → E} {y : E} {r : ℝ}
    (hr : 0 < r)
    (hG : ∀ᶠ n in Filter.atTop, ∀ x ∈ closedBall y r, DifferentiableAt ℝ (G n) x)
    (hvalue : TendstoUniformlyOn G id Filter.atTop (closedBall y r))
    (hderiv : TendstoUniformlyOn (fun n x => fderiv ℝ (G n) x)
      (fun _ => ContinuousLinearMap.id ℝ E) Filter.atTop (closedBall y r)) :
    ∀ᶠ n in Filter.atTop, ∃ x ∈ closedBall y r, G n x = y := by
  filter_upwards [hG, Metric.tendstoUniformlyOn_iff.mp hvalue r hr,
    Metric.tendstoUniformlyOn_iff.mp hderiv (1 / 2) (by norm_num)] with n hn hv hd
  apply near_identity_surjective_of_fderiv_error (K := 1 / 2) hr.le (by norm_num) hn
  · intro x hx
    have h : ‖fderiv ℝ (G n) x - ContinuousLinearMap.id ℝ E‖ ≤ (1 / 2 : ℝ) := by
      simpa only [dist_eq_norm, norm_sub_rev] using (hd x hx).le
    exact_mod_cast h
  · intro x hx
    simpa only [id_eq, dist_eq_norm, norm_sub_rev] using (hv x hx).le

end NearIdentity

theorem moment_exact_of_fixedPointProperty {L : ℝ} {F : (ℝ × ℝ) → ℝ × ℝ}
    {y : ℝ × ℝ} {r : ℝ}
    (hball : closedBall y r ⊆ momentDomain L)
    (hfix : BallFixedPointProperty y r)
    (hF : ContinuousOn F (momentInverse '' closedBall y r))
    (hnear : ∀ x ∈ momentInverse '' closedBall y r, ‖F x - momentMap x‖ ≤ r) :
    ∃ x ∈ parameterDomain L, F x = y := by
  have hG : ContinuousOn (F ∘ momentInverse) (closedBall y r) :=
    hF.comp ((momentInverse_contDiffOn L).continuousOn.mono hball)
      (fun x hx => mem_image_of_mem momentInverse hx)
  obtain ⟨v, hv, heq⟩ := near_identity_surjective_of_fixedPointProperty hfix hG
    (fun v hv => by
      simpa only [Function.comp_apply, momentMap_inverse (hball hv)] using
        hnear (momentInverse v) (mem_image_of_mem momentInverse hv))
  exact ⟨momentInverse v, momentInverse_mem (hball hv), heq⟩

theorem moment_exact_of_lipschitz_error {L : ℝ} {F : (ℝ × ℝ) → ℝ × ℝ}
    {y : ℝ × ℝ} {r : ℝ} {K : ℝ≥0}
    (hr : 0 ≤ r) (hK : K < 1)
    (hball : closedBall y r ⊆ momentDomain L)
    (herror : LipschitzOnWith K (fun v => F (momentInverse v) - v) (closedBall y r))
    (hnear : ∀ x ∈ momentInverse '' closedBall y r, ‖F x - momentMap x‖ ≤ r) :
    ∃ x ∈ parameterDomain L, F x = y := by
  obtain ⟨v, hv, heq⟩ := near_identity_surjective_of_lipschitz_error hr hK herror
    (fun v hv => by
      simpa only [momentMap_inverse (hball hv)] using
        hnear (momentInverse v) (mem_image_of_mem momentInverse hv))
  exact ⟨momentInverse v, momentInverse_mem (hball hv), heq⟩

theorem eventually_moment_exact_of_uniform_convergence {L : ℝ}
    {F : ℕ → (ℝ × ℝ) → ℝ × ℝ} {y : ℝ × ℝ} {r : ℝ}
    (hr : 0 < r) (hball : closedBall y r ⊆ momentDomain L)
    (hfix : BallFixedPointProperty y r)
    (hF : ∀ n, ContinuousOn (F n) (momentInverse '' closedBall y r))
    (hconv : TendstoUniformlyOn F momentMap Filter.atTop
      (momentInverse '' closedBall y r)) :
    ∀ᶠ n in Filter.atTop, ∃ x ∈ parameterDomain L, F n x = y := by
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconv r hr] with n hn
  apply moment_exact_of_fixedPointProperty hball hfix (hF n)
  intro x hx
  have h := (hn x hx).le
  simpa only [dist_eq_norm, norm_sub_rev] using h

theorem eventually_moment_exact_of_uniform_convergence_and_lipschitz {L : ℝ}
    {F : ℕ → (ℝ × ℝ) → ℝ × ℝ} {y : ℝ × ℝ} {r : ℝ} {K : ℝ≥0}
    (hr : 0 < r) (hK : K < 1) (hball : closedBall y r ⊆ momentDomain L)
    (herror : ∀ᶠ n in Filter.atTop,
      LipschitzOnWith K (fun v => F n (momentInverse v) - v) (closedBall y r))
    (hconv : TendstoUniformlyOn F momentMap Filter.atTop
      (momentInverse '' closedBall y r)) :
    ∀ᶠ n in Filter.atTop, ∃ x ∈ parameterDomain L, F n x = y := by
  filter_upwards [herror, Metric.tendstoUniformlyOn_iff.mp hconv r hr] with n herr hn
  apply moment_exact_of_lipschitz_error hr.le hK hball herr
  intro x hx
  have h := (hn x hx).le
  simpa only [dist_eq_norm, norm_sub_rev] using h

theorem eventually_moment_exact_of_locally_uniform_convergence {L : ℝ}
    {F : ℕ → (ℝ × ℝ) → ℝ × ℝ} {y : ℝ × ℝ}
    (hy : y ∈ momentDomain L)
    (hfix : ∀ r > 0, BallFixedPointProperty y r)
    (hF : ∀ n, ContinuousOn (F n) (parameterDomain L))
    (hconv : ∀ D : Set (ℝ × ℝ), IsCompact D → D ⊆ parameterDomain L →
      TendstoUniformlyOn F momentMap Filter.atTop D) :
    ∀ᶠ n in Filter.atTop, ∃ x ∈ parameterDomain L, F n x = y := by
  obtain ⟨r, hr, hball, hcompact, hsub⟩ := exists_compact_coordinate_ball hy
  exact eventually_moment_exact_of_uniform_convergence hr hball (hfix r hr)
    (fun n => (hF n).mono hsub) (hconv _ hcompact hsub)

theorem eventually_moment_exact_of_c1_convergence {L : ℝ}
    {F : ℕ → (ℝ × ℝ) → ℝ × ℝ} {y : ℝ × ℝ} {r : ℝ}
    (hr : 0 < r) (hball : closedBall y r ⊆ momentDomain L)
    (hG : ∀ᶠ n in Filter.atTop, ∀ x ∈ closedBall y r,
      DifferentiableAt ℝ (F n ∘ momentInverse) x)
    (hvalue : TendstoUniformlyOn (fun n => F n ∘ momentInverse)
      id Filter.atTop (closedBall y r))
    (hderiv : TendstoUniformlyOn (fun n x => fderiv ℝ (F n ∘ momentInverse) x)
      (fun _ => ContinuousLinearMap.id ℝ (ℝ × ℝ)) Filter.atTop (closedBall y r)) :
    ∀ᶠ n in Filter.atTop, ∃ x ∈ parameterDomain L, F n x = y := by
  filter_upwards [eventually_near_identity_surjective_of_c1_convergence hr hG hvalue hderiv]
    with n hn
  obtain ⟨v, hv, heq⟩ := hn
  exact ⟨momentInverse v, momentInverse_mem (hball hv), heq⟩

end Rhone.Statistics.Identifiability.MutationMomentSurjectivity
