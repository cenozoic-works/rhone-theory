/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.MutationMomentSurjectivity

/-! # Exact moment matching from local compact-uniform C¹ convergence -/

@[expose] public section

open Set Metric
open scoped Topology ContDiff

namespace Rhone.Statistics.Identifiability.MutationMomentSurjectivity

section Composition

theorem tendstoUniformlyOn_comp_image {E D H : Type*} [PseudoMetricSpace H]
    {F : ℕ → E → H} {f : E → H}
    {g : D → E} {K : Set D}
    (hvalue : TendstoUniformlyOn F f Filter.atTop (g '' K)) :
    TendstoUniformlyOn (fun n => F n ∘ g) (f ∘ g) Filter.atTop K := by
  rw [Metric.tendstoUniformlyOn_iff] at hvalue ⊢
  intro ε hε
  filter_upwards [hvalue ε hε] with n hn
  intro x hx
  exact hn (g x) (mem_image_of_mem g hx)

variable {E : Type*} {D : Type*} {H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem tendstoUniformlyOn_fderiv_comp_of_bound
    {F : ℕ → E → H} {f : E → H} {g : D → E} {K : Set D} {C : ℝ}
    (hF : ∀ᶠ n in Filter.atTop, ∀ x ∈ g '' K, DifferentiableAt ℝ (F n) x)
    (hf : ∀ x ∈ g '' K, DifferentiableAt ℝ f x)
    (hg : ∀ x ∈ K, DifferentiableAt ℝ g x)
    (hC : 0 < C) (hbound : ∀ x ∈ K, ‖fderiv ℝ g x‖ ≤ C)
    (hderiv : TendstoUniformlyOn (fun n x => fderiv ℝ (F n) x)
      (fderiv ℝ f) Filter.atTop (g '' K)) :
    TendstoUniformlyOn (fun n x => fderiv ℝ (F n ∘ g) x)
      (fderiv ℝ (f ∘ g)) Filter.atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hF, Metric.tendstoUniformlyOn_iff.mp
    hderiv (ε / C) (div_pos hε hC)] with n hn hd
  intro x hx
  have hxg : g x ∈ g '' K := mem_image_of_mem g hx
  have hdiff : ‖fderiv ℝ (F n) (g x) - fderiv ℝ f (g x)‖ < ε / C := by
    simpa only [dist_eq_norm, norm_sub_rev] using hd (g x) hxg
  rw [dist_eq_norm, norm_sub_rev,
    fderiv_comp x (hn _ hxg) (hg x hx), fderiv_comp x (hf _ hxg) (hg x hx),
    ← ContinuousLinearMap.sub_comp]
  calc
    _ ≤ ‖fderiv ℝ (F n) (g x) - fderiv ℝ f (g x)‖ * ‖fderiv ℝ g x‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖fderiv ℝ (F n) (g x) - fderiv ℝ f (g x)‖ * C :=
      mul_le_mul_of_nonneg_left (hbound x hx) (norm_nonneg _)
    _ < (ε / C) * C := mul_lt_mul_of_pos_right hdiff hC
    _ = ε := div_mul_cancel₀ ε (ne_of_gt hC)

theorem tendstoUniformlyOn_fderiv_comp_on_compact
    {F : ℕ → E → H} {f : E → H} {g : D → E} {K : Set D}
    (hK : IsCompact K)
    (hF : ∀ᶠ n in Filter.atTop, ∀ x ∈ g '' K, DifferentiableAt ℝ (F n) x)
    (hf : ∀ x ∈ g '' K, DifferentiableAt ℝ f x)
    (hg : ∀ x ∈ K, DifferentiableAt ℝ g x)
    (hDg : ContinuousOn (fderiv ℝ g) K)
    (hderiv : TendstoUniformlyOn (fun n x => fderiv ℝ (F n) x)
      (fderiv ℝ f) Filter.atTop (g '' K)) :
    TendstoUniformlyOn (fun n x => fderiv ℝ (F n ∘ g) x)
      (fderiv ℝ (f ∘ g)) Filter.atTop K := by
  obtain ⟨C, hC, hbound⟩ :=
    (hK.image_of_continuousOn hDg).isBounded.exists_pos_norm_le
  exact tendstoUniformlyOn_fderiv_comp_of_bound hF hf hg hC
    (fun x hx => hbound _ (mem_image_of_mem _ hx)) hderiv

theorem tendstoUniformlyOn_c1_comp_on_compact
    {F : ℕ → E → H} {f : E → H} {g : D → E} {K : Set D}
    (hK : IsCompact K)
    (hF : ∀ᶠ n in Filter.atTop, ∀ x ∈ g '' K, DifferentiableAt ℝ (F n) x)
    (hf : ∀ x ∈ g '' K, DifferentiableAt ℝ f x)
    (hg : ∀ x ∈ K, DifferentiableAt ℝ g x)
    (hDg : ContinuousOn (fderiv ℝ g) K)
    (hvalue : TendstoUniformlyOn F f Filter.atTop (g '' K))
    (hderiv : TendstoUniformlyOn (fun n x => fderiv ℝ (F n) x)
      (fderiv ℝ f) Filter.atTop (g '' K)) :
    (∀ᶠ n in Filter.atTop, ∀ x ∈ K, DifferentiableAt ℝ (F n ∘ g) x) ∧
      TendstoUniformlyOn (fun n => F n ∘ g) (f ∘ g) Filter.atTop K ∧
      TendstoUniformlyOn (fun n x => fderiv ℝ (F n ∘ g) x)
        (fderiv ℝ (f ∘ g)) Filter.atTop K := by
  refine ⟨?_, tendstoUniformlyOn_comp_image hvalue,
    tendstoUniformlyOn_fderiv_comp_on_compact hK hF hf hg hDg hderiv⟩
  filter_upwards [hF] with n hn
  intro x hx
  exact (hn _ (mem_image_of_mem g hx)).comp x (hg x hx)

end Composition

theorem momentInverse_differentiableAt {L : ℝ} {y : ℝ × ℝ}
    (hy : y ∈ momentDomain L) : DifferentiableAt ℝ momentInverse y := by
  exact ((momentInverse_contDiffOn L).contDiffAt
    ((momentDomain_isOpen L).mem_nhds hy)).differentiableAt (by simp)

theorem momentMap_fderiv_inverse {L : ℝ} {y : ℝ × ℝ}
    (hy : y ∈ momentDomain L) :
    (fderiv ℝ momentMap (momentInverse y)).comp (fderiv ℝ momentInverse y) =
      ContinuousLinearMap.id ℝ (ℝ × ℝ) := by
  have heq : momentMap ∘ momentInverse =ᶠ[𝓝 y] id := by
    filter_upwards [(momentDomain_isOpen L).eventually_mem hy] with x hx
    exact momentMap_inverse hx
  rw [← fderiv_comp y (momentMap_contDiff.differentiable (by simp) _)
    (momentInverse_differentiableAt hy), heq.fderiv_eq, fderiv_id]

theorem exists_pos_bound_fderiv_momentInverse {L : ℝ} {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) (hsub : K ⊆ momentDomain L) :
    ∃ C > 0, ∀ y ∈ K, ‖fderiv ℝ momentInverse y‖ ≤ C := by
  have hcont : ContinuousOn (fderiv ℝ momentInverse) K :=
    ((momentInverse_contDiffOn L).continuousOn_fderiv_of_isOpen
      (momentDomain_isOpen L) (by simp)).mono hsub
  obtain ⟨C, hC, hbound⟩ :=
    (hK.image_of_continuousOn hcont).isBounded.exists_pos_norm_le
  exact ⟨C, hC, fun y hy => hbound _ (mem_image_of_mem _ hy)⟩

theorem eventually_moment_exact_of_local_c1 {L : ℝ}
    {F : ℕ → (ℝ × ℝ) → ℝ × ℝ} {y : ℝ × ℝ}
    (hy : y ∈ momentDomain L)
    (hF : ∀ᶠ n in Filter.atTop, ∀ x ∈ parameterDomain L,
      DifferentiableAt ℝ (F n) x)
    (hvalue : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ parameterDomain L →
      TendstoUniformlyOn F momentMap Filter.atTop K)
    (hderiv : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ parameterDomain L →
      TendstoUniformlyOn (fun n x => fderiv ℝ (F n) x)
        (fderiv ℝ momentMap) Filter.atTop K) :
    ∀ᶠ n in Filter.atTop, ∃ x ∈ parameterDomain L, F n x = y := by
  obtain ⟨r, hr, hball, hcompact, hsub⟩ := exists_compact_coordinate_ball hy
  have hInv : ∀ v ∈ closedBall y r, DifferentiableAt ℝ momentInverse v :=
    fun v hv => momentInverse_differentiableAt (hball hv)
  obtain ⟨C, hC, hbound⟩ :=
    exists_pos_bound_fderiv_momentInverse (isCompact_closedBall y r) hball
  apply eventually_moment_exact_of_c1_convergence hr hball
  · filter_upwards [hF] with n hn
    intro v hv
    exact (hn _ (momentInverse_mem (hball hv))).comp v (hInv v hv)
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp
      (hvalue _ hcompact hsub) ε hε] with n hn
    intro v hv
    simpa only [Function.comp_apply, momentMap_inverse (hball hv), id_eq] using
      hn (momentInverse v) (mem_image_of_mem momentInverse hv)
  · rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [hF, Metric.tendstoUniformlyOn_iff.mp
      (hderiv _ hcompact hsub) (ε / C) (div_pos hε hC)] with n hn hd
    intro v hv
    have hdiff : ‖fderiv ℝ (F n) (momentInverse v) -
        fderiv ℝ momentMap (momentInverse v)‖ < ε / C := by
      simpa only [dist_eq_norm, norm_sub_rev] using
        hd (momentInverse v) (mem_image_of_mem momentInverse hv)
    rw [dist_eq_norm, norm_sub_rev,
      fderiv_comp v (hn _ (momentInverse_mem (hball hv))) (hInv v hv),
      ← momentMap_fderiv_inverse (hball hv), ← ContinuousLinearMap.sub_comp]
    calc
      _ ≤ ‖fderiv ℝ (F n) (momentInverse v) -
          fderiv ℝ momentMap (momentInverse v)‖ * ‖fderiv ℝ momentInverse v‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖fderiv ℝ (F n) (momentInverse v) -
          fderiv ℝ momentMap (momentInverse v)‖ * C :=
        mul_le_mul_of_nonneg_left (hbound v hv) (norm_nonneg _)
      _ < (ε / C) * C := mul_lt_mul_of_pos_right hdiff hC
      _ = ε := div_mul_cancel₀ ε (ne_of_gt hC)

theorem eventually_moment_exact_on_coordinate_ball {L : ℝ}
    {F : ℕ → (ℝ × ℝ) → ℝ × ℝ} {y : ℝ × ℝ} {r : ℝ}
    (hr : 0 < r) (hball : closedBall y r ⊆ momentDomain L)
    (hF : ∀ᶠ n in Filter.atTop, ∀ x ∈ momentInverse '' closedBall y r,
      DifferentiableAt ℝ (F n) x)
    (hvalue : TendstoUniformlyOn F momentMap Filter.atTop
      (momentInverse '' closedBall y r))
    (hderiv : TendstoUniformlyOn (fun n x => fderiv ℝ (F n) x)
      (fderiv ℝ momentMap) Filter.atTop (momentInverse '' closedBall y r)) :
    ∀ᶠ n in Filter.atTop, ∃ x ∈ momentInverse '' closedBall y r, F n x = y := by
  have hpre := tendstoUniformlyOn_c1_comp_on_compact (isCompact_closedBall y r) hF
    (fun x _ => momentMap_contDiff.differentiable (by simp) x)
    (fun x hx => momentInverse_differentiableAt (hball hx))
    (((momentInverse_contDiffOn L).continuousOn_fderiv_of_isOpen
      (momentDomain_isOpen L) (by simp)).mono hball) hvalue hderiv
  have hv : TendstoUniformlyOn (fun n => F n ∘ momentInverse) id
      Filter.atTop (closedBall y r) :=
    hpre.2.1.congr_right (fun x hx => momentMap_inverse (hball hx))
  have hd : TendstoUniformlyOn (fun n x => fderiv ℝ (F n ∘ momentInverse) x)
      (fun _ => ContinuousLinearMap.id ℝ (ℝ × ℝ)) Filter.atTop (closedBall y r) := by
    apply hpre.2.2.congr_right
    intro x hx
    rw [fderiv_comp x (momentMap_contDiff.differentiable (by simp) _)
      (momentInverse_differentiableAt (hball hx)), momentMap_fderiv_inverse (hball hx)]
  filter_upwards [eventually_near_identity_surjective_of_c1_convergence hr hpre.1 hv hd]
    with n hn
  obtain ⟨x, hx, heq⟩ := hn
  exact ⟨momentInverse x, mem_image_of_mem momentInverse hx, heq⟩

end Rhone.Statistics.Identifiability.MutationMomentSurjectivity
