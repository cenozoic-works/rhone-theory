/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.MutationLocalC1Exactness
public import Rhone.Statistics.Identifiability.MutationFourEpochConvergence
public import Rhone.Statistics.Identifiability.MutationMomentCoordinates
public import Rhone.Statistics.Identifiability.MutationFourEpochRates
public import Rhone.Statistics.Identifiability.MutationConstantTail
public import Rhone.Statistics.Identifiability.MutationFourEpochRegularity

/-! # Exact matching for the four-epoch finite matrix family -/

@[expose] public section

open Set Metric
open scoped Topology ContDiff

namespace Rhone.Statistics.Identifiability.MutationFourEpochExactness

section Affine

variable {D E H : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem affine_comp_fderiv (A : E →L[ℝ] H) (c : H) {f : D → E} {x : D}
    (hf : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun x => c + A (f x)) x = A.comp (fderiv ℝ f x) := by
  exact ((A.hasFDerivAt.comp x hf.hasFDerivAt).const_add c).fderiv

theorem tendstoUniformlyOn_fderiv_affine_comp
    (A : E →L[ℝ] H) (c : H)
    {F : ℕ → D → E} {f : D → E} {K : Set D}
    (hF : ∀ᶠ n in Filter.atTop, ∀ x ∈ K, DifferentiableAt ℝ (F n) x)
    (hf : ∀ x ∈ K, DifferentiableAt ℝ f x)
    (hderiv : TendstoUniformlyOn (fun n x => fderiv ℝ (F n) x)
      (fderiv ℝ f) Filter.atTop K) :
    TendstoUniformlyOn (fun n x => fderiv ℝ (fun x => c + A (F n x)) x)
      (fderiv ℝ (fun x => c + A (f x))) Filter.atTop K := by
  have hc : TendstoUniformlyOn (fun n x => A.comp (fderiv ℝ (F n) x))
      (fun x => A.comp (fderiv ℝ f x)) Filter.atTop K :=
    ((ContinuousLinearMap.compL ℝ D E H) A).uniformContinuous.comp_tendstoUniformlyOn hderiv
  refine (hc.congr_right ?_).congr ?_
  · intro x hx
    exact (affine_comp_fderiv A c (hf x hx)).symm
  · filter_upwards [hF] with n hn
    intro x hx
    exact (affine_comp_fderiv A c (hn x hx)).symm

theorem tendstoUniformlyOn_c1_affine_comp
    (A : E →L[ℝ] H) (c : H)
    {F : ℕ → D → E} {f : D → E} {K : Set D}
    (hF : ∀ᶠ n in Filter.atTop, ∀ x ∈ K, DifferentiableAt ℝ (F n) x)
    (hf : ∀ x ∈ K, DifferentiableAt ℝ f x)
    (hvalue : TendstoUniformlyOn F f Filter.atTop K)
    (hderiv : TendstoUniformlyOn (fun n x => fderiv ℝ (F n) x)
      (fderiv ℝ f) Filter.atTop K) :
    (∀ᶠ n in Filter.atTop, ∀ x ∈ K,
      DifferentiableAt ℝ (fun x => c + A (F n x)) x) ∧
      TendstoUniformlyOn (fun n x => c + A (F n x))
        (fun x => c + A (f x)) Filter.atTop K ∧
      TendstoUniformlyOn (fun n x => fderiv ℝ (fun x => c + A (F n x)) x)
        (fderiv ℝ (fun x => c + A (f x))) Filter.atTop K := by
  refine ⟨?_, ?_, tendstoUniformlyOn_fderiv_affine_comp A c hF hf hderiv⟩
  · filter_upwards [hF] with n hn
    intro x hx
    exact ((A.differentiableAt.comp x (hn x hx)).const_add c)
  · exact (uniformContinuous_const.add A.uniformContinuous).comp_tendstoUniformlyOn hvalue

end Affine

open MutationPulseKernel
local notation "State" => MutationPulseKernel.State

noncomputable def momentLinear (L : ℝ) : (State → ℝ) →L[ℝ] ℝ × ℝ :=
  ((-L) • ContinuousLinearMap.proj (3 : State)).prod
    ((L ^ 2) • (ContinuousLinearMap.proj (0 : State) -
      (2 : ℝ) • ContinuousLinearMap.proj (3 : State)))

theorem momentLinear_affine_formula (L : ℝ) (v : State → ℝ) :
    (L, L ^ 2) + momentLinear L v =
      (L * (1 - v 3), L ^ 2 * (1 - 2 * v 3 + v 0)) := by
  ext <;> simp [momentLinear] <;> ring

open MutationMomentSurjectivity
open MutationMomentCoordinates (coord momentExtract contDiffOn_coord coord_pos
  ideal_extraction_eq_momentMap)

theorem momentExtract_eq_affine (L : ℝ) (v : State → ℝ) :
    momentExtract L v = (L, L ^ 2) + momentLinear L v :=
  (momentLinear_affine_formula L v).symm

theorem momentExtract_hasFDerivAt (L : ℝ) (v : State → ℝ) :
    HasFDerivAt (momentExtract L) (momentLinear L) v := by
  have heq : momentExtract L = fun v => (L, L ^ 2) + momentLinear L v :=
    funext (momentExtract_eq_affine L)
  rw [heq]
  exact ((momentLinear L).hasFDerivAt (x := v)).const_add (L, L ^ 2)

theorem momentExtract_contDiff (L : ℝ) : ContDiff ℝ ∞ (momentExtract L) := by
  have heq : momentExtract L = fun v => (L, L ^ 2) + momentLinear L v :=
    funext (momentExtract_eq_affine L)
  rw [heq]
  exact contDiff_const.add (momentLinear L).contDiff

theorem coord_differentiableAt {L : ℝ} (hL : 0 < L) (k : ℝ) {x : ℝ × ℝ}
    (hx : x ∈ parameterDomain L) : DifferentiableAt ℝ (coord L k) x :=
  ((contDiffOn_coord hL k).contDiffAt ((parameterDomain_isOpen L).mem_nhds hx)).differentiableAt
    (by simp)

noncomputable def fourEpochMoments (L r k : ℝ) (v : ℕ → State → ℝ)
    (n : ℕ) (x : ℝ × ℝ) : ℝ × ℝ :=
  momentExtract L
    (fourEpochVector (pulseScale n) (pulseScale n) (n : ℝ) r k (v n) (coord L k x))

theorem fourEpochMoments_eq_affine (L r k : ℝ) (v : ℕ → State → ℝ) :
    fourEpochMoments L r k v = fun n x => (L, L ^ 2) + momentLinear L
      (fourEpochVector (pulseScale n) (pulseScale n) (n : ℝ) r k (v n) (coord L k x)) := by
  funext n x
  exact momentExtract_eq_affine L _

theorem fourEpochMoments_contDiffOn_one {L : ℝ} (hL : 0 < L) (r k : ℝ)
    (v : ℕ → State → ℝ) (n : ℕ) :
    ContDiffOn ℝ 1 (fourEpochMoments L r k v n) (parameterDomain L) := by
  exact (((momentExtract_contDiff L).of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).comp
    (fourEpochVector_contDiff_one (pulseScale n) (pulseScale n) (n : ℝ) r k (v n))).comp_contDiffOn
    ((contDiffOn_coord hL k).of_le (by simp))

theorem fourEpochMoments_differentiableAt {L : ℝ} (hL : 0 < L) (r k : ℝ)
    (v : ℕ → State → ℝ) (n : ℕ) {x : ℝ × ℝ} (hx : x ∈ parameterDomain L) :
    DifferentiableAt ℝ (fourEpochMoments L r k v n) x := by
  exact (momentExtract_hasFDerivAt L _).differentiableAt.comp x
    ((fourEpochVector_differentiableAt (pulseScale n) (pulseScale n) (n : ℝ) r k (v n) _).comp x
      (coord_differentiableAt hL k hx))

theorem ideal_moments_eq_momentMap {L k : ℝ} (hL : 0 < L) (hk : 0 < k)
    (r : ℝ) {x : ℝ × ℝ} (hx : x ∈ parameterDomain L) :
    (L, L ^ 2) + momentLinear L (idealVector r k (coord L k x)) = momentMap x := by
  rw [← momentExtract_eq_affine]
  exact ideal_extraction_eq_momentMap hL hk r hx

theorem fourEpochMoments_locally_uniform_c1
    (v : ℕ → State → ℝ) (hv0 : ∀ n i, 0 ≤ v n i) (hv1 : ∀ n i, v n i ≤ 1)
    (hvabs : ∀ n, v n 4 = 1) {L r k : ℝ}
    (hL : 0 < L) (hr : 0 ≤ r) (hk : 0 < k)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hsub : K ⊆ parameterDomain L) :
    TendstoUniformlyOn (fourEpochMoments L r k v) momentMap Filter.atTop K ∧
      TendstoUniformlyOn (fun n x => fderiv ℝ (fourEpochMoments L r k v n) x)
        (fderiv ℝ momentMap) Filter.atTop K := by
  have hc : IsCompact (coord L k '' K) :=
    hK.image_of_continuousOn ((contDiffOn_coord hL k).continuousOn.mono hsub)
  have hpos : coord L k '' K ⊆ {x : ℝ × ℝ | 0 < x.1 ∧ 0 < x.2} := by
    rintro x ⟨z, hz, rfl⟩
    exact coord_pos hL hk (hsub hz)
  obtain ⟨hv, hd⟩ := fourEpochVector_locally_uniform_c1 v hv0 hv1 hvabs hr hk.le hc hpos
  have hpre := tendstoUniformlyOn_c1_comp_on_compact hK
    (Filter.Eventually.of_forall (fun n x _ =>
      fourEpochVector_differentiableAt (pulseScale n) (pulseScale n) (n : ℝ) r k (v n) x))
    (fun x _ => idealVector_differentiableAt r k x)
    (fun x hx => coord_differentiableAt hL k (hsub hx))
    (((contDiffOn_coord hL k).continuousOn_fderiv_of_isOpen
      (parameterDomain_isOpen L) (by simp)).mono hsub) hv hd
  have hpost := tendstoUniformlyOn_c1_affine_comp (momentLinear L) (L, L ^ 2) hpre.1
    (fun x hx => (idealVector_differentiableAt r k _).comp x
      (coord_differentiableAt hL k (hsub hx))) hpre.2.1 hpre.2.2
  have hideal : EqOn
      (fun x => (L, L ^ 2) + momentLinear L (idealVector r k (coord L k x)))
      momentMap (parameterDomain L) := fun _ hx => ideal_moments_eq_momentMap hL hk r hx
  have hdideal : EqOn
      (fderiv ℝ (fun x => (L, L ^ 2) + momentLinear L (idealVector r k (coord L k x))))
      (fderiv ℝ momentMap) (parameterDomain L) := by
    intro x hx
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [(parameterDomain_isOpen L).eventually_mem hx] with z hz
    exact hideal hz
  constructor
  · have h := hpost.2.1.congr_right (hideal.mono hsub)
    simpa only [fourEpochMoments_eq_affine, Function.comp_apply] using h
  · have h := hpost.2.2.congr_right (hdideal.mono hsub)
    simpa only [fourEpochMoments_eq_affine, Function.comp_apply] using h

theorem fourEpochMoments_eventually_exact
    (v : ℕ → State → ℝ) (hv0 : ∀ n i, 0 ≤ v n i) (hv1 : ∀ n i, v n i ≤ 1)
    (hvabs : ∀ n, v n 4 = 1) {L r k : ℝ}
    (hL : 0 < L) (hr : 0 ≤ r) (hk : 0 < k)
    {y : ℝ × ℝ} (hy : y ∈ momentDomain L) :
    ∀ᶠ n in Filter.atTop, ∃ x ∈ parameterDomain L,
      fourEpochMoments L r k v n x = y := by
  apply eventually_moment_exact_of_local_c1 hy
    (Filter.Eventually.of_forall (fun n x hx => fourEpochMoments_differentiableAt hL r k v n hx))
  · intro K hK hsub
    exact (fourEpochMoments_locally_uniform_c1 v hv0 hv1 hvabs hL hr hk hK hsub).1
  · intro K hK hsub
    exact (fourEpochMoments_locally_uniform_c1 v hv0 hv1 hvabs hL hr hk hK hsub).2

theorem fourEpochMoments_eventually_exact_positive_epochs
    (v : ℕ → State → ℝ) (hv0 : ∀ n i, 0 ≤ v n i) (hv1 : ∀ n i, v n i ≤ 1)
    (hvabs : ∀ n, v n 4 = 1) {L r k : ℝ}
    (hL : 0 < L) (hr : 0 ≤ r) (hk : 0 < k)
    {y : ℝ × ℝ} (hy : y ∈ momentDomain L) :
    ∀ᶠ n in Filter.atTop, ∃ x ∈ parameterDomain L,
      0 < pulseScale n ∧ pulseScale n < (coord L k x).2 ∧
        0 < (n : ℝ) ∧ fourEpochMoments L r k v n x = y := by
  obtain ⟨ρ, hρ, hball, hcompact, hsub⟩ := exists_compact_coordinate_ball hy
  have hc : IsCompact (coord L k '' (momentInverse '' closedBall y ρ)) :=
    hcompact.image_of_continuousOn ((contDiffOn_coord hL k).continuousOn.mono hsub)
  obtain ⟨t, ht, T, hbound⟩ := compact_positive_time_bounds hc (fun z hz => by
    rcases hz with ⟨x, hx, rfl⟩
    exact (coord_pos hL hk (hsub hx)).2)
  have hconv := fourEpochMoments_locally_uniform_c1 v hv0 hv1 hvabs hL hr hk hcompact hsub
  have hexact := eventually_moment_exact_on_coordinate_ball hρ hball
    (Filter.Eventually.of_forall (fun n x hx =>
      fourEpochMoments_differentiableAt hL r k v n (hsub hx))) hconv.1 hconv.2
  filter_upwards [hexact, eventually_pulseScale_lt ht] with n hn hscale
  obtain ⟨x, hx, heq⟩ := hn
  exact ⟨x, hsub hx, hscale.1,
    hscale.2.1.trans_le (hbound _ (mem_image_of_mem (coord L k) hx)).1,
    hscale.2.2, heq⟩

noncomputable def fourEpochTailMoments (L r k : ℝ) : ℕ → (ℝ × ℝ) → ℝ × ℝ :=
  fourEpochMoments L r k (fun n => MutationConstantTail.tailPayoff (pulseScale n) r k)

theorem fourEpochTailMoments_contDiffOn_one {L : ℝ} (hL : 0 < L) (r k : ℝ) (n : ℕ) :
    ContDiffOn ℝ 1 (fourEpochTailMoments L r k n) (parameterDomain L) :=
  fourEpochMoments_contDiffOn_one hL r k _ n

theorem fourEpochTailMoments_locally_uniform_c1 {L r k : ℝ}
    (hL : 0 < L) (hr : 0 ≤ r) (hk : 0 < k)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hsub : K ⊆ parameterDomain L) :
    TendstoUniformlyOn (fourEpochTailMoments L r k) momentMap Filter.atTop K ∧
      TendstoUniformlyOn (fun n x => fderiv ℝ (fourEpochTailMoments L r k n) x)
        (fderiv ℝ momentMap) Filter.atTop K :=
  fourEpochMoments_locally_uniform_c1 _
    (fun n i => MutationConstantTail.tailPayoff_nonneg (pulseScale_nonneg n) hr i)
    (fun n i => MutationConstantTail.tailPayoff_le_one (pulseScale_nonneg n) hr i)
    (fun n => MutationConstantTail.tailPayoff_absorbing (pulseScale n) r k) hL hr hk hK hsub

theorem fourEpochTailMoments_eventually_exact {L r k : ℝ}
    (hL : 0 < L) (hr : 0 ≤ r) (hk : 0 < k)
    {y : ℝ × ℝ} (hy : y ∈ momentDomain L) :
    ∀ᶠ n in Filter.atTop, ∃ x ∈ parameterDomain L,
      0 < pulseScale n ∧ pulseScale n < (coord L k x).2 ∧
        0 < (n : ℝ) ∧ fourEpochTailMoments L r k n x = y ∧
        (∀ t : ℝ, 0 < fourEpochRate (pulseScale n) (pulseScale n) (n : ℝ)
          (coord L k x).1 (coord L k x).2 t) := by
  have hexact := fourEpochMoments_eventually_exact_positive_epochs _
    (fun n i => MutationConstantTail.tailPayoff_nonneg (pulseScale_nonneg n) hr i)
    (fun n i => MutationConstantTail.tailPayoff_le_one (pulseScale_nonneg n) hr i)
    (fun n => MutationConstantTail.tailPayoff_absorbing (pulseScale n) r k) hL hr hk hy
  filter_upwards [hexact] with n hn
  obtain ⟨x, hx, hε, hτ, hn, heq⟩ := hn
  exact ⟨x, hx, hε, hτ, hn, heq,
    fun t => fourEpochRate_pos hε hε hn.le (coord_pos hL hk hx).1.le t⟩

theorem fourEpochTailMoments_eventually_exact_bounded_rate {L r k : ℝ}
    (hL : 0 < L) (hr : 0 ≤ r) (hk : 0 < k)
    {y : ℝ × ℝ} (hy : y ∈ momentDomain L) :
    ∀ᶠ n in Filter.atTop, ∃ x ∈ parameterDomain L,
      0 < pulseScale n ∧ pulseScale n < (coord L k x).2 ∧
        0 < (n : ℝ) ∧ fourEpochTailMoments L r k n x = y ∧
        (∀ t : ℝ, pulseScale n ≤ fourEpochRate (pulseScale n) (pulseScale n) (n : ℝ)
          (coord L k x).1 (coord L k x).2 t ∧
          fourEpochRate (pulseScale n) (pulseScale n) (n : ℝ)
            (coord L k x).1 (coord L k x).2 t ≤
              pulseScale n + ((coord L k x).1 + (n : ℝ)) / pulseScale n) := by
  filter_upwards [fourEpochTailMoments_eventually_exact hL hr hk hy] with n hn
  obtain ⟨x, hx, hε, hτ, hn, heq, _⟩ := hn
  exact ⟨x, hx, hε, hτ, hn, heq, fun t =>
    ⟨fourEpochRate_lower hε hn.le (coord_pos hL hk hx).1.le t,
      fourEpochRate_upper hε hn.le (coord_pos hL hk hx).1.le t⟩⟩

end Rhone.Statistics.Identifiability.MutationFourEpochExactness
