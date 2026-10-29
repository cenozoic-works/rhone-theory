/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.MutationFourEpochBounds
public import Rhone.Statistics.Identifiability.MutationFourEpochCalculus

/-! # Compact-uniform `C¹` convergence of the four-epoch matrix family -/

@[expose] public section

open Set Filter
open scoped Topology Matrix Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false

namespace Rhone.Statistics.Identifiability.MutationPulseKernel

theorem fourEpochVector_hasFDerivAt (ε δ M r k : ℝ) (v : State → ℝ) (x : ℝ × ℝ) :
    HasFDerivAt (fourEpochVector ε δ M r k v)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (fourEpochPartialA ε δ M r k v x) +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (fourEpochPartialT ε δ M r k v x)) x := by
  unfold fourEpochVector fourEpochPartialA fourEpochPartialT
  exact
    separated_mulVec_hasFDerivAt
      (fun a => NormedSpace.exp (a • C + ε • B δ r k))
      (fun t => quietEpoch t ε δ r k) x.1 x.2
      (ContractiveDuhamel.expInsertion (x.1 • C + ε • B δ r k) C)
      (B δ r k * quietEpoch x.2 ε δ r k)
      (NormedSpace.exp (M • C + ε • B δ r k) *ᵥ v)
      (early_pulse_hasDerivAt x.1 ε δ r k) (quietEpoch_hasDerivAt x.2 ε δ r k)

theorem fourEpochVector_differentiableAt (ε δ M r k : ℝ) (v : State → ℝ) (x : ℝ × ℝ) :
    DifferentiableAt ℝ (fourEpochVector ε δ M r k v) x :=
  (fourEpochVector_hasFDerivAt ε δ M r k v x).differentiableAt

theorem idealVector_hasFDerivAt (r k : ℝ) (x : ℝ × ℝ) :
    HasFDerivAt (idealVector r k)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (idealPartialA r k x) +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (idealPartialT r k x)) x := by
  unfold idealVector idealPartialA idealPartialT
  exact
    separated_mulVec_hasFDerivAt
      (fun a => NormedSpace.exp (a • C)) (fun t => quietLimitEpoch t r k) x.1 x.2
      (C * NormedSpace.exp (x.1 • C)) (B 0 r k * quietLimitEpoch x.2 r k)
      (fun _ => 1) (hasDerivAt_exp_smul_const' C x.1) (quietLimitEpoch_hasDerivAt x.2 r k)

theorem idealVector_differentiableAt (r k : ℝ) (x : ℝ × ℝ) :
    DifferentiableAt ℝ (idealVector r k) x :=
  (idealVector_hasFDerivAt r k x).differentiableAt

noncomputable def fourEpochDerivativeError (ε δ M r k T : ℝ) : ℝ :=
  12 * fourEpochError ε δ M r k T +
    ((12*δ+4*r+2*k)*earlyEpochError ε δ r k + 12*δ +
      (4*r+2*k)*(quietEpochError ε δ r k T + lateEpochError ε δ M r k))

theorem fourEpochVector_fderiv_error (v : State → ℝ)
    (hv0 : ∀ i, 0 ≤ v i) (hv1 : ∀ i, v i ≤ 1) (hvabs : v 4 = 1)
    {x : ℝ × ℝ} {ε δ M r k T : ℝ}
    (hA : 0 ≤ x.1) (hε : 0 ≤ ε) (hετ : ε ≤ x.2) (hτT : x.2 ≤ T)
    (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hr : 0 ≤ r) (hk : 0 ≤ k) :
    ‖fderiv ℝ (fourEpochVector ε δ M r k v) x - fderiv ℝ (idealVector r k) x‖ ≤
      fourEpochDerivativeError ε δ M r k T := by
  rw [(fourEpochVector_hasFDerivAt ε δ M r k v x).fderiv,
    (idealVector_hasFDerivAt r k x).fderiv]
  have heq :
      (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (fourEpochPartialA ε δ M r k v x) +
          (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (fourEpochPartialT ε δ M r k v x) -
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (idealPartialA r k x) +
          (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (idealPartialT r k x)) =
      (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight
          (fourEpochPartialA ε δ M r k v x - idealPartialA r k x) +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight
          (fourEpochPartialT ε δ M r k v x - idealPartialT r k x) := by
    apply ContinuousLinearMap.ext
    intro y
    change y.1 • fourEpochPartialA ε δ M r k v x + y.2 • fourEpochPartialT ε δ M r k v x -
      (y.1 • idealPartialA r k x + y.2 • idealPartialT r k x) =
      y.1 • (fourEpochPartialA ε δ M r k v x - idealPartialA r k x) +
      y.2 • (fourEpochPartialT ε δ M r k v x - idealPartialT r k x)
    simp only [smul_sub]
    abel
  rw [heq]
  exact (coordinate_derivative_norm_le _ _).trans
    (add_le_add
      (fourEpochPartialA_error v hv0 hv1 hvabs hA hε hετ hτT hM hδ hr hk)
      (fourEpochPartialT_error v hv0 hv1 hvabs hA hε hετ hτT hM hδ hr hk))

theorem fourEpoch_errors_tendsto_zero (r k T : ℝ) :
    Tendsto (fun n => fourEpochError (pulseScale n) (pulseScale n) (n : ℝ) r k T)
      atTop (𝓝 0) ∧
    Tendsto (fun n => fourEpochDerivativeError (pulseScale n) (pulseScale n) (n : ℝ) r k T)
      atTop (𝓝 0) := by
  have hs := pulseScale_tendsto_zero
  have hb : Tendsto (fun n => 12*pulseScale n + 4*r + 2*k) atTop (𝓝 (4*r+2*k)) := by
    convert! ((tendsto_const_nhds.mul hs).add tendsto_const_nhds).add tendsto_const_nhds using 1;
      simp
  have he : Tendsto (fun n => earlyEpochError (pulseScale n) (pulseScale n) r k)
      atTop (𝓝 0) := by
    simpa only [earlyEpochError, zero_mul] using hs.mul hb
  have hq : Tendsto (fun n => quietEpochError (pulseScale n) (pulseScale n) r k T)
      atTop (𝓝 0) := by
    convert! ((tendsto_const_nhds.mul hs).mul tendsto_const_nhds).add
      (hs.mul tendsto_const_nhds) using 1; simp
  have hl : Tendsto (fun n => lateEpochError (pulseScale n) (pulseScale n) (n : ℝ) r k)
      atTop (𝓝 0) := by
    convert! (tendsto_const_nhds.mul exp_neg_nat_tendsto_zero).add he using 1; simp
  have hv : Tendsto (fun n => fourEpochError (pulseScale n) (pulseScale n) (n : ℝ) r k T)
      atTop (𝓝 0) := by
    simpa only [fourEpochError, add_zero] using (he.add hq).add hl
  refine ⟨hv, ?_⟩
  convert! (tendsto_const_nhds.mul hv).add
    (((hb.mul he).add (tendsto_const_nhds.mul hs)).add
      (tendsto_const_nhds.mul (hq.add hl))) using 1; simp

theorem fourEpochVector_uniform_c1_on_strip
    (v : ℕ → State → ℝ) (hv0 : ∀ n i, 0 ≤ v n i) (hv1 : ∀ n i, v n i ≤ 1)
    (hvabs : ∀ n, v n 4 = 1) {r k t T : ℝ} (hr : 0 ≤ r) (hk : 0 ≤ k)
    (ht : 0 < t) {K : Set (ℝ × ℝ)}
    (hK : ∀ x ∈ K, 0 ≤ x.1 ∧ t ≤ x.2 ∧ x.2 ≤ T) :
    TendstoUniformlyOn
      (fun n => fourEpochVector (pulseScale n) (pulseScale n) (n : ℝ) r k (v n))
      (idealVector r k) atTop K ∧
    TendstoUniformlyOn
      (fun n x => fderiv ℝ
        (fourEpochVector (pulseScale n) (pulseScale n) (n : ℝ) r k (v n)) x)
      (fderiv ℝ (idealVector r k)) atTop K := by
  have herr := fourEpoch_errors_tendsto_zero r k T
  constructor
  · apply uniformlyOn_of_eventually_norm_sub_le herr.1
    filter_upwards [pulseScale_eventually_le ht] with n hn
    intro x hx
    obtain ⟨hA, htx, hxT⟩ := hK x hx
    exact fourEpochVector_error (v n) (hv0 n) (hv1 n) (hvabs n) hA
      (pulseScale_nonneg n) (hn.trans htx) hxT (Nat.cast_nonneg n)
      (pulseScale_nonneg n) hr hk
  · apply uniformlyOn_of_eventually_norm_sub_le herr.2
    filter_upwards [pulseScale_eventually_le ht] with n hn
    intro x hx
    obtain ⟨hA, htx, hxT⟩ := hK x hx
    exact fourEpochVector_fderiv_error (v n) (hv0 n) (hv1 n) (hvabs n) hA
      (pulseScale_nonneg n) (hn.trans htx) hxT (Nat.cast_nonneg n)
      (pulseScale_nonneg n) hr hk

theorem fourEpochVector_locally_uniform_c1
    (v : ℕ → State → ℝ) (hv0 : ∀ n i, 0 ≤ v n i) (hv1 : ∀ n i, v n i ≤ 1)
    (hvabs : ∀ n, v n 4 = 1) {r k : ℝ} (hr : 0 ≤ r) (hk : 0 ≤ k)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hsub : K ⊆ {x : ℝ × ℝ | 0 < x.1 ∧ 0 < x.2}) :
    TendstoUniformlyOn
      (fun n => fourEpochVector (pulseScale n) (pulseScale n) (n : ℝ) r k (v n))
      (idealVector r k) atTop K ∧
    TendstoUniformlyOn
      (fun n x => fderiv ℝ
        (fourEpochVector (pulseScale n) (pulseScale n) (n : ℝ) r k (v n)) x)
      (fderiv ℝ (idealVector r k)) atTop K := by
  obtain ⟨t, ht, T, hbound⟩ := compact_positive_time_bounds hK (fun x hx => (hsub hx).2)
  exact fourEpochVector_uniform_c1_on_strip v hv0 hv1 hvabs hr hk ht
    (fun x hx => ⟨(hsub hx).1.le, hbound x hx⟩)

end Rhone.Statistics.Identifiability.MutationPulseKernel
