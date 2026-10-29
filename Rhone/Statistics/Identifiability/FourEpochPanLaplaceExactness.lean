/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.FourEpochBackwardValue
public import Rhone.Statistics.Identifiability.FourEpochProperPanModel
public import Rhone.Statistics.Identifiability.IntegrablePanMutationMoments
public import Rhone.Statistics.Identifiability.IntegrablePanLaplaceVerification
public import Rhone.Statistics.Identifiability.MutationFourEpochExactness

/-! # Exact Laplace transform and mutation moments of the four-epoch pan joint law -/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology Matrix Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false

namespace Rhone.Statistics.Identifiability.FourEpochBackward
open MutationPulseKernel MutationConstantTail
local notation "State" => MutationPulseKernel.State

noncomputable def modelBackwardValue (P : ProperIntegrablePanModel)
    {ε δ M A τ r k : ℝ}
    (hrate : P.rate = fourEpochRate ε δ M A τ) (hrecomb : P.pre.recomb = fun _ => r)
    (hε : 0 < ε) (hτ : ε ≤ τ) (hδ : 0 ≤ δ) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hr : 0 ≤ r) (hk : 0 ≤ k) : IntegrablePanBackwardValue P.rate P.pre.recomb k where
  val := value ε δ M A τ r k
  ac := fun T _ i => value_ac hε hδ hM hA hr hk τ 0 T i
  bounded := ⟨1, fun t _ i => by
    have hh := value_bounds hε hδ hM hA hr hk τ t
    simpa only [abs_of_nonneg (hh.1 i)] using hh.2 i⟩
  absorbing := fun t _ => value_absorbing ε δ M A τ r k t
  equation := by
    simpa only [hrate, hrecomb] using value_ae_hasDerivAt hε hτ hδ hr hk

theorem jointLaw_laplace_eq (P : ProperIntegrablePanModel)
    {ε δ M A τ r k : ℝ}
    (hrate : P.rate = fourEpochRate ε δ M A τ) (hrecomb : P.pre.recomb = fun _ => r)
    (hε : 0 < ε) (hτ : ε ≤ τ) (hδ : 0 ≤ δ) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hr : 0 ≤ r) (hk : 0 < k) :
    (∫ p, Real.exp (-k*p.1) ∂P.pre.jointLaw) =
      fourEpochVector ε δ M r k (tailPayoff δ r k) (A,τ) 3 ∧
    (∫ p, Real.exp (-k*(p.1+p.2)) ∂P.pre.jointLaw) =
      fourEpochVector ε δ M r k (tailPayoff δ r k) (A,τ) 0 := by
  let V := modelBackwardValue P hrate hrecomb hε hτ hδ hM hA hr hk.le
  constructor
  · exact (P.backwardValue_singleLaplace_integral V hk).trans
      (congrFun (value_zero hε hτ δ M A r k) 3)
  · exact (P.pre.backwardValue_jointLaplace_integral V hk).trans
      (congrFun (value_zero hε hτ δ M A r k) 0)

theorem mutationMoments_eq (P : ProperIntegrablePanModel)
    {ε δ M A τ r k : ℝ}
    (hrate : P.rate = fourEpochRate ε δ M A τ) (hrecomb : P.pre.recomb = fun _ => r)
    (hε : 0 < ε) (hτ : ε ≤ τ) (hδ : 0 ≤ δ) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hr : 0 ≤ r) (hk : 0 < k) (L : ℝ) :
    P.mutationMomentPair L k = MutationMomentCoordinates.momentExtract L
      (fourEpochVector ε δ M r k (tailPayoff δ r k) (A,τ)) := by
  let V := modelBackwardValue P hrate hrecomb hε hτ hδ hM hA hr hk.le
  have h := P.mutationMomentPair_eq_backwardValue V hk L
  change P.mutationMomentPair L k =
    MutationMomentCoordinates.momentExtract L (value ε δ M A τ r k 0) at h
  rw [value_zero hε hτ δ M A r k] at h
  exact h

open MutationMomentSurjectivity MutationMomentCoordinates MutationFourEpochExactness
open ProperIntegrablePanModel

theorem fourEpoch_jointLaw_eventually_exact {L r k : ℝ}
    (hL : 0 < L) (hr : 0 ≤ r) (hk : 0 < k)
    {y : ℝ × ℝ} (hy : y ∈ momentDomain L) :
    ∀ᶠ n in atTop, ∃ x ∈ parameterDomain L, ∃ P : ProperIntegrablePanModel,
      0 < pulseScale n ∧ pulseScale n < (coord L k x).2 ∧ 0 < (n : ℝ) ∧
      P.rate = fourEpochRate (pulseScale n) (pulseScale n) (n : ℝ)
        (coord L k x).1 (coord L k x).2 ∧
      P.pre.recomb = (fun _ => r) ∧ IsProbabilityMeasure P.pre.jointLaw ∧
      Integrable (firstMutationObservable L k) P.pre.jointLaw ∧
      Integrable (productMutationObservable L k) P.pre.jointLaw ∧
      P.mutationMomentPair L k = y ∧
      (∀ t : ℝ, pulseScale n ≤ P.rate t ∧
        P.rate t ≤ pulseScale n + ((coord L k x).1 + (n : ℝ)) / pulseScale n) := by
  filter_upwards [fourEpochTailMoments_eventually_exact_bounded_rate hL hr hk hy] with n hn
  obtain ⟨x, hx, hε, hτ, hn, heq, hbound⟩ := hn
  have hA := (coord_pos hL hk hx).1.le
  obtain ⟨P, hPrate, hPrecomb⟩ := exists_fourEpochProperIntegrablePanModel
    (τ := (coord L k x).2) hε hε hn.le hA hr
  let V := modelBackwardValue P hPrate hPrecomb hε hτ.le hε.le hn.le hA hr hk.le
  have hobs := P.mutationMomentPair_integrable_and_eq V hk L
  have hm := mutationMoments_eq P hPrate hPrecomb hε hτ.le hε.le hn.le hA hr hk L
  change P.mutationMomentPair L k = fourEpochTailMoments L r k n x at hm
  exact ⟨x, hx, P, hε, hτ, hn, hPrate, hPrecomb, P.jointLaw_probability,
    hobs.1, hobs.2.1, hm.trans heq, fun t => by simpa only [hPrate] using hbound t⟩

theorem exists_fourEpoch_jointLaw_exact {L r k : ℝ}
    (hL : 0 < L) (hr : 0 ≤ r) (hk : 0 < k)
    {y : ℝ × ℝ} (hy : y ∈ momentDomain L) :
    ∃ (ε δ M A τ : ℝ) (P : ProperIntegrablePanModel),
      0 < ε ∧ 0 < δ ∧ 0 < M ∧ 0 < A ∧ ε < τ ∧
      P.rate = fourEpochRate ε δ M A τ ∧ P.pre.recomb = (fun _ => r) ∧
      IsProbabilityMeasure P.pre.jointLaw ∧
      Integrable (firstMutationObservable L k) P.pre.jointLaw ∧
      Integrable (productMutationObservable L k) P.pre.jointLaw ∧
      P.mutationMomentPair L k = y ∧
      (∀ t : ℝ, δ ≤ P.rate t ∧ P.rate t ≤ δ + (A+M)/ε) := by
  obtain ⟨n, x, hx, P, hε, hτ, hn, hPrate, hPrecomb, hprob, hi1, hi2, heq, hbound⟩ :=
    (fourEpoch_jointLaw_eventually_exact hL hr hk hy).exists
  exact ⟨pulseScale n, pulseScale n, n, (coord L k x).1, (coord L k x).2,
    P, hε, hε, hn, (coord_pos hL hk hx).1, hτ, hPrate, hPrecomb, hprob, hi1, hi2, heq, hbound⟩

end Rhone.Statistics.Identifiability.FourEpochBackward
