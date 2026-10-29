/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegrablePanLaplaceVerification

/-! # Mutation-observable moments under the proper locally integrable pan joint law -/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Rhone.Statistics.Identifiability

set_option backward.isDefEq.respectTransparency false

namespace IntegrablePanBackwardValue

theorem pairLaw_laplace_integrable {rate recomb : ℝ → ℝ} {k : ℝ}
    (V : IntegrablePanBackwardValue rate recomb k)
    (hr : LocallyIntegrableOn rate (Ici 0) volume)
    (hrn : ∀ᵐ t, 0 ≤ t → 0 ≤ rate t) (hk : 0 < k)
    {s : ℝ} (hs : 0 ≤ s) :
    Integrable (fun t => Real.exp (-k * (t-s)))
      (conditionalPairLaw rate (integrablePanClock rate) s) := by
  refine ⟨(Real.measurable_exp.comp
    ((measurable_id.sub_const s).const_mul (-k))).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun t => (Real.exp_pos _).le)),
    V.pairLaw_laplace_lintegral hr hrn hk hs]
  exact ENNReal.ofReal_lt_top

end IntegrablePanBackwardValue

namespace ProperIntegrablePanModel

variable (P : ProperIntegrablePanModel)

noncomputable def firstMutationObservable (L k : ℝ) (p : ℝ × ℝ) : ℝ :=
  L * (1 - Real.exp (-k * p.1))

noncomputable def productMutationObservable (L k : ℝ) (p : ℝ × ℝ) : ℝ :=
  L^2 * (1 - Real.exp (-k * p.1)) * (1 - Real.exp (-k * p.2))

noncomputable def mutationMomentPair (L k : ℝ) : ℝ × ℝ :=
  (∫ p, firstMutationObservable L k p ∂P.pre.jointLaw,
   ∫ p, productMutationObservable L k p ∂P.pre.jointLaw)

variable {k : ℝ} (V : IntegrablePanBackwardValue P.rate P.pre.recomb k)

include V in
theorem backwardValue_fstLaplace_integrable (hk : 0 < k) :
    Integrable (fun p => Real.exp (-k * p.1)) P.pre.jointLaw := by
  have h := V.pairLaw_laplace_integrable P.pre.rate_integrable
    P.pre.rate_nonneg hk (s := 0) le_rfl
  simp only [sub_zero] at h
  rw [← P.jointLaw_map_fst] at h
  exact h.comp_aemeasurable measurable_fst.aemeasurable

include V in
theorem backwardValue_sndLaplace_integrable (hk : 0 < k) :
    Integrable (fun p => Real.exp (-k * p.2)) P.pre.jointLaw := by
  have h := V.pairLaw_laplace_integrable P.pre.rate_integrable
    P.pre.rate_nonneg hk (s := 0) le_rfl
  simp only [sub_zero] at h
  rw [← P.jointLaw_map_snd] at h
  exact h.comp_aemeasurable measurable_snd.aemeasurable

theorem backwardValue_sndLaplace_integral (hk : 0 < k) :
    (∫ p, Real.exp (-k * p.2) ∂P.pre.jointLaw) = V.val 0 3 := by
  have hm : AEStronglyMeasurable (fun t : ℝ => Real.exp (-k*t))
      (P.pre.jointLaw.map Prod.snd) :=
    (Real.measurable_exp.comp (measurable_id.const_mul (-k))).aestronglyMeasurable
  rw [← integral_map measurable_snd.aemeasurable hm, P.jointLaw_map_snd]
  simpa only [sub_zero] using V.pairLaw_laplace_integral P.pre.rate_integrable
    P.pre.rate_nonneg hk (s := 0) le_rfl

theorem productMutationObservable_eq_expansion (L : ℝ) (p : ℝ × ℝ) :
    productMutationObservable L k p =
      L^2 * (1 - Real.exp (-k * p.1) - Real.exp (-k * p.2) +
        Real.exp (-k * (p.1+p.2))) := by
  have he : Real.exp (-k * (p.1+p.2)) =
      Real.exp (-k * p.1) * Real.exp (-k * p.2) := by
    rw [mul_add, Real.exp_add]
  rw [he, productMutationObservable]
  ring

include V in
theorem firstMutationObservable_integrable (hk : 0 < k) (L : ℝ) :
    Integrable (firstMutationObservable L k) P.pre.jointLaw := by
  have := P.jointLaw_probability
  exact ((integrable_const (1 : ℝ)).sub
    (P.backwardValue_fstLaplace_integrable V hk)).const_mul L

include V in
theorem productMutationObservable_integrable (hk : 0 < k) (L : ℝ) :
    Integrable (productMutationObservable L k) P.pre.jointLaw := by
  have := P.jointLaw_probability
  have h := (((integrable_const (1 : ℝ)).sub
    (P.backwardValue_fstLaplace_integrable V hk)).sub
    (P.backwardValue_sndLaplace_integrable V hk)).add
    (P.pre.backwardValue_jointLaplace_integrable V hk)
  exact (h.const_mul (L^2)).congr
    (ae_of_all _ (fun p => (productMutationObservable_eq_expansion L p).symm))

theorem firstMutationObservable_integral (hk : 0 < k) (L : ℝ) :
    (∫ p, firstMutationObservable L k p ∂P.pre.jointLaw) =
      L * (1 - V.val 0 3) := by
  have := P.jointLaw_probability
  simp only [firstMutationObservable, integral_const_mul]
  rw [integral_sub (integrable_const (1 : ℝ))
    (P.backwardValue_fstLaplace_integrable V hk),
    P.backwardValue_singleLaplace_integral V hk]
  simp

theorem productMutationObservable_integral (hk : 0 < k) (L : ℝ) :
    (∫ p, productMutationObservable L k p ∂P.pre.jointLaw) =
      L^2 * (1 - 2 * V.val 0 3 + V.val 0 0) := by
  have := P.jointLaw_probability
  have h1 : Integrable (fun p : ℝ × ℝ => 1 - Real.exp (-k*p.1))
      P.pre.jointLaw := (integrable_const (1 : ℝ)).sub
        (P.backwardValue_fstLaplace_integrable V hk)
  have h2 : Integrable (fun p : ℝ × ℝ =>
      1 - Real.exp (-k*p.1) - Real.exp (-k*p.2)) P.pre.jointLaw :=
    h1.sub (P.backwardValue_sndLaplace_integrable V hk)
  simp_rw [productMutationObservable_eq_expansion]
  rw [integral_const_mul,
    integral_add h2 (P.pre.backwardValue_jointLaplace_integrable V hk),
    integral_sub h1 (P.backwardValue_sndLaplace_integrable V hk),
    integral_sub (integrable_const (1 : ℝ))
      (P.backwardValue_fstLaplace_integrable V hk),
    P.backwardValue_singleLaplace_integral V hk,
    P.backwardValue_sndLaplace_integral V hk,
    P.pre.backwardValue_jointLaplace_integral V hk]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  ring

theorem mutationMomentPair_eq_backwardValue (hk : 0 < k) (L : ℝ) :
    P.mutationMomentPair L k =
      (L * (1 - V.val 0 3), L^2 * (1 - 2 * V.val 0 3 + V.val 0 0)) := by
  exact Prod.ext (P.firstMutationObservable_integral V hk L)
    (P.productMutationObservable_integral V hk L)

theorem mutationMomentPair_integrable_and_eq (hk : 0 < k) (L : ℝ) :
    Integrable (firstMutationObservable L k) P.pre.jointLaw ∧
    Integrable (productMutationObservable L k) P.pre.jointLaw ∧
    P.mutationMomentPair L k =
      (L * (1 - V.val 0 3), L^2 * (1 - 2 * V.val 0 3 + V.val 0 0)) :=
  ⟨P.firstMutationObservable_integrable V hk L,
   P.productMutationObservable_integrable V hk L,
   P.mutationMomentPair_eq_backwardValue V hk L⟩

end ProperIntegrablePanModel
end Rhone.Statistics.Identifiability
