/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegrableRiccati

/-! # Observable ODEs with locally integrable coefficients -/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability

set_option backward.isDefEq.respectTransparency false

theorem exists_integrable_observable_G (rate delta : ℝ → ℝ)
    (hr : LocallyIntegrableOn rate (Ici 0) volume)
    (hd : LocallyIntegrableOn delta (Ici 0) volume)
    (hdn : ∀ᵐ t, 0 ≤ t → 0 ≤ delta t) :
    ∃ G : ℝ → ℝ, G 0 = 1 ∧ Continuous G ∧
      (∀ a b, AbsolutelyContinuousOnInterval G a b) ∧
      (∀ t, 0 ≤ t → 0 < G t) ∧
      (∀ᵐ t, 0 ≤ t → HasDerivAt G (delta t - 2 * rate t * G t) t) := by
  have hp : LocallyIntegrableOn (fun t => 2 * rate t) (Ici 0) volume := hr.smul (2 : ℝ)
  obtain ⟨G, hG0, hGc, hGa, hGn, hGd⟩ := exists_halfLine_integrable_riccati_solution
    delta (fun t => 2 * rate t) (fun _ => 0) hd hp (locallyIntegrableOn_const 0)
    hdn (Filter.Eventually.of_forall (fun _ _ => le_rfl)) 1 (by norm_num)
  refine ⟨G, hG0, hGc, hGa, hGn, ?_⟩
  filter_upwards [hGd] with t ht ht0
  simpa only [zero_mul, sub_zero] using ht ht0

theorem exists_integrable_observable_Z (rate delta a G : ℝ → ℝ)
    (hr : LocallyIntegrableOn rate (Ici 0) volume)
    (hd : LocallyIntegrableOn delta (Ici 0) volume)
    (ha : LocallyIntegrableOn a (Ici 0) volume)
    (han : ∀ᵐ t, 0 ≤ t → 0 ≤ a t)
    (hGc : ContinuousOn G (Ici 0)) (hGn : ∀ t, 0 ≤ t → 0 ≤ G t) :
    ∃ Z : ℝ → ℝ, Z 0 = 2 ∧ Continuous Z ∧
      (∀ u v, AbsolutelyContinuousOnInterval Z u v) ∧
      (∀ t, 0 ≤ t → 0 < Z t) ∧
      (∀ᵐ t, 0 ≤ t → HasDerivAt Z
        (4 * a t * G t + 4 * Real.sqrt (rate t * delta t) -
          (7 / 2) * rate t * Z t - (a t / 2) * (Z t) ^ 2) t) := by
  let b : ℝ → ℝ := fun t => Real.sqrt (rate t * delta t)
  let q : ℝ → ℝ := fun t => 4 * a t * G t + 4 * b t
  let p : ℝ → ℝ := fun t => (7 / 2) * rate t
  let r : ℝ → ℝ := fun t => a t / 2
  have hb : LocallyIntegrableOn b (Ici 0) volume := sqrt_mul_locallyIntegrableOn hr hd
  have hq : LocallyIntegrableOn q (Ici 0) volume := by
    have h := ((ha.mul_continuousOn hGc isClosed_Ici.isLocallyClosed).smul (4 : ℝ)).add (hb.smul
        (4 : ℝ))
    convert! h using 1
    ext t
    simp only [q, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hp : LocallyIntegrableOn p (Ici 0) volume := hr.smul (7 / 2 : ℝ)
  have hi : LocallyIntegrableOn r (Ici 0) volume := by
    convert! ha.smul (2⁻¹ : ℝ) using 1
    ext t
    simp only [r, Pi.smul_apply, smul_eq_mul]
    ring
  have hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t := by
    filter_upwards [han] with t ht ht0
    exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (ht ht0)) (hGn t ht0))
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
  have hrn : ∀ᵐ t, 0 ≤ t → 0 ≤ r t := by
    filter_upwards [han] with t ht ht0
    exact div_nonneg (ht ht0) (by norm_num)
  exact exists_halfLine_integrable_riccati_solution q p r hq hp hi hqn hrn 2 (by norm_num)

theorem exists_integrable_pan_observables (rate delta a : ℝ → ℝ)
    (hr : LocallyIntegrableOn rate (Ici 0) volume)
    (hd : LocallyIntegrableOn delta (Ici 0) volume)
    (ha : LocallyIntegrableOn a (Ici 0) volume)
    (hdn : ∀ᵐ t, 0 ≤ t → 0 ≤ delta t)
    (han : ∀ᵐ t, 0 ≤ t → 0 ≤ a t) :
    ∃ G Z : ℝ → ℝ, G 0 = 1 ∧ Z 0 = 2 ∧ Continuous G ∧ Continuous Z ∧
      (∀ u v, AbsolutelyContinuousOnInterval G u v) ∧
      (∀ u v, AbsolutelyContinuousOnInterval Z u v) ∧
      (∀ t, 0 ≤ t → 0 < G t) ∧ (∀ t, 0 ≤ t → 0 < Z t) ∧
      (∀ᵐ t, 0 ≤ t → HasDerivAt G (delta t - 2 * rate t * G t) t) ∧
      (∀ᵐ t, 0 ≤ t → HasDerivAt Z
        (4 * a t * G t + 4 * Real.sqrt (rate t * delta t) -
          (7 / 2) * rate t * Z t - (a t / 2) * (Z t) ^ 2) t) := by
  obtain ⟨G, hG0, hGc, hGa, hGn, hGd⟩ := exists_integrable_observable_G rate delta hr hd hdn
  obtain ⟨Z, hZ0, hZc, hZa, hZn, hZd⟩ := exists_integrable_observable_Z rate delta a G
    hr hd ha han hGc.continuousOn (fun t ht => (hGn t ht).le)
  exact ⟨G, Z, hG0, hZ0, hGc, hZc, hGa, hZa, hGn, hZn, hGd, hZd⟩

theorem integrable_observable_G_unique (rate delta G H : ℝ → ℝ)
    (hr : LocallyIntegrableOn rate (Ici 0) volume)
    (hGc : ContinuousOn G (Ici 0)) (hHc : ContinuousOn H (Ici 0))
    (hGa : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval G 0 T)
    (hHa : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval H 0 T)
    (hGd : ∀ᵐ t, 0 ≤ t → HasDerivAt G (delta t - 2 * rate t * G t) t)
    (hHd : ∀ᵐ t, 0 ≤ t → HasDerivAt H (delta t - 2 * rate t * H t) t)
    (hzero : G 0 = H 0) : ∀ t, 0 ≤ t → G t = H t := by
  apply integrable_riccati_solution_unique delta (fun t => 2 * rate t) (fun _ => 0)
    G H (hr.smul (2 : ℝ)) (locallyIntegrableOn_const 0) hGc hHc hGa hHa
    _ _ hzero
  · simpa only [zero_mul, sub_zero] using hGd
  · simpa only [zero_mul, sub_zero] using hHd

theorem integrable_observable_Z_unique (rate delta a G Z W : ℝ → ℝ)
    (hr : LocallyIntegrableOn rate (Ici 0) volume)
    (ha : LocallyIntegrableOn a (Ici 0) volume)
    (hZc : ContinuousOn Z (Ici 0)) (hWc : ContinuousOn W (Ici 0))
    (hZa : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval Z 0 T)
    (hWa : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval W 0 T)
    (hZd : ∀ᵐ t, 0 ≤ t → HasDerivAt Z
      (4 * a t * G t + 4 * Real.sqrt (rate t * delta t) -
        (7 / 2) * rate t * Z t - (a t / 2) * (Z t) ^ 2) t)
    (hWd : ∀ᵐ t, 0 ≤ t → HasDerivAt W
      (4 * a t * G t + 4 * Real.sqrt (rate t * delta t) -
        (7 / 2) * rate t * W t - (a t / 2) * (W t) ^ 2) t)
    (hzero : Z 0 = W 0) : ∀ t, 0 ≤ t → Z t = W t := by
  have hi : LocallyIntegrableOn (fun t => a t / 2) (Ici 0) volume := by
    convert! ha.smul (2⁻¹ : ℝ) using 1
    ext t
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  exact integrable_riccati_solution_unique
    (fun t => 4 * a t * G t + 4 * Real.sqrt (rate t * delta t))
    (fun t => (7 / 2) * rate t) (fun t => a t / 2) Z W
    (hr.smul (7 / 2 : ℝ)) hi hZc hWc hZa hWa hZd hWd hzero

end Rhone.Statistics.Identifiability
