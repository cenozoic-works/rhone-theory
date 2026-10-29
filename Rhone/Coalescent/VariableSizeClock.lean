/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.KingmanChain
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The clock of the coalescent with a population-size function

Source: griffiths_tavare1994, sec. 2, eq. (3)–(4), p. 404. -/

@[expose] public section

namespace Rhone.Coalescent

open MeasureTheory Filter Set
open scoped Topology

noncomputable def cumIntensity (ν : ℝ → ℝ) (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, (ν s)⁻¹

structure IsSizeFunction (ν : ℝ → ℝ) : Prop where
  pos : ∀ t, 0 ≤ t → 0 < ν t
  intervalIntegrable : ∀ t, 0 ≤ t → IntervalIntegrable (fun s => (ν s)⁻¹) volume 0 t
  tendsto_atTop : Tendsto (cumIntensity ν) atTop atTop

noncomputable def cumIntensityInv (ν : ℝ → ℝ) (x : ℝ) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ x ≤ cumIntensity ν t}

variable {ν : ℝ → ℝ}

theorem cumIntensity_zero (ν : ℝ → ℝ) : cumIntensity ν 0 = 0 :=
  intervalIntegral.integral_same

theorem cumIntensity_congr {ν₁ ν₂ : ℝ → ℝ} (h : ∀ s, 0 < s → ν₁ s = ν₂ s) {t : ℝ}
    (ht : 0 ≤ t) : cumIntensity ν₁ t = cumIntensity ν₂ t := by
  unfold cumIntensity
  refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun s hs => ?_)
  rw [uIoc_of_le ht] at hs
  rw [h s hs.1]

theorem IsSizeFunction.intervalIntegrable_of_nonneg (hν : IsSizeFunction ν) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) : IntervalIntegrable (fun r => (ν r)⁻¹) volume s t :=
  (hν.intervalIntegrable s hs).symm.trans (hν.intervalIntegrable t ht)

theorem IsSizeFunction.cumIntensity_sub (hν : IsSizeFunction ν) {s t : ℝ} (hs : 0 ≤ s)
    (ht : 0 ≤ t) : cumIntensity ν t - cumIntensity ν s = ∫ r in s..t, (ν r)⁻¹ :=
  intervalIntegral.integral_interval_sub_left (hν.intervalIntegrable t ht)
    (hν.intervalIntegrable s hs)

theorem IsSizeFunction.strictMonoOn (hν : IsSizeFunction ν) :
    StrictMonoOn (cumIntensity ν) (Ici 0) := by
  intro s hs t ht hst
  have hs0 : (0 : ℝ) ≤ s := hs
  have ht0 : (0 : ℝ) ≤ t := ht
  have hpos : 0 < ∫ r in s..t, (ν r)⁻¹ :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (hν.intervalIntegrable_of_nonneg hs0 ht0)
      (fun r hr => inv_pos.2 (hν.pos r (hs0.trans hr.1.le))) hst
  rw [← hν.cumIntensity_sub hs0 ht0] at hpos
  linarith

theorem IsSizeFunction.continuousOn (hν : IsSizeFunction ν) :
    ContinuousOn (cumIntensity ν) (Ici 0) := by
  intro x hx
  have hx0 : (0 : ℝ) ≤ x := hx
  have h := intervalIntegral.continuousOn_primitive_interval' (a := 0)
    (hν.intervalIntegrable (x + 1) (by linarith)) left_mem_uIcc
  rw [uIcc_of_le (by linarith : (0 : ℝ) ≤ x + 1)] at h
  have hmem : Icc 0 (x + 1) ∈ 𝓝[Ici 0] x := by
    rw [← Ici_inter_Iic]
    exact inter_mem_nhdsWithin _ (Iic_mem_nhds (by linarith))
  exact (h x ⟨hx0, by linarith⟩).mono_of_mem_nhdsWithin hmem

theorem IsSizeFunction.cumIntensity_nonneg (hν : IsSizeFunction ν) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ cumIntensity ν t := by
  have h := hν.strictMonoOn.monotoneOn (self_mem_Ici (a := (0 : ℝ))) (mem_Ici.2 ht) ht
  rwa [cumIntensity_zero] at h

theorem cumIntensityInv_nonneg (ν : ℝ → ℝ) (x : ℝ) : 0 ≤ cumIntensityInv ν x :=
  Real.sInf_nonneg fun _ ht => ht.1

theorem bddBelow_cumIntensityInv_set (ν : ℝ → ℝ) (x : ℝ) :
    BddBelow {t : ℝ | 0 ≤ t ∧ x ≤ cumIntensity ν t} :=
  ⟨0, fun _ ht => ht.1⟩

theorem cumIntensityInv_of_nonpos (ν : ℝ → ℝ) {x : ℝ} (hx : x ≤ 0) :
    cumIntensityInv ν x = 0 :=
  le_antisymm (csInf_le (bddBelow_cumIntensityInv_set ν x)
    ⟨le_rfl, by rw [cumIntensity_zero]; exact hx⟩) (cumIntensityInv_nonneg ν x)

theorem cumIntensityInv_congr {ν₁ ν₂ : ℝ → ℝ}
    (h : ∀ t, 0 ≤ t → cumIntensity ν₁ t = cumIntensity ν₂ t) :
    cumIntensityInv ν₁ = cumIntensityInv ν₂ := by
  funext x
  unfold cumIntensityInv
  congr 1
  ext t
  constructor
  · rintro ⟨h0, hx⟩
    exact ⟨h0, by rwa [← h t h0]⟩
  · rintro ⟨h0, hx⟩
    exact ⟨h0, by rwa [h t h0]⟩

theorem IsSizeFunction.cumIntensityInv_mem (hν : IsSizeFunction ν) (x : ℝ) :
    0 ≤ cumIntensityInv ν x ∧ x ≤ cumIntensity ν (cumIntensityInv ν x) := by
  have hne : {t : ℝ | 0 ≤ t ∧ x ≤ cumIntensity ν t}.Nonempty := by
    obtain ⟨t, ht, h0⟩ := ((hν.tendsto_atTop.eventually (eventually_ge_atTop x)).and
      (eventually_ge_atTop (0 : ℝ))).exists
    exact ⟨t, h0, ht⟩
  have hcl : IsClosed {t : ℝ | 0 ≤ t ∧ x ≤ cumIntensity ν t} :=
    hν.continuousOn.preimage_isClosed_of_isClosed isClosed_Ici (isClosed_Ici (a := x))
  exact hcl.csInf_mem hne (bddBelow_cumIntensityInv_set ν x)

theorem IsSizeFunction.lt_cumIntensityInv_iff (hν : IsSizeFunction ν) {u : ℝ} (hu : 0 ≤ u)
    (x : ℝ) : u < cumIntensityInv ν x ↔ cumIntensity ν u < x := by
  constructor
  · intro h
    by_contra hx
    exact absurd (csInf_le (bddBelow_cumIntensityInv_set ν x) ⟨hu, not_lt.1 hx⟩) (not_le.2 h)
  · intro h
    by_contra hle
    obtain ⟨h0, hx⟩ := hν.cumIntensityInv_mem x
    have := hν.strictMonoOn.monotoneOn (mem_Ici.2 h0) (mem_Ici.2 hu) (not_lt.1 hle)
    linarith

theorem IsSizeFunction.cumIntensity_cumIntensityInv (hν : IsSizeFunction ν) {x : ℝ}
    (hx : 0 ≤ x) : cumIntensity ν (cumIntensityInv ν x) = x := by
  obtain ⟨h0, hle⟩ := hν.cumIntensityInv_mem x
  have hivt := intermediate_value_Icc h0 (hν.continuousOn.mono Icc_subset_Ici_self)
  obtain ⟨u, hu, hux⟩ := hivt (show x ∈ Icc (cumIntensity ν 0)
    (cumIntensity ν (cumIntensityInv ν x)) from ⟨by rw [cumIntensity_zero]; exact hx, hle⟩)
  have hsu : cumIntensityInv ν x ≤ u :=
    csInf_le (bddBelow_cumIntensityInv_set ν x) ⟨hu.1, hux.ge⟩
  rw [le_antisymm hsu hu.2]
  exact hux

theorem IsSizeFunction.cumIntensityInv_cumIntensity (hν : IsSizeFunction ν) {t : ℝ}
    (ht : 0 ≤ t) : cumIntensityInv ν (cumIntensity ν t) = t := by
  refine le_antisymm (csInf_le (bddBelow_cumIntensityInv_set ν _) ⟨ht, le_rfl⟩) ?_
  by_contra hlt
  obtain ⟨h0, hle⟩ := hν.cumIntensityInv_mem (cumIntensity ν t)
  have := hν.strictMonoOn (mem_Ici.2 h0) (mem_Ici.2 ht) (not_le.1 hlt)
  linarith

theorem IsSizeFunction.monotone_cumIntensityInv (hν : IsSizeFunction ν) :
    Monotone (cumIntensityInv ν) := by
  intro x y hxy
  obtain ⟨h0, hle⟩ := hν.cumIntensityInv_mem y
  exact csInf_le (bddBelow_cumIntensityInv_set ν x) ⟨h0, hxy.trans hle⟩

theorem IsSizeFunction.measurable_cumIntensityInv (hν : IsSizeFunction ν) :
    Measurable (cumIntensityInv ν) :=
  hν.monotone_cumIntensityInv.measurable

theorem IsSizeFunction.hasDerivAt_cumIntensity (hν : IsSizeFunction ν) {u : ℝ} (hu : 0 < u)
    (hc : ContinuousAt ν u) : HasDerivAt (cumIntensity ν) (ν u)⁻¹ u := by
  have hint : IntegrableOn (fun s => (ν s)⁻¹) (Ioc 0 (u + 1)) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).1
      (hν.intervalIntegrable (u + 1) (by linarith))
  have hmeas : StronglyMeasurableAtFilter (fun s => (ν s)⁻¹) (𝓝 u) volume :=
    ⟨Ioo 0 (u + 1), Ioo_mem_nhds hu (by linarith),
      (hint.mono_set Ioo_subset_Ioc_self).aestronglyMeasurable⟩
  exact intervalIntegral.integral_hasDerivAt_right (hν.intervalIntegrable u hu.le) hmeas
    (hc.inv₀ (hν.pos u hu.le).ne')

theorem IsSizeFunction.hasDerivAt_survival (hν : IsSizeFunction ν) (c t : ℝ) {u : ℝ}
    (hu : 0 < u) (hc : ContinuousAt ν u) :
    HasDerivAt (fun u => Real.exp (-(c * (cumIntensity ν u - cumIntensity ν t))))
      (-(c / ν u) * Real.exp (-(c * (cumIntensity ν u - cumIntensity ν t)))) u := by
  have h : HasDerivAt (fun u => -(c * (cumIntensity ν u - cumIntensity ν t)))
      (-(c * (ν u)⁻¹)) u :=
    (((hν.hasDerivAt_cumIntensity hu hc).sub_const (cumIntensity ν t)).const_mul c).neg
  convert h.exp using 1
  ring

theorem cumIntensity_one (t : ℝ) : cumIntensity (fun _ => 1) t = t := by
  simp [cumIntensity]

theorem isSizeFunction_one : IsSizeFunction (fun _ => 1) where
  pos _ _ := one_pos
  intervalIntegrable _ _ := intervalIntegrable_const
  tendsto_atTop := by
    have h : cumIntensity (fun _ => (1 : ℝ)) = id := funext cumIntensity_one
    rw [h]
    exact tendsto_id

theorem cumIntensityInv_one (x : ℝ) : cumIntensityInv (fun _ => 1) x = max 0 x := by
  unfold cumIntensityInv
  have h : {t : ℝ | 0 ≤ t ∧ x ≤ cumIntensity (fun _ => 1) t} = Ici (max 0 x) := by
    ext t
    simp [cumIntensity_one]
  rw [h, csInf_Ici]

end Rhone.Coalescent
