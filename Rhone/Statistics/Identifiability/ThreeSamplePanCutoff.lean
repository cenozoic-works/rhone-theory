/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeSampleScalarCountSeparation

/-! # Proper cutoff approximations of the three-tip ordered merger law -/

@[expose] public section

noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Rhone.Statistics.Identifiability
namespace ThreeSamplePanCutoff

def rate (f : ℝ → ℝ) (T t : ℝ) : ℝ := if t ≤ T then f t else 1

lemma nonneg {f : ℝ → ℝ} (hn : ∀ t, 0 ≤ f t) (T t : ℝ) : 0 ≤ rate f T t := by
  unfold rate
  split_ifs
  · exact hn t
  · norm_num

lemma locallyIntegrable {f : ℝ → ℝ} (hf : LocallyIntegrable f volume) (T : ℝ) :
    LocallyIntegrable (rate f T) volume := by
  have he : rate f T = (Iic T).indicator f + (Ioi T).indicator (fun _ => (1 : ℝ)) := by
    ext t
    by_cases ht : t ≤ T
    · simp [rate, ht, Pi.add_apply, not_lt.mpr ht]
    · simp [rate, ht, Pi.add_apply, lt_of_not_ge ht]
  rw [he]
  exact (hf.indicator (s := Iic T) measurableSet_Iic).add
    ((locallyIntegrable_const (1 : ℝ)).indicator (s := Ioi T) measurableSet_Ioi)

lemma clock_eq {f : ℝ → ℝ} {T t : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    integratedClock (rate f T) t = integratedClock f t := by
  unfold integratedClock
  apply intervalIntegral.integral_congr
  intro s hs
  have hsT : s ≤ T := ((show s ∈ Icc 0 t by simpa [uIcc_of_le ht] using hs).2).trans htT
  simp [rate, hsT]

lemma clock_diverges {f : ℝ → ℝ} (hf : LocallyIntegrable f volume) (T : ℝ) :
    Tendsto (integratedClock (rate f T)) atTop atTop := by
  let g := rate f T
  have hg := locallyIntegrable hf T
  have hi (u v : ℝ) := locallyIntegrable_interval g hg u v
  let a := T + 1
  have hb : ∀ t, a ≤ t →
      t + ((∫ u in (0 : ℝ)..a, g u) - a) ≤ integratedClock g t := by
    intro t ht
    have hm := intervalIntegral.integral_mono_on (μ := volume) ht
      (continuous_const.intervalIntegrable a t) (hi a t)
      (show ∀ u ∈ Icc a t, (1 : ℝ) ≤ g u from fun u hu => by
        have hTu : ¬ u ≤ T := by dsimp [a] at hu; linarith [hu.1]
        simp [g, rate, hTu])
    have ha := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hi 0 a) (hi a t)
    simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one] at hm
    change _ ≤ ∫ u in (0 : ℝ)..t, g u
    linarith
  apply tendsto_atTop_mono' atTop _
    (tendsto_atTop_add_const_right atTop ((∫ u in (0 : ℝ)..a, g u) - a) tendsto_id)
  filter_upwards [eventually_ge_atTop a] with t ht
  exact hb t ht

def beforeRoot (T : ℝ) : Set (ℝ × ℝ) := {p | p.2 ≤ T}

lemma measurableSet_beforeRoot (T : ℝ) : MeasurableSet (beforeRoot T) :=
  measurableSet_le measurable_snd measurable_const

lemma density_eq {f : ℝ → ℝ} {T : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ upperWedge) (hT : p ∈ beforeRoot T) :
    PanThreeSample.jointDensity (rate f T) p = PanThreeSample.jointDensity f p := by
  change p.2 ≤ T at hT
  have hp1 : 0 ≤ p.1 := hp.1.le
  have hp2 : 0 ≤ p.2 := (hp.1.trans hp.2).le
  have hpT : p.1 ≤ T := hp.2.le.trans hT
  rw [PanThreeSample.jointDensity_exp, PanThreeSample.jointDensity_exp,
    clock_eq hp1 hpT, clock_eq hp2 hT]
  simp only [rate, ite_eq_left hpT, ite_eq_left hT]

lemma law_restrict_eq (f : ℝ → ℝ) (T : ℝ) :
    (PanThreeSample.law (rate f T)).restrict (beforeRoot T) =
      (PanThreeSample.law f).restrict (beforeRoot T) := by
  unfold PanThreeSample.law triangularDensityLaw
  rw [restrict_withDensity (measurableSet_beforeRoot T),
    restrict_withDensity (measurableSet_beforeRoot T),
    Measure.restrict_restrict (measurableSet_beforeRoot T)]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem
    ((measurableSet_beforeRoot T).inter upperWedge_open.measurableSet)] with p hp
  rw [density_eq hp.2 hp.1]

theorem law_mass_le_one (f : ℝ → ℝ) (hf : LocallyIntegrable f volume)
    (hn : ∀ t, 0 ≤ f t) : PanThreeSample.law f univ ≤ 1 := by
  have hbound (n : ℕ) : PanThreeSample.law f (beforeRoot (n : ℝ)) ≤ 1 := by
    let : IsProbabilityMeasure (PanThreeSample.law (rate f n)) :=
      PanThreeSample.isProbability _ (locallyIntegrable hf n) (nonneg hn n)
        (clock_diverges hf n)
    have he := congrArg (fun μ : Measure (ℝ × ℝ) => μ univ) (law_restrict_eq f n)
    simp only [Measure.restrict_apply_univ] at he
    rw [← he]
    simpa only [measure_univ] using
      (measure_mono (μ := PanThreeSample.law (rate f n)) (subset_univ (beforeRoot n)))
  have hcover : (⋃ n : ℕ, beforeRoot (n : ℝ)) = univ := by
    apply eq_univ_of_forall
    intro p
    obtain ⟨n, hn⟩ := exists_nat_ge p.2
    exact mem_iUnion.mpr ⟨n, hn⟩
  have hmono : Monotone (fun n : ℕ => beforeRoot (n : ℝ)) := by
    intro m n hmn p hp
    change p.2 ≤ (m : ℝ) at hp
    change p.2 ≤ (n : ℝ)
    exact hp.trans (by exact_mod_cast hmn)
  rw [← hcover, hmono.measure_iUnion]
  exact iSup_le hbound

lemma law_isFinite (f : ℝ → ℝ) (hf : LocallyIntegrable f volume)
    (hn : ∀ t, 0 ≤ f t) : IsFiniteMeasure (PanThreeSample.law f) :=
  ⟨(law_mass_le_one f hf hn).trans_lt (by simp)⟩

end ThreeSamplePanCutoff
end Rhone.Statistics.Identifiability
