/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.Hitting

/-! # Hitting times and costs collected before absorption -/

@[expose] public section

namespace Rhone.MarkovChain

open MeasureTheory ProbabilityTheory Finset Filter
open scoped ENNReal

variable {S : Type*}

open Classical in
noncomputable def hitTime (A : Finset S) (ω : ℕ → S) : ℕ∞ :=
  if h : ∃ n, ω n ∈ A then (Nat.find h : ℕ∞) else ⊤

noncomputable def pathCost [DecidableEq S] (A : Finset S) (c : S → ℝ) (ω : ℕ → S) : ℝ≥0∞ :=
  ∑' n, if ω n ∈ A then 0 else ENNReal.ofReal (c (ω n))

theorem hitTime_eq_top_iff {A : Finset S} {ω : ℕ → S} : hitTime A ω = ⊤ ↔ ∀ n, ω n ∉ A := by
  classical
  unfold hitTime
  split_ifs with h
  · simp only [ENat.natCast_ne_top, false_iff, not_forall, not_not]
    exact h
  · simpa using h

open Classical in
theorem hitTime_eq_natCast {A : Finset S} {ω : ℕ → S} (h : ∃ n, ω n ∈ A) :
    ∃ k : ℕ, hitTime A ω = k ∧ ω k ∈ A ∧ ∀ n, n < k → ω n ∉ A := by
  unfold hitTime
  rw [dite_eq_left h]
  exact ⟨_, rfl, Nat.find_spec h, fun n hn => Nat.find_min h hn⟩

theorem pathCost_one_eq_hitTime [DecidableEq S] {A : Finset S} {ω : ℕ → S}
    (hstay : ∀ n, ω n ∈ A → ω (n + 1) ∈ A) :
    pathCost A (fun _ => 1) ω = (hitTime A ω : ℝ≥0∞) := by
  unfold pathCost
  by_cases h : ∃ n, ω n ∈ A
  · obtain ⟨k, hk, hspec, hlt⟩ := hitTime_eq_natCast h
    rw [hk]
    have hge : ∀ n, k ≤ n → ω n ∈ A := by
      intro n hn
      induction n, hn using Nat.le_induction with
      | base => exact hspec
      | succ m _ ih => exact hstay m ih
    have hterm : ∀ n, (if ω n ∈ A then (0 : ℝ≥0∞) else ENNReal.ofReal 1) =
        if n ∈ Finset.range k then 1 else 0 := by
      intro n
      by_cases hn : n < k
      · simp [hlt n hn, hn]
      · simp [hge n (not_lt.1 hn), hn]
    simp only [hterm]
    rw [tsum_eq_sum (s := Finset.range k) (fun n hn => by simp [hn]),
      Finset.sum_congr rfl fun n hn => ite_eq_left hn]
    simp
  · have hall : ∀ n, ω n ∉ A := by simpa using h
    rw [hitTime_eq_top_iff.2 hall]
    simp [hall]

namespace FinChain

variable [Fintype S] [DecidableEq S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  {C : FinChain S} {A : Finset S}

theorem lintegral_pathCost (hA : C.IsAbsorbingSet A) (hR : C.Reaches A) {c : S → ℝ}
    (hc : ∀ y, 0 ≤ c y) (x : S) :
    ∫⁻ ω, pathCost A c ω ∂C.pathLaw x = ENNReal.ofReal (C.potential A c x) := by
  set g : S → ℝ := fun y => if y ∈ A then 0 else c y with hg
  have hg0 : ∀ y, 0 ≤ g y := fun y => by
    simp only [hg]
    split_ifs
    · exact le_rfl
    · exact hc y
  have hterm : ∀ n, ∫⁻ ω, (if ω n ∈ A then 0 else ENNReal.ofReal (c (ω n))) ∂C.pathLaw x
      = ENNReal.ofReal (∑ y ∈ Aᶜ, C.stepN n x y * c y) := by
    intro n
    have e1 : ∀ ω : ℕ → S, (if ω n ∈ A then (0 : ℝ≥0∞) else ENNReal.ofReal (c (ω n))) =
        ENNReal.ofReal (g (ω n)) := by
      intro ω
      simp only [hg]
      split_ifs <;> simp
    have hsum : C.expectN n g x = ∑ y ∈ Aᶜ, C.stepN n x y * c y := by
      rw [expectN_apply, ← Finset.sum_add_sum_compl A]
      have hA0 : ∑ y ∈ A, C.stepN n x y * g y = 0 :=
        Finset.sum_eq_zero fun y hy => by simp [hg, hy]
      rw [hA0, zero_add]
      exact Finset.sum_congr rfl fun y hy => by simp [hg, Finset.mem_compl.1 hy]
    simp only [e1]
    rw [← ofReal_integral_eq_lintegral_ofReal (C.integrable_eval g n x)
      (Eventually.of_forall fun ω => hg0 (ω n)), C.integral_eval, hsum]
  have hmeas : ∀ n, AEMeasurable
      (fun ω : ℕ → S => if ω n ∈ A then (0 : ℝ≥0∞) else ENNReal.ofReal (c (ω n)))
      (C.pathLaw x) := fun n => ((Measurable.of_discrete
    (f := fun y : S => if y ∈ A then (0 : ℝ≥0∞) else ENNReal.ofReal (c y))).comp
    (measurable_pi_apply n)).aemeasurable
  unfold pathCost
  rw [lintegral_tsum hmeas]
  simp only [hterm]
  rw [potential, ENNReal.ofReal_tsum_of_nonneg
    (fun n => Finset.sum_nonneg fun y _ => mul_nonneg (C.stepN_nonneg n x y) (hc y))
    (summable_potential hA hR c x)]

omit [DecidableEq S] in
theorem ae_stays_mem (hA : C.IsAbsorbingSet A) (x : S) :
    ∀ᵐ ω ∂C.pathLaw x, ∀ n, ω n ∈ A → ω (n + 1) ∈ A := by
  have hstay : ∀ᵐ ω ∂C.pathLaw x, ∀ a ∈ A, ∀ n, ω n = a → ω (n + 1) = a :=
    (eventually_all_finset A).2 fun a ha => ae_stays (hA a ha) x
  filter_upwards [hstay] with ω hω n hn
  rw [hω (ω n) hn n rfl]
  exact hn

theorem lintegral_hitTime (hA : C.IsAbsorbingSet A) (hR : C.Reaches A) (x : S) :
    ∫⁻ ω, (hitTime A ω : ℝ≥0∞) ∂C.pathLaw x = ENNReal.ofReal (C.absorbTime A x) := by
  have hae : (fun ω : ℕ → S => (hitTime A ω : ℝ≥0∞)) =ᵐ[C.pathLaw x]
      fun ω => pathCost A (fun _ => 1) ω := by
    filter_upwards [ae_stays_mem hA x] with ω hω
    exact (pathCost_one_eq_hitTime hω).symm
  rw [lintegral_congr_ae hae, lintegral_pathCost hA hR (fun _ => zero_le_one) x,
    absorbTime_eq_potential]

theorem ae_hitTime_ne_top (hA : C.IsAbsorbingSet A) (hR : C.Reaches A) (x : S) :
    ∀ᵐ ω ∂C.pathLaw x, hitTime A ω ≠ ⊤ := by
  filter_upwards [ae_exists_mem hA hR x] with ω ⟨n, hn⟩ htop
  exact hitTime_eq_top_iff.1 htop n hn

end FinChain

end Rhone.MarkovChain
