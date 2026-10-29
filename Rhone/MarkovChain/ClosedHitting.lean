/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.ClosedSet
public import Rhone.MarkovChain.HittingTime

/-! # Absorption into a closed set, for trajectories -/

@[expose] public section

namespace Rhone.MarkovChain.FinChain

open MeasureTheory ProbabilityTheory Finset Filter Topology
open scoped ENNReal

private theorem mem_of_le {S : Type*} {A : Finset S} {ω : ℕ → S}
    (h : ∀ n, ω n ∈ A → ω (n + 1) ∈ A) {m n : ℕ} (hmn : m ≤ n) (hm : ω m ∈ A) : ω n ∈ A := by
  induction n, hmn using Nat.le_induction with
  | base => exact hm
  | succ k _ ih => exact h k ih

variable {S : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  {C : FinChain S} {A : Finset S}

omit [DecidableEq S] in
theorem IsClosedSet.ae_stays_mem (hA : C.IsClosedSet A) (x : S) :
    ∀ᵐ ω ∂C.pathLaw x, ∀ n, ω n ∈ A → ω (n + 1) ∈ A := by
  classical
  rw [ae_all_iff]
  intro n
  set g : S → ℝ := fun y => if y ∈ A then 0 else 1 with hg
  set B : Set (ℕ → S) := {ω | ω n ∈ A} with hB
  have hBn : MeasurableSet[Filtration.piLE (X := fun _ : ℕ => S) n] B :=
    (DiscreteProcess.measurable_eval_piLE (S := S) n)
      (MeasurableSet.of_discrete (s := (A : Set S)))
  have hBm : MeasurableSet B := (Filtration.piLE.le n) B hBn
  have hexp : ∀ a ∈ A, C.expect g a = 0 := fun a ha =>
    hA.expect_eq_of_const (h := g) (fun b hb => by simp [hg, hb]) ha
  have hzero : ∫ ω in B, g (ω (n + 1)) ∂C.pathLaw x = 0 := by
    rw [C.setIntegral_eval_succ x n g hBn]
    have : ∀ ω ∈ B, C.expect g (ω n) = 0 := fun ω hω => hexp (ω n) hω
    rw [setIntegral_congr_fun hBm this, integral_zero]
  have hnn : 0 ≤ᵐ[(C.pathLaw x).restrict B] fun ω : ℕ → S => g (ω (n + 1)) :=
    Eventually.of_forall fun ω => by
      simp only [hg, Pi.zero_apply]
      split_ifs <;> norm_num
  have hint : IntegrableOn (fun ω : ℕ → S => g (ω (n + 1))) B (C.pathLaw x) :=
    (Integrable.of_bound
      ((Measurable.of_discrete (f := g)).comp (measurable_pi_apply (n + 1))).aestronglyMeasurable
      1 (Eventually.of_forall fun ω => by
        simp only [hg, Real.norm_eq_abs, Function.comp_apply]
        split_ifs <;> norm_num)).integrableOn
  have hae := (setIntegral_eq_zero_iff_of_nonneg_ae hnn hint).1 hzero
  rw [EventuallyEq, ae_restrict_iff' hBm] at hae
  filter_upwards [hae] with ω hω hωn
  by_contra hne
  have := hω hωn
  simp [hg, hne] at this

theorem IsClosedSet.pathLaw_enter_eq_enterProb (hA : C.IsClosedSet A) (x : S) :
    (C.pathLaw x).real {ω | ∃ n, ω n ∈ A} = C.enterProb A x := by
  set F : ℕ → Set (ℕ → S) := fun n => {ω | ∃ m ≤ n, ω m ∈ A} with hF
  have hmono : Monotone F := fun i j hij ω ⟨m, hm, h⟩ => ⟨m, hm.trans hij, h⟩
  have hU : (⋃ n, F n) = {ω : ℕ → S | ∃ n, ω n ∈ A} := by
    ext ω
    simp only [Set.mem_iUnion, hF, Set.mem_ofPred_eq]
    exact ⟨fun ⟨_, m, _, h⟩ => ⟨m, h⟩, fun ⟨m, h⟩ => ⟨m, m, le_rfl, h⟩⟩
  have hFE : ∀ n, C.pathLaw x (F n) = C.pathLaw x {ω | ω n ∈ A} := by
    intro n
    refine measure_congr ?_
    filter_upwards [hA.ae_stays_mem x] with ω hω
    exact propext ⟨fun ⟨m, hm, h⟩ => mem_of_le hω hm h, fun h => ⟨n, le_rfl, h⟩⟩
  have h1 : Tendsto (fun n => (C.pathLaw x).real (F n)) atTop
      (𝓝 ((C.pathLaw x).real (⋃ n, F n))) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp (tendsto_measure_iUnion_atTop hmono)
  have h2 : Tendsto (fun n => (C.pathLaw x).real (F n)) atTop (𝓝 (C.enterProb A x)) := by
    refine (hA.tendsto_enterProb x).congr fun n => ?_
    rw [measureReal_def, hFE n, ← measureReal_def, C.pathLaw_real_eval_mem]
  rw [← hU]
  exact tendsto_nhds_unique h1 h2

theorem IsClosedSet.ae_exists_mem (hA : C.IsClosedSet A) (hR : C.Reaches A) (x : S) :
    ∀ᵐ ω ∂C.pathLaw x, ∃ n, ω n ∈ A := by
  have hle : ∀ n, (C.pathLaw x).real {ω | ∀ n, ω n ∉ A} ≤ C.survival A n x := by
    intro n
    rw [← C.pathLaw_real_eval_notMem n x A]
    exact measureReal_mono fun ω hω => hω n
  have h0 : (C.pathLaw x).real {ω | ∀ n, ω n ∉ A} ≤ 0 :=
    ge_of_tendsto' (hA.tendsto_survival hR x) hle
  have h0' : C.pathLaw x {ω | ∀ n, ω n ∉ A} = 0 :=
    (measureReal_eq_zero_iff (measure_ne_top _ _)).1 (le_antisymm h0 measureReal_nonneg)
  rw [ae_iff]
  convert h0' using 2
  ext ω
  simp

theorem IsClosedSet.ae_eventually_mem (hA : C.IsClosedSet A) (hR : C.Reaches A) (x : S) :
    ∀ᵐ ω ∂C.pathLaw x, ∃ n, ∀ m, n ≤ m → ω m ∈ A := by
  filter_upwards [hA.ae_stays_mem x, hA.ae_exists_mem hR x] with ω hs ⟨n, hn⟩
  exact ⟨n, fun m hm => mem_of_le hs hm hn⟩

omit [DecidableEq S] in
theorem IsClosedSet.pathLaw_eventually_mem_eq_enter (hA : C.IsClosedSet A) (x : S) :
    (C.pathLaw x).real {ω | ∃ n, ∀ m, n ≤ m → ω m ∈ A} =
      (C.pathLaw x).real {ω | ∃ n, ω n ∈ A} := by
  rw [measureReal_def, measureReal_def]
  congr 1
  refine measure_congr ?_
  filter_upwards [hA.ae_stays_mem x] with ω hω
  exact propext ⟨fun ⟨n, h⟩ => ⟨n, h n le_rfl⟩, fun ⟨n, h⟩ => ⟨n, fun m hm => mem_of_le hω hm h⟩⟩

theorem pathLaw_enter_eq_of_harmonicOff {A₁ A₀ : Finset S} (hA₁ : C.IsClosedSet A₁)
    (hA₀ : C.IsClosedSet A₀) (hd : Disjoint A₁ A₀) (hR : C.Reaches (A₁ ∪ A₀)) {h : S → ℝ}
    (hh : ∀ x, x ∉ A₁ ∪ A₀ → C.expect h x = h x) (h1 : ∀ a ∈ A₁, h a = 1)
    (h0 : ∀ a ∈ A₀, h a = 0) (x : S) :
    (C.pathLaw x).real {ω | ∃ n, ω n ∈ A₁} = h x := by
  rw [hA₁.pathLaw_enter_eq_enterProb, enterProb_eq_of_harmonicOff hA₁ hA₀ hd hR hh h1 h0]

theorem pathLaw_eventually_mem_eq_of_harmonicOff {A₁ A₀ : Finset S} (hA₁ : C.IsClosedSet A₁)
    (hA₀ : C.IsClosedSet A₀) (hd : Disjoint A₁ A₀) (hR : C.Reaches (A₁ ∪ A₀)) {h : S → ℝ}
    (hh : ∀ x, x ∉ A₁ ∪ A₀ → C.expect h x = h x) (h1 : ∀ a ∈ A₁, h a = 1)
    (h0 : ∀ a ∈ A₀, h a = 0) (x : S) :
    (C.pathLaw x).real {ω | ∃ n, ∀ m, n ≤ m → ω m ∈ A₁} = h x := by
  rw [hA₁.pathLaw_eventually_mem_eq_enter,
    pathLaw_enter_eq_of_harmonicOff hA₁ hA₀ hd hR hh h1 h0]

theorem IsClosedSet.lintegral_pathCost (hA : C.IsClosedSet A) (hR : C.Reaches A) {c : S → ℝ}
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
    (hA.summable_potential hR c x)]

theorem IsClosedSet.lintegral_hitTime (hA : C.IsClosedSet A) (hR : C.Reaches A) (x : S) :
    ∫⁻ ω, (hitTime A ω : ℝ≥0∞) ∂C.pathLaw x = ENNReal.ofReal (C.absorbTime A x) := by
  have hae : (fun ω : ℕ → S => (hitTime A ω : ℝ≥0∞)) =ᵐ[C.pathLaw x]
      fun ω => pathCost A (fun _ => 1) ω := by
    filter_upwards [hA.ae_stays_mem x] with ω hω
    exact (pathCost_one_eq_hitTime hω).symm
  rw [lintegral_congr_ae hae, hA.lintegral_pathCost hR (fun _ => zero_le_one) x,
    absorbTime_eq_potential]

theorem IsClosedSet.ae_hitTime_ne_top (hA : C.IsClosedSet A) (hR : C.Reaches A) (x : S) :
    ∀ᵐ ω ∂C.pathLaw x, hitTime A ω ≠ ⊤ := by
  filter_upwards [hA.ae_exists_mem hR x] with ω ⟨n, hn⟩ htop
  exact hitTime_eq_top_iff.1 htop n hn

end Rhone.MarkovChain.FinChain
