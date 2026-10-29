/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.AbsorptionProb
public import Rhone.MarkovChain.Trajectory

/-! # Absorption as a statement about trajectories -/

@[expose] public section

namespace Rhone.MarkovChain.FinChain

open MeasureTheory ProbabilityTheory Finset Filter Topology

private theorem stays_le {S : Type*} {a : S} {ω : ℕ → S} (h : ∀ n, ω n = a → ω (n + 1) = a)
    {m n : ℕ} (hmn : m ≤ n) (hm : ω m = a) : ω n = a := by
  induction n, hmn using Nat.le_induction with
  | base => exact hm
  | succ k _ ih => exact h k ih

variable {S : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  {C : FinChain S} {A : Finset S}

omit [DecidableEq S] in
theorem ae_stays {a : S} (ha : C.IsAbsorbing a) (x : S) :
    ∀ᵐ ω ∂C.pathLaw x, ∀ n, ω n = a → ω (n + 1) = a := by
  classical
  rw [ae_all_iff]
  intro n
  set g : S → ℝ := fun y => if y = a then 0 else 1 with hg
  set B : Set (ℕ → S) := {ω | ω n = a} with hB
  have hBn : MeasurableSet[Filtration.piLE (X := fun _ : ℕ => S) n] B :=
    (DiscreteProcess.measurable_eval_piLE (S := S) n) (MeasurableSet.of_discrete (s := {a}))
  have hBm : MeasurableSet B := (Filtration.piLE.le n) B hBn
  have hexp : C.expect g a = 0 := by
    rw [expect_apply]
    refine Finset.sum_eq_zero fun y _ => ?_
    by_cases hy : a = y
    · simp [hg, hy]
    · simp [ha.P_apply, hy]
  have hzero : ∫ ω in B, g (ω (n + 1)) ∂C.pathLaw x = 0 := by
    rw [C.setIntegral_eval_succ x n g hBn]
    have : ∀ ω ∈ B, C.expect g (ω n) = 0 := fun ω hω => by
      rw [show ω n = a from hω, hexp]
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

theorem pathLaw_hit_eq_absorbProb {a : S} (ha : C.IsAbsorbing a) (x : S) :
    (C.pathLaw x).real {ω | ∃ n, ω n = a} = C.absorbProb a x := by
  set F : ℕ → Set (ℕ → S) := fun n => {ω | ∃ m ≤ n, ω m = a} with hF
  have hmono : Monotone F := fun i j hij ω ⟨m, hm, h⟩ => ⟨m, hm.trans hij, h⟩
  have hU : (⋃ n, F n) = {ω : ℕ → S | ∃ n, ω n = a} := by
    ext ω
    simp only [Set.mem_iUnion, hF, Set.mem_ofPred_eq]
    exact ⟨fun ⟨_, m, _, h⟩ => ⟨m, h⟩, fun ⟨m, h⟩ => ⟨m, m, le_rfl, h⟩⟩
  have hFE : ∀ n, C.pathLaw x (F n) = C.pathLaw x {ω | ω n = a} := by
    intro n
    refine measure_congr ?_
    filter_upwards [ae_stays ha x] with ω hω
    exact propext ⟨fun ⟨m, hm, h⟩ => stays_le hω hm h, fun h => ⟨n, le_rfl, h⟩⟩
  have h1 : Tendsto (fun n => (C.pathLaw x).real (F n)) atTop
      (𝓝 ((C.pathLaw x).real (⋃ n, F n))) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp (tendsto_measure_iUnion_atTop hmono)
  have h2 : Tendsto (fun n => (C.pathLaw x).real (F n)) atTop (𝓝 (C.absorbProb a x)) := by
    refine (tendsto_stepN_absorbProb ha x).congr fun n => ?_
    rw [measureReal_def, hFE n, ← measureReal_def, C.pathLaw_real_eval]
  rw [← hU]
  exact tendsto_nhds_unique h1 h2

theorem ae_exists_mem (hA : C.IsAbsorbingSet A) (hR : C.Reaches A) (x : S) :
    ∀ᵐ ω ∂C.pathLaw x, ∃ n, ω n ∈ A := by
  have hle : ∀ n, (C.pathLaw x).real {ω | ∀ n, ω n ∉ A} ≤ C.survival A n x := by
    intro n
    rw [← C.pathLaw_real_eval_notMem n x A]
    exact measureReal_mono fun ω hω => hω n
  have h0 : (C.pathLaw x).real {ω | ∀ n, ω n ∉ A} ≤ 0 :=
    ge_of_tendsto' (tendsto_survival hA hR x) hle
  have h0' : C.pathLaw x {ω | ∀ n, ω n ∉ A} = 0 :=
    (measureReal_eq_zero_iff (measure_ne_top _ _)).1 (le_antisymm h0 measureReal_nonneg)
  rw [ae_iff]
  convert h0' using 2
  ext ω
  simp

theorem ae_eventually_const (hA : C.IsAbsorbingSet A) (hR : C.Reaches A) (x : S) :
    ∀ᵐ ω ∂C.pathLaw x, ∃ a ∈ A, ∃ n, ∀ m, n ≤ m → ω m = a := by
  have hstay : ∀ᵐ ω ∂C.pathLaw x, ∀ a ∈ A, ∀ n, ω n = a → ω (n + 1) = a :=
    (eventually_all_finset A).2 fun a ha => ae_stays (hA a ha) x
  filter_upwards [hstay, ae_exists_mem hA hR x] with ω hs ⟨n, hn⟩
  exact ⟨ω n, hn, n, fun m hm => stays_le (hs (ω n) hn) hm rfl⟩

omit [DecidableEq S] in
theorem pathLaw_absorbed_eq_hit {a : S} (ha : C.IsAbsorbing a) (x : S) :
    (C.pathLaw x).real {ω | ∃ n, ∀ m, n ≤ m → ω m = a} =
      (C.pathLaw x).real {ω | ∃ n, ω n = a} := by
  rw [measureReal_def, measureReal_def]
  congr 1
  refine measure_congr ?_
  filter_upwards [ae_stays ha x] with ω hω
  exact propext ⟨fun ⟨n, h⟩ => ⟨n, h n le_rfl⟩, fun ⟨n, h⟩ => ⟨n, fun m hm => stays_le hω hm h⟩⟩

theorem pathLaw_hit_eq_of_isHarmonic (hA : C.IsAbsorbingSet A) (hR : C.Reaches A) {a : S}
    (ha : a ∈ A) {h : S → ℝ} (hh : C.IsHarmonic h) (h1 : h a = 1)
    (h0 : ∀ b ∈ A, b ≠ a → h b = 0) (x : S) :
    (C.pathLaw x).real {ω | ∃ n, ω n = a} = h x := by
  rw [pathLaw_hit_eq_absorbProb (hA a ha), absorbProb_eq_of_isHarmonic hA hR ha hh h1 h0]

theorem pathLaw_absorbed_eq_of_isHarmonic (hA : C.IsAbsorbingSet A) (hR : C.Reaches A) {a : S}
    (ha : a ∈ A) {h : S → ℝ} (hh : C.IsHarmonic h) (h1 : h a = 1)
    (h0 : ∀ b ∈ A, b ≠ a → h b = 0) (x : S) :
    (C.pathLaw x).real {ω | ∃ n, ∀ m, n ≤ m → ω m = a} = h x := by
  rw [pathLaw_absorbed_eq_hit (hA a ha), pathLaw_hit_eq_of_isHarmonic hA hR ha hh h1 h0]

end Rhone.MarkovChain.FinChain
