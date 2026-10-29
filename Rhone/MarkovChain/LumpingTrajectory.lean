/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.Lumping
public import Rhone.MarkovChain.Trajectory
public import Mathlib.MeasureTheory.Constructions.Projective

/-! # The trajectory law of a lumped chain -/

@[expose] public section

namespace Rhone.MarkovChain

open MeasureTheory ProbabilityTheory Finset

theorem measure_ext_of_cylinder {T : Type*} [MeasurableSpace T] [MeasurableSingletonClass T]
    [Countable T] {μ ν : Measure (ℕ → T)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ (n : ℕ) (z : ℕ → T),
      μ {ω | ∀ i ≤ n, ω i = z i} = ν {ω | ∀ i ≤ n, ω i = z i}) : μ = ν := by
  have hIic : ∀ n : ℕ, μ.map (Finset.Iic n).restrict = ν.map (Finset.Iic n).restrict := by
    intro n
    refine Measure.ext_of_singleton fun y => ?_
    rw [Measure.map_apply (Finset.measurable_restrict _) (measurableSet_singleton y),
      Measure.map_apply (Finset.measurable_restrict _) (measurableSet_singleton y)]
    set z : ℕ → T := fun i => y ⟨min i n, Finset.mem_Iic.2 (min_le_right i n)⟩ with hz
    have hset : (Finset.Iic n).restrict ⁻¹' ({y} : Set ((i : Finset.Iic n) → T)) =
        {ω : ℕ → T | ∀ i ≤ n, ω i = z i} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
      constructor
      · rintro rfl i hi
        change ω i = ω (min i n)
        rw [min_eq_left hi]
      · intro hω
        funext i
        have hi' : (i : ℕ) ≤ n := Finset.mem_Iic.1 i.2
        change ω i = y i
        rw [hω i hi', hz]
        exact congrArg y (Subtype.ext (min_eq_left hi'))
    rw [hset, h n z]
  refine IsProjectiveLimit.unique (P := fun I => ν.map I.restrict) (fun I => ?_) fun I => rfl
  have hn : I ⊆ Finset.Iic (I.sup id) := fun i hi =>
    Finset.mem_Iic.2 (Finset.le_sup (f := id) hi)
  have hcomp : (I.restrict : (ℕ → T) → _) =
      Finset.restrict₂ hn ∘ (Finset.Iic (I.sup id)).restrict := rfl
  change μ.map I.restrict = ν.map I.restrict
  rw [hcomp, ← Measure.map_map (Finset.measurable_restrict₂ hn) (Finset.measurable_restrict _),
    hIic, Measure.map_map (Finset.measurable_restrict₂ hn) (Finset.measurable_restrict _)]

namespace FinChain

private theorem cylinder_succ {S T : Type*} (f : S → T) (z : ℕ → T) (n : ℕ) :
    {ω : ℕ → S | ∀ i ≤ n + 1, f (ω i) = z i} =
      {ω | ∀ i ≤ n, f (ω i) = z i} ∩ {ω | f (ω (n + 1)) = z (n + 1)} := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
  constructor
  · exact fun h => ⟨fun i hi => h i (Nat.le_succ_of_le hi), h (n + 1) le_rfl⟩
  · rintro ⟨h1, h2⟩ i hi
    rcases Nat.le_or_eq_of_le_succ hi with h | h
    · exact h1 i h
    · rw [h]
      exact h2

private theorem measurableSet_cylinder {S T : Type*} [MeasurableSpace S]
    [DiscreteMeasurableSpace S] (f : S → T) (z : ℕ → T) (n : ℕ) :
    MeasurableSet[Filtration.piLE (X := fun _ : ℕ => S) n]
      {ω : ℕ → S | ∀ i ≤ n, f (ω i) = z i} := by
  induction n with
  | zero =>
    have h : {ω : ℕ → S | ∀ i ≤ 0, f (ω i) = z i} = (fun ω => ω 0) ⁻¹' {s | f s = z 0} := by
      ext ω
      simp
    rw [h]
    exact DiscreteProcess.measurable_eval_piLE (S := S) 0
      (MeasurableSet.of_discrete (s := {s | f s = z 0}))
  | succ n ih =>
    rw [cylinder_succ]
    exact MeasurableSet.inter
      ((Filtration.piLE (X := fun _ : ℕ => S)).mono (Nat.le_succ n) _ ih)
      (DiscreteProcess.measurable_eval_piLE (S := S) (n + 1)
        (MeasurableSet.of_discrete (s := {s | f s = z (n + 1)})))

variable {S T : Type*} [Fintype S] [Fintype T] [DecidableEq T] [MeasurableSpace S]
  [DiscreteMeasurableSpace S] {C : FinChain S} {f : S → T} {D : FinChain T}

theorem Lumps.pathLaw_real_cylinder (hL : C.Lumps f D) (x : S) (z : ℕ → T) (n : ℕ) :
    (C.pathLaw x).real {ω | ∀ i ≤ n, f (ω i) = z i} =
      (if f x = z 0 then 1 else 0) * ∏ i ∈ range n, D.P (z i) (z (i + 1)) := by
  classical
  induction n with
  | zero =>
    have hset : {ω : ℕ → S | ∀ i ≤ 0, f (ω i) = z i} =
        {ω | ω 0 ∈ univ.filter fun s => f s = z 0} := by
      ext ω
      simp
    rw [hset, C.pathLaw_real_eval_mem, stepN_zero]
    simp [Matrix.one_apply, Finset.sum_ite_eq, Finset.mem_filter]
  | succ n ih =>
    set B : Set (ℕ → S) := {ω | ∀ i ≤ n, f (ω i) = z i} with hB
    have hBn : MeasurableSet[Filtration.piLE (X := fun _ : ℕ => S) n] B :=
      measurableSet_cylinder f z n
    have hBm : MeasurableSet B := (Filtration.piLE.le n) B hBn
    set g : S → ℝ := fun s => if f s = z (n + 1) then 1 else 0 with hg
    have hE : MeasurableSet {ω : ℕ → S | f (ω (n + 1)) = z (n + 1)} := by
      change MeasurableSet ((fun ω : ℕ → S => ω (n + 1)) ⁻¹' {s | f s = z (n + 1)})
      exact measurable_pi_apply (n + 1) (MeasurableSet.of_discrete (s := {s | f s = z (n + 1)}))
    have h1 : (C.pathLaw x).real (B ∩ {ω | f (ω (n + 1)) = z (n + 1)}) =
        ∫ ω in B, g (ω (n + 1)) ∂C.pathLaw x := by
      have hind : (fun ω : ℕ → S => g (ω (n + 1))) =
          Set.indicator {ω : ℕ → S | f (ω (n + 1)) = z (n + 1)} fun _ => (1 : ℝ) := by
        funext ω
        simp [hg, Set.indicator]
      rw [hind, setIntegral_indicator hE, setIntegral_const, smul_eq_mul, mul_one]
    have h2 : ∀ ω ∈ B, C.expect g (ω n) = D.P (z n) (z (n + 1)) := by
      intro ω hω
      have h3 := congrFun (hL.expect_comp fun t => if t = z (n + 1) then (1 : ℝ) else 0) (ω n)
      have h4 : D.expect (fun t => if t = z (n + 1) then (1 : ℝ) else 0) (f (ω n)) =
          D.P (f (ω n)) (z (n + 1)) := by
        simp [expect_apply]
      rw [← hω n le_rfl, ← h4]
      exact h3
    rw [cylinder_succ, h1, C.setIntegral_eval_succ x n g hBn, setIntegral_congr_fun hBm h2,
      setIntegral_const, smul_eq_mul, ih, Finset.prod_range_succ]
    ring

theorem pathLaw_real_cylinder [MeasurableSpace T] [DiscreteMeasurableSpace T] (D : FinChain T)
    (t : T) (z : ℕ → T) (n : ℕ) :
    (D.pathLaw t).real {ω | ∀ i ≤ n, ω i = z i} =
      (if t = z 0 then 1 else 0) * ∏ i ∈ range n, D.P (z i) (z (i + 1)) :=
  (lumps_id D).pathLaw_real_cylinder t z n

variable [MeasurableSpace T] [DiscreteMeasurableSpace T]

theorem Lumps.map_pathLaw (hL : C.Lumps f D) (x : S) :
    (C.pathLaw x).map (fun ω n => f (ω n)) = D.pathLaw (f x) := by
  have hF : Measurable fun (ω : ℕ → S) (n : ℕ) => f (ω n) :=
    measurable_pi_iff.2 fun n => (Measurable.of_discrete (f := f)).comp (measurable_pi_apply n)
  refine measure_ext_of_cylinder fun n z => ?_
  have hms : MeasurableSet {ω : ℕ → T | ∀ i ≤ n, ω i = z i} := by
    have h : {ω : ℕ → T | ∀ i ≤ n, ω i = z i} =
        ⋂ i, ⋂ (_ : i ≤ n), (fun ω : ℕ → T => ω i) ⁻¹' {z i} := by
      ext ω
      simp
    rw [h]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
      measurable_pi_apply i (measurableSet_singleton _)
  rw [Measure.map_apply hF hms]
  refine (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 ?_
  exact (hL.pathLaw_real_cylinder x z n).trans (D.pathLaw_real_cylinder (f x) z n).symm

theorem Lumps.pathLaw_real_preimage (hL : C.Lumps f D) (x : S) {E : Set (ℕ → T)}
    (hE : MeasurableSet E) :
    (C.pathLaw x).real {ω | (fun n => f (ω n)) ∈ E} = (D.pathLaw (f x)).real E := by
  have hF : Measurable fun (ω : ℕ → S) (n : ℕ) => f (ω n) :=
    measurable_pi_iff.2 fun n => (Measurable.of_discrete (f := f)).comp (measurable_pi_apply n)
  rw [← hL.map_pathLaw x, measureReal_def, measureReal_def, Measure.map_apply hF hE]
  rfl

end FinChain

end Rhone.MarkovChain
