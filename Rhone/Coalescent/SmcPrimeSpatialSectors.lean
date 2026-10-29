/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeGenealogyLaw
public import Rhone.Coalescent.SmcPrimeSpatialLengthMean
public import Rhone.Coalescent.SmcSupport.JointSampler

/-! # Finite sectors of the sequential SMC′ process -/

@[expose] public section

namespace Rhone.Coalescent.SmcPrime
open MeasureTheory ProbabilityTheory IntervalProcess

theorem spatial_step_stopped (N : ℕ) (R : ℝ) (z : SpatialState N)
    (u : ProposalNoise) (hz : z.1 = 1) : spatialStep N R z u = z := by
  simp only [spatialStep, hz, le_refl, true_or, ↓reduceIte]
  exact Prod.ext hz.symm rfl

theorem spatial_path_stopped (N : ℕ) (R : ℝ) (z : SpatialState N) :
    ∀ᵐ ω ∂(spatialProcess N R).pathLaw z,
      ∀ k, (ω k).1 = 1 → (ω (k + 1)).1 = 1 := by
  let A : SpatialState N × SpatialState N → Prop := fun p => p.1.1 = 1 → p.2.1 = 1
  have hA : MeasurableSet {p | A p} := by
    simp only [A, imp_iff_not_or]
    exact (measurableSet_eq_fun (show Measurable (fun p : SpatialState N × SpatialState N =>
      p.1.1) from measurable_fst.fst) measurable_const).compl.union
      (measurableSet_eq_fun measurable_snd.fst measurable_const)
  apply SmcSupport.process_transition_relation (spatialProcess N R) A hA _ z
  intro w
  change ∀ᵐ y ∂spatialKernel N R w, A (w, y)
  rw [spatialKernel_apply]
  apply (ae_map_iff ((spatialStep_measurable N R).comp
    (measurable_const.prodMk measurable_id)).aemeasurable
    (hA.preimage (measurable_const.prodMk measurable_id))).mpr
  exact Filter.Eventually.of_forall (fun u hw => by
    change (spatialStep N R w u).1 = 1
    rw [spatial_step_stopped N R w u hw]
    exact hw)

theorem spatial_position_after_stop {N : ℕ} (ω : ℕ → SpatialState N)
    (hstop : ∀ k, (ω k).1 = 1 → (ω (k + 1)).1 = 1)
    (K : ℕ) (hK : (ω K).1 = 1) (k : ℕ) (hk : K ≤ k) : (ω k).1 = 1 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  induction j with
  | zero => simpa using hK
  | succ j ih => exact hstop (K + j) ih

theorem spatial_observation_zero {N : ℕ} (ω : ℕ → SpatialState N)
    (hinit : (ω 0).1 = 0) (hfirst : (ω 1).1 = 1)
    (hstop : ∀ k, (ω k).1 = 1 → (ω (k + 1)).1 = 1) :
    spatialGenealogyObservation N ω = fun _ i j => treePairMRCA (ω 0).2 i j := by
  funext q i j
  have hq0 : (0 : ℝ) ≤ q.val := by exact_mod_cast q.property.1
  have hq1 : (q.val : ℝ) < 1 := by exact_mod_cast q.property.2
  apply le_antisymm
  · exact iInf_le_of_le 0 (by simp [hinit, hfirst, hq0, hq1])
  · apply le_iInf
    intro k
    by_cases hk : k = 0
    · subst k
      simp [hinit, hfirst, hq0, hq1]
    · have hx := spatial_position_after_stop ω hstop 1 hfirst k (by omega)
      simp [hx, not_le.mpr hq1]

theorem spatial_observation_one {N : ℕ} (ω : ℕ → SpatialState N)
    (hinit : (ω 0).1 = 0) (_hfirst : (ω 1).1 < 1) (hsecond : (ω 2).1 = 1)
    (hstop : ∀ k, (ω k).1 = 1 → (ω (k + 1)).1 = 1) :
    spatialGenealogyObservation N ω = fun q i j =>
      if (q.val : ℝ) < (ω 1).1 then treePairMRCA (ω 0).2 i j
      else treePairMRCA (ω 1).2 i j := by
  funext q i j
  have hq0 : (0 : ℝ) ≤ q.val := by exact_mod_cast q.property.1
  have hq1 : (q.val : ℝ) < 1 := by exact_mod_cast q.property.2
  by_cases hqx : (q.val : ℝ) < (ω 1).1
  · rw [ite_eq_left hqx]
    apply le_antisymm
    · exact iInf_le_of_le 0 (by simp [hinit, hq0, hqx])
    · apply le_iInf
      intro k
      by_cases hk0 : k = 0
      · subst k
        simp [hinit, hq0, hqx]
      · by_cases hk1 : k = 1
        · subst k
          simp [not_le.mpr hqx]
        · have hx := spatial_position_after_stop ω hstop 2 hsecond k (by omega)
          simp [hx, not_le.mpr hq1]
  · rw [ite_eq_right hqx]
    apply le_antisymm
    · exact iInf_le_of_le 1 (by simp [hsecond, le_of_not_gt hqx, hq1])
    · apply le_iInf
      intro k
      by_cases hk0 : k = 0
      · subst k
        simp [hqx]
      · by_cases hk1 : k = 1
        · subst k
          simp [hsecond, le_of_not_gt hqx, hq1]
        · have hx := spatial_position_after_stop ω hstop 2 hsecond k (by omega)
          simp [hx, not_le.mpr hq1]

noncomputable def zeroProposalGenealogySector (N : ℕ) (R : ℝ) : Measure (Genealogy N) :=
  (((spatialProcess N R).law (spatialInitialLaw N)).restrict
    {ω | (ω 1).1 = 1}).map (spatialGenealogyObservation N)

noncomputable def oneProposalGenealogySector (N : ℕ) (R : ℝ) : Measure (Genealogy N) :=
  (((spatialProcess N R).law (spatialInitialLaw N)).restrict
    {ω | (ω 1).1 < 1 ∧ (ω 2).1 = 1}).map (spatialGenealogyObservation N)

theorem spatial_zero_one_sectors_le (N : ℕ) (R : ℝ) :
    zeroProposalGenealogySector N R + oneProposalGenealogySector N R ≤
      smcPrimeGenealogyLaw N R := by
  have hmeas : MeasurableSet {ω : ℕ → SpatialState N |
      (ω 1).1 < 1 ∧ (ω 2).1 = 1} := by
    have h1 : Measurable (fun ω : ℕ → SpatialState N => (ω 1).1) :=
      (measurable_pi_apply 1).fst
    have h2 : Measurable (fun ω : ℕ → SpatialState N => (ω 2).1) :=
      (measurable_pi_apply 2).fst
    exact (measurableSet_lt h1 measurable_const).inter
      (measurableSet_eq_fun h2 measurable_const)
  have hdis : Disjoint {ω : ℕ → SpatialState N | (ω 1).1 = 1}
      {ω | (ω 1).1 < 1 ∧ (ω 2).1 = 1} := by
    apply Set.disjoint_left.mpr
    intro ω h0 h1
    exact (ne_of_lt h1.1) h0
  unfold zeroProposalGenealogySector oneProposalGenealogySector smcPrimeGenealogyLaw
  rw [← Measure.map_add _ _ (spatialGenealogyObservation_measurable N),
    ← Measure.restrict_union hdis hmeas]
  exact Measure.map_mono Measure.restrict_le_self (spatialGenealogyObservation_measurable N)

end Rhone.Coalescent.SmcPrime
