/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.LocallyIntegrableLinearODE
public import Rhone.Statistics.Identifiability.InhomogeneousMarkovFlow
public import Rhone.Statistics.Identifiability.AbsolutelyContinuousClock

/-! # Locally integrable inhomogeneous row operators: absolute continuity basics -/

@[expose] public section

open Set Filter MeasureTheory
open scoped BigOperators Topology NNReal
namespace Rhone.Statistics.Identifiability

theorem ac_comp_lipschitz {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    {f : ℝ → E} {g : E → F} {a b : ℝ} {K : ℝ≥0}
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : LipschitzWith K g) :
    AbsolutelyContinuousOnInterval (fun t => g (f t)) a b :=
  hg.comp_absolutelyContinuousOnInterval hf

theorem ac_finset_sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ} {a b : ℝ}
    (hf : ∀ i ∈ s, AbsolutelyContinuousOnInterval (f i) a b) :
    AbsolutelyContinuousOnInterval (fun t => ∑ i ∈ s, f i t) a b := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using (LipschitzWith.const (0 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval
  | @insert i s hi ih =>
      simpa only [Finset.sum_insert hi] using
        (hf i (Finset.mem_insert_self i s)).fun_add
          (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem ac_sq_min_zero {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun t => (min (f t) 0)^2) a b := by
  have hm : AbsolutelyContinuousOnInterval (fun t => min (f t) 0) a b :=
    ac_comp_lipschitz (g := fun x : ℝ => min x 0) hf (LipschitzWith.id.min_const 0)
  simpa only [pow_two] using hm.fun_mul hm

variable {ι : Type*} [Fintype ι]

theorem ac_coordinate {v : ℝ → ι → ℝ} {a b : ℝ}
    (hv : AbsolutelyContinuousOnInterval v a b) (i : ι) :
    AbsolutelyContinuousOnInterval (fun t => v t i) a b :=
  ac_comp_lipschitz (g := fun x : ι → ℝ => x i) hv (ContinuousLinearMap.proj (R := ℝ) (φ := fun _
    : ι => ℝ) i).lipschitzWith

theorem metzler_energy_coefficient_locallyIntegrable {Q : ℝ → ι → ι → ℝ}
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume) :
    LocallyIntegrable (fun t => 2 * ∑ j, ∑ i, |Q t i j|) volume := by
  have h : LocallyIntegrable (fun t => ∑ j, ∑ i, |Q t i j|) volume := by
    apply locallyIntegrable_finsetSum; intro j _
    apply locallyIntegrable_finsetSum; intro i _
    change LocallyIntegrable (fun t => ‖Q t i j‖) volume
    exact fun t => (hQ i j t).norm
  change LocallyIntegrable ((2 : ℝ) • (fun t => ∑ j, ∑ i, |Q t i j|)) volume
  exact h.smul 2

theorem locallyIntegrable_finite_pi {κ E : Type*} [Fintype κ] [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → κ → E}
    (hf : ∀ i, LocallyIntegrable (fun t => f t i) volume) : LocallyIntegrable f volume := by
  classical
  have h : LocallyIntegrable (fun t => ∑ i, (ContinuousLinearMap.single ℝ (fun _ : κ => E) i)
      (f t i)) volume := by
    apply locallyIntegrable_finsetSum
    intro i _ t
    exact (ContinuousLinearMap.single ℝ (fun _ : κ => E) i).integrableAtFilter_comp (hf i t)
  simpa only [ContinuousLinearMap.single_apply, Finset.univ_sum_single] using h

noncomputable def matrixToRowOperator : (ι → ι → ℝ) →L[ℝ] ((ι → ℝ) →L[ℝ] (ι → ℝ)) :=
  LinearMap.toContinuousLinearMap
  { toFun := inhomogeneousRowOperator
    map_add' := by
      intro Q R
      ext x j
      simp [inhomogeneousRowOperator_apply, mul_add, Finset.sum_add_distrib]
    map_smul' := by
      intro a Q
      ext x j
      simp [inhomogeneousRowOperator_apply, Finset.mul_sum, mul_left_comm] }

theorem inhomogeneousRowOperator_locallyIntegrable (Q : ℝ → ι → ι → ℝ)
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume) :
    LocallyIntegrable (fun t => inhomogeneousRowOperator (Q t)) volume := by
  have h : LocallyIntegrable Q volume :=
    locallyIntegrable_finite_pi (fun i => locallyIntegrable_finite_pi (hQ i))
  exact fun t => (matrixToRowOperator (ι := ι)).integrableAtFilter_comp (h t)

theorem locallyIntegrable_entries_of_rowOperator (Q : ℝ → ι → ι → ℝ)
    (hQ : LocallyIntegrable (fun t => inhomogeneousRowOperator (Q t)) volume) :
    ∀ i j, LocallyIntegrable (fun t => Q t i j) volume := by
  classical
  intro i j
  let L : ((ι → ℝ) →L[ℝ] (ι → ℝ)) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j).comp
      (ContinuousLinearMap.apply' (ι → ℝ) (RingHom.id ℝ) (Pi.single i 1))
  have h : LocallyIntegrable (fun t => L (inhomogeneousRowOperator (Q t))) volume :=
    fun t => L.integrableAtFilter_comp (hQ t)
  simpa [L, inhomogeneousRowOperator_apply, Pi.single_apply] using h

theorem inhomogeneousRowOperator_locallyIntegrable_iff (Q : ℝ → ι → ι → ℝ) :
    LocallyIntegrable (fun t => inhomogeneousRowOperator (Q t)) volume ↔
      ∀ i j, LocallyIntegrable (fun t => Q t i j) volume :=
  ⟨locallyIntegrable_entries_of_rowOperator Q, inhomogeneousRowOperator_locallyIntegrable Q⟩

end Rhone.Statistics.Identifiability
