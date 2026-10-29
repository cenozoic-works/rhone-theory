/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.KingmanDiversityRewards
public import Rhone.MarkovChain.Shift

/-!
# Two-time Kingman state laws for diversity reward moments

Source: kingman1982, sec. 1, eq. (1.1)–(1.4), (1.7). -/

@[expose] public section
open MeasureTheory ProbabilityTheory Finset Filter Rhone.MarkovChain
namespace Rhone.Coalescent
theorem partitionChain_real_eval_pair (n : ℕ)
    (x y z : Finpartition (Finset.univ : Finset (Fin n))) (i j : ℕ) :
    ((partitionChain (Fin n)).jumpChain.pathLaw x).real
      {ω | ω i = y ∧ ω (i + j) = z} =
    (partitionChain (Fin n)).jumpChain.stepN i x y *
      (partitionChain (Fin n)).jumpChain.stepN j y z := by
  classical
  let C := (partitionChain (Fin n)).jumpChain
  let B : Set (ℕ → Finpartition (Finset.univ : Finset (Fin n))) :=
    {ω | ω 0 = y ∧ ω j = z}
  have hB : MeasurableSet B := (measurableSet_eq_fun
    (measurable_pi_apply 0) measurable_const).inter
      (measurableSet_eq_fun (measurable_pi_apply j) measurable_const)
  have hrow (q : Finpartition (Finset.univ : Finset (Fin n))) :
      (C.pathLaw q).real B = if q = y then C.stepN j y z else 0 := by
    have hinit : ∀ᵐ ω ∂C.pathLaw q, ω 0 = q := by
      have hz : C.pathLaw q {ω | ω 0 ≠ q} = 0 := by
        have he := C.map_eval_singleton 0 q q
        rw [Measure.map_apply (measurable_pi_apply 0) (measurableSet_singleton q)] at he
        have hm : MeasurableSet {ω : ℕ → Finpartition (Finset.univ : Finset (Fin n)) | ω 0 = q} :=
          measurableSet_eq_fun (measurable_pi_apply 0) measurable_const
        have hone : C.pathLaw q {ω | ω 0 = q} = 1 := by
          convert he using 1
          · congr 1
          · simp [FinChain.stepN_zero]
        exact (prob_compl_eq_zero_iff hm).2 hone
      exact ae_iff.2 hz
    by_cases hq : q = y
    · subst q
      rw [ite_eq_left rfl, ← C.pathLaw_real_eval j y z]
      apply measureReal_congr
      filter_upwards [hinit] with ω hω
      simp [B, hω]
    · rw [ite_eq_right hq]
      have he : B =ᵐ[C.pathLaw q] (∅ : Set _) := by
        filter_upwards [hinit] with ω hω
        simp [B, hω, hq]
      rw [measureReal_congr he, measureReal_empty]
  have hevent : {ω : ℕ → Finpartition (Finset.univ : Finset (Fin n)) |
      ω i = y ∧ ω (i + j) = z} =
      {ω | (fun k => ω (i + k)) ∈ B} := by
    ext ω
    simp [B]
  rw [hevent, C.pathLaw_real_shift x i hB]
  simp_rw [hrow]
  simp [C]
theorem partitionChain_integral_eval_mul (n : ℕ)
    (x : Finpartition (Finset.univ : Finset (Fin n))) (i j : ℕ)
    (f g : Finpartition (Finset.univ : Finset (Fin n)) → ℝ) :
    ∫ ω, f (ω i) * g (ω (i + j))
      ∂(partitionChain (Fin n)).jumpChain.pathLaw x =
    ∑ y, (partitionChain (Fin n)).jumpChain.stepN i x y * f y *
      (partitionChain (Fin n)).jumpChain.expectN j g y := by
  classical
  let C := (partitionChain (Fin n)).jumpChain
  let ev := fun ω : ℕ → Finpartition (Finset.univ : Finset (Fin n)) =>
    (ω i, ω (i + j))
  have hm : Measurable ev := (measurable_pi_apply i).prodMk
    (measurable_pi_apply (i + j))
  let F := fun yz : Finpartition (Finset.univ : Finset (Fin n)) ×
      Finpartition (Finset.univ : Finset (Fin n)) => f yz.1 * g yz.2
  have hint : Integrable F ((C.pathLaw x).map ev) :=
    Integrable.of_bound Measurable.of_discrete.aestronglyMeasurable (∑ yz, |F yz|)
      (Eventually.of_forall fun yz => (Real.norm_eq_abs _).le.trans
        (Finset.single_le_sum (f := fun yz => |F yz|)
          (fun _ _ => abs_nonneg _) (mem_univ yz)))
  have hp (yz : Finpartition (Finset.univ : Finset (Fin n)) ×
      Finpartition (Finset.univ : Finset (Fin n))) :
      ((C.pathLaw x).map ev).real {yz} = C.stepN i x yz.1 * C.stepN j yz.1 yz.2 := by
    rw [Measure.real, Measure.map_apply hm (measurableSet_singleton yz)]
    have he : ev ⁻¹' {yz} = {ω | ω i = yz.1 ∧ ω (i + j) = yz.2} := by
      ext ω
      simp [ev, Prod.ext_iff]
    rw [he]
    exact partitionChain_real_eval_pair n x yz.1 yz.2 i j
  change (∫ ω, F (ev ω) ∂C.pathLaw x) = _
  rw [← integral_map hm.aemeasurable hint.aestronglyMeasurable,
    integral_fintype hint]
  simp_rw [hp, smul_eq_mul]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro y _
  simp only [F, FinChain.expectN, Matrix.mulVec, dotProduct]
  change (∑ z, C.stepN i x y * C.stepN j y z * (f y * g z)) =
    C.stepN i x y * f y * ∑ z, C.stepN j y z * g z
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  ring

theorem partitionChain_integrable_eval_mul (n : ℕ)
    (x : Finpartition (Finset.univ : Finset (Fin n))) (i j : ℕ)
    (f g : Finpartition (Finset.univ : Finset (Fin n)) → ℝ) :
    Integrable (fun ω => f (ω i) * g (ω j))
      ((partitionChain (Fin n)).jumpChain.pathLaw x) := by
  classical
  let F := fun yz : Finpartition (Finset.univ : Finset (Fin n)) ×
      Finpartition (Finset.univ : Finset (Fin n)) => f yz.1 * g yz.2
  apply Integrable.of_bound
    (((Measurable.of_discrete (f := f)).comp (measurable_pi_apply i)).mul
      ((Measurable.of_discrete (f := g)).comp (measurable_pi_apply j))).aestronglyMeasurable
    (∑ yz, |F yz|)
  exact Eventually.of_forall fun ω => (Real.norm_eq_abs _).le.trans
    (Finset.single_le_sum (f := fun yz => |F yz|) (fun _ _ => abs_nonneg _)
      (mem_univ (ω i, ω j)))

theorem partitionChain_integral_eval_difference (n : ℕ)
    (x : Finpartition (Finset.univ : Finset (Fin n))) (i j : ℕ)
    (f u : Finpartition (Finset.univ : Finset (Fin n)) → ℝ) :
    ∫ ω, f (ω i) * (u (ω (i + j)) - u (ω (i + j + 1)))
      ∂(partitionChain (Fin n)).jumpChain.pathLaw x =
    ∫ ω, f (ω i) * (u (ω (i + j)) -
      (partitionChain (Fin n)).jumpChain.expect u (ω (i + j)))
      ∂(partitionChain (Fin n)).jumpChain.pathLaw x := by
  classical
  let C := (partitionChain (Fin n)).jumpChain
  have hleft : (fun ω : ℕ → Finpartition (Finset.univ : Finset (Fin n)) =>
      f (ω i) * (u (ω (i + j)) - u (ω (i + j + 1)))) =
      (fun ω => f (ω i) * u (ω (i + j))) -
        (fun ω => f (ω i) * u (ω (i + j + 1))) := by
    funext ω
    exact mul_sub _ _ _
  rw [hleft]
  change (∫ ω, f (ω i) * u (ω (i + j)) - f (ω i) * u (ω (i + j + 1))
    ∂(partitionChain (Fin n)).jumpChain.pathLaw x) = _
  rw [integral_sub (partitionChain_integrable_eval_mul n x i (i + j) f u)
    (partitionChain_integrable_eval_mul n x i (i + j + 1) f u)]
  rw [partitionChain_integral_eval_mul]
  have hadd : i + j + 1 = i + (j + 1) := by omega
  rw [hadd, partitionChain_integral_eval_mul]
  change _ = ∫ ω, f (ω i) * (u - C.expect u) (ω (i + j)) ∂C.pathLaw x
  rw [partitionChain_integral_eval_mul]
  simp only [FinChain.expectN_sub_fun, Pi.sub_apply, FinChain.expectN_succ']
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem kingmanDiversityReward_jump_drift {n : ℕ} (hn : 0 < n)
    (π : Finpartition (Finset.univ : Finset (Fin n))) :
    kingmanDiversityReward n π -
      (partitionChain (Fin n)).jumpChain.expect (kingmanDiversityReward n) π =
    if π ∈ coalescedPartitions (Fin n) then 0
      else kingmanDiversityReward n π / (partitionChain (Fin n)).rate π := by
  have hs := FinChain.potential_step (partitionChain_coalesced_isAbsorbingSet n)
    (partitionChain_coalesced_reaches n)
    (fun σ => kingmanDiversityReward n σ / (partitionChain (Fin n)).rate σ) π
  change (partitionChain (Fin n)).expectedCost (coalescedPartitions (Fin n))
    (kingmanDiversityReward n) π = _ + (partitionChain (Fin n)).jumpChain.expect
      ((partitionChain (Fin n)).expectedCost (coalescedPartitions (Fin n))
        (kingmanDiversityReward n)) π at hs
  rw [← kingmanDiversityReward_eq_expectedCost hn] at hs
  linarith

theorem kingmanDiversitySquarePotential_jump_drift {n : ℕ} (hn : 0 < n)
    (π : Finpartition (Finset.univ : Finset (Fin n))) :
    kingmanDiversitySquarePotential n π -
      (partitionChain (Fin n)).jumpChain.expect (kingmanDiversitySquarePotential n) π =
    if π ∈ coalescedPartitions (Fin n) then 0
      else 2 * kingmanDiversityReward n π ^ 2 / (partitionChain (Fin n)).rate π := by
  have hs := FinChain.potential_step (partitionChain_coalesced_isAbsorbingSet n)
    (partitionChain_coalesced_reaches n)
    (fun σ => (2 * kingmanDiversityReward n σ ^ 2) / (partitionChain (Fin n)).rate σ) π
  change (partitionChain (Fin n)).expectedCost (coalescedPartitions (Fin n))
    (fun σ => 2 * kingmanDiversityReward n σ ^ 2) π = _ + (partitionChain (Fin n)).jumpChain.expect
      ((partitionChain (Fin n)).expectedCost (coalescedPartitions (Fin n))
        (fun σ => 2 * kingmanDiversityReward n σ ^ 2)) π at hs
  rw [← kingmanDiversitySquarePotential_eq_expectedCost hn] at hs
  linarith

end Rhone.Coalescent
