/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeTwoSampleArrayLaw
public import Rhone.Coalescent.SmcPrimeSpatialProcess

/-!
# One step of the SMC′ chain on a reachable two-sample array

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/

@[expose] public section

namespace Rhone.Coalescent.SmcPrime
open MeasureTheory Set IntervalProcess
open scoped ENNReal

theorem proposalNoiseLaw_map_marks :
    proposalNoiseLaw.map (fun u => ((u 1, u 2), (u 3, u 4))) =
      (unitUniform.prod unitUniform).prod (unitUniform.prod unitUniform) := by
  have hgr := proposalNoiseLaw_grouped
  have hcomp : (fun u : ProposalNoise => ((u 1, u 2), (u 3, u 4))) =
      Prod.snd ∘ fun u : ProposalNoise => (u 0, ((u 1, u 2), (u 3, u 4))) := rfl
  rw [hcomp, ← Measure.map_map measurable_snd (by fun_prop), hgr, Measure.map_snd_prod]
  simp

theorem proposal_distance {N : ℕ} (R : ℝ) (T : Tree N) (u : ProposalNoise) :
    (proposal R T u).1 = -Real.log (u 0) / (R / 2 * treeLength T) := by
  unfold proposal
  cases cutPoint T (u 1) (u 2) <;> rfl

namespace TwoSampleArray

variable {T : Tree 2}

theorem proposal_mark_rootHeight_lintegral (hT : TwoSampleArray T) (R : ℝ)
    (hh : 0 < rootHeight T) (Φ : ℝ × ℝ → ℝ≥0∞) (hΦ : Measurable Φ) :
    ∫⁻ u, Φ (u 0, rootHeight (SmcPrime.proposal R T u).2.2) ∂proposalNoiseLaw =
      ∫⁻ v, (ENNReal.ofReal (twoSampleSelfMass (rootHeight T)) * Φ (v, rootHeight T) +
        ∫⁻ a in Ioi 0, ENNReal.ofReal (twoSampleJumpDensity (rootHeight T) a) * Φ (v, a))
        ∂unitUniform := by
  let G : ℝ × ((ℝ × ℝ) × (ℝ × ℝ)) → ℝ≥0∞ := fun x =>
    Φ (x.1, rootHeight (SmcPrime.proposal R T (proposalMarks x.2.1 x.2.2)).2.2)
  have hG : Measurable G := hΦ.comp (measurable_fst.prodMk ((rootHeight_measurable 2).comp
    ((measurable_snd.comp measurable_snd).comp ((proposal_measurable 2 R).comp
      (measurable_const.prodMk (measurable_proposalMarks.comp measurable_snd))))))
  have hfun : (fun u : ProposalNoise =>
      Φ (u 0, rootHeight (SmcPrime.proposal R T u).2.2)) =
      fun u => G (u 0, ((u 1, u 2), (u 3, u 4))) := by
    funext u
    simp only [G, proposal_tree_proposalMarks]
  rw [hfun, ← lintegral_map hG (by fun_prop), proposalNoiseLaw_grouped,
    lintegral_prod _ hG.aemeasurable]
  refine lintegral_congr fun v => ?_
  rw [← hT.proposal_rootHeight_lintegral R hh (fun a => Φ (v, a))
    (hΦ.comp (measurable_const.prodMk measurable_id))]
  have hGv : Measurable (fun pq : (ℝ × ℝ) × (ℝ × ℝ) => G (v, pq)) :=
    hG.comp (measurable_const.prodMk measurable_id)
  rw [← proposalNoiseLaw_map_marks, lintegral_map hGv (by fun_prop)]
  simp only [G, proposal_tree_proposalMarks]

theorem spatialStep_lintegral (hT : TwoSampleArray T) {R : ℝ} (hR : 0 < R)
    (hh : 0 < rootHeight T) {p : ℝ} (hp : p < 1) (Ψ : ℝ × ℝ → ℝ≥0∞) (hΨ : Measurable Ψ) :
    ∫⁻ u, Ψ ((SmcPrime.spatialStep 2 R (p, T) u).1,
        rootHeight (SmcPrime.spatialStep 2 R (p, T) u).2)
        ∂proposalNoiseLaw =
      ∫⁻ e in Ioi 0, ENNReal.ofReal (Real.exp (-e)) *
        (if p + e / (R * rootHeight T) < 1 then
          ENNReal.ofReal (twoSampleSelfMass (rootHeight T)) *
              Ψ (p + e / (R * rootHeight T), rootHeight T) +
            ∫⁻ a in Ioi 0, ENNReal.ofReal (twoSampleJumpDensity (rootHeight T) a) *
              Ψ (p + e / (R * rootHeight T), a)
        else Ψ (1, rootHeight T)) := by
  have hL := treeLength_pos_of_rootHeight_pos T hh
  let Φ : ℝ × ℝ → ℝ≥0∞ := fun x =>
    if p + -Real.log x.1 / (R * rootHeight T) < 1 then
      Ψ (p + -Real.log x.1 / (R * rootHeight T), x.2) else Ψ (1, rootHeight T)
  have hΦ : Measurable Φ :=
    Measurable.ite (measurableSet_lt (by fun_prop) measurable_const)
      (hΨ.comp (by fun_prop)) measurable_const
  have hstop : ¬ (1 ≤ p ∨ R ≤ 0 ∨ treeLength T ≤ 0) := by
    rintro (h | h | h)
    · exact absurd hp (not_lt.mpr h)
    · exact absurd hR (not_lt.mpr h)
    · exact absurd hL (not_lt.mpr h)
  have hstep : ∀ u : ProposalNoise,
      Ψ ((SmcPrime.spatialStep 2 R (p, T) u).1,
          rootHeight (SmcPrime.spatialStep 2 R (p, T) u).2) =
        Φ (u 0, rootHeight (SmcPrime.proposal R T u).2.2) := by
    intro u
    have hd := proposal_distance R T u
    rw [hT.treeLength_eq hh, show R / 2 * (2 * rootHeight T) = R * rootHeight T by ring] at hd
    by_cases hin : p + -Real.log (u 0) / (R * rootHeight T) < 1
    · have hin' : p + (SmcPrime.proposal R T u).1 < 1 := by rwa [hd]
      simp only [SmcPrime.spatialStep, hstop, ↓reduceIte, hin', Φ, hin]
      rw [hd]
    · have hin' : ¬ p + (SmcPrime.proposal R T u).1 < 1 := by rwa [hd]
      simp only [SmcPrime.spatialStep, hstop, ↓reduceIte, hin', Φ, hin]
  have hk : Measurable (fun q : ℝ × ℝ =>
      ENNReal.ofReal (twoSampleJumpDensity (rootHeight T) q.2) *
        Ψ (p + q.1 / (R * rootHeight T), q.2)) :=
    ((measurable_twoSampleJumpDensity.comp
      (measurable_const.prodMk measurable_snd)).ennreal_ofReal).mul (hΨ.comp (by fun_prop))
  let ψ : ℝ → ℝ≥0∞ := fun e =>
    if p + e / (R * rootHeight T) < 1 then
      ENNReal.ofReal (twoSampleSelfMass (rootHeight T)) *
          Ψ (p + e / (R * rootHeight T), rootHeight T) +
        ∫⁻ a in Ioi 0, ENNReal.ofReal (twoSampleJumpDensity (rootHeight T) a) *
          Ψ (p + e / (R * rootHeight T), a)
    else Ψ (1, rootHeight T)
  have hψ : Measurable ψ :=
    Measurable.ite (measurableSet_lt (by fun_prop) measurable_const)
      ((measurable_const.mul (hΨ.comp (by fun_prop))).add
        (Measurable.lintegral_prod_right' (ν := volume.restrict (Ioi (0 : ℝ))) hk))
      measurable_const
  have hmass : ∀ X : ℝ≥0∞, ENNReal.ofReal (twoSampleSelfMass (rootHeight T)) * X +
      ∫⁻ a in Ioi 0, ENNReal.ofReal (twoSampleJumpDensity (rootHeight T) a) * X = X := by
    intro X
    have hmk : Measurable (fun a : ℝ =>
        ENNReal.ofReal (twoSampleJumpDensity (rootHeight T) a)) :=
      (measurable_twoSampleJumpDensity.comp
        (measurable_const.prodMk measurable_id)).ennreal_ofReal
    rw [lintegral_mul_const _ hmk, lintegral_twoSampleJumpDensity hh, ← add_mul,
      ← ENNReal.ofReal_add (twoSampleSelfMass_nonneg hh)
        (sub_nonneg.mpr (twoSampleSelfMass_le_one hh)),
      add_sub_cancel, ENNReal.ofReal_one, one_mul]
  rw [lintegral_congr hstep, hT.proposal_mark_rootHeight_lintegral R hh Φ hΦ,
    ← lintegral_unitUniform_comp_neg_log ψ hψ]
  refine lintegral_congr fun v => ?_
  by_cases hin : p + -Real.log v / (R * rootHeight T) < 1
  · simp only [Φ, ψ, hin, ↓reduceIte]
  · simp only [Φ, ψ, hin, ↓reduceIte]
    exact hmass _

end TwoSampleArray

end Rhone.Coalescent.SmcPrime
