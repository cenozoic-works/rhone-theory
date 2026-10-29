/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.CommonClockIslandJointDensity
public import Rhone.Statistics.Identifiability.TimeVaryingJointMarginalMeasure
public import Rhone.Statistics.Identifiability.FiniteProductFlow
public import Rhone.Statistics.Identifiability.PairAbsorption

/-! # Pair marginals of the common-clock island joint law in the constant-rate case -/

@[expose] public section

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal Matrix Matrix.Norms.Operator
namespace Rhone.Statistics.Identifiability
set_option backward.isDefEq.respectTransparency false

theorem constant_exp_entry_hasDerivAt {d : ℕ}
    (Q : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) (t : ℝ) :
    HasDerivAt (fun u => NormedSpace.exp (u • Q) i j)
      ((NormedSpace.exp (t • Q) * Q) i j) t := by
  have h := flowOutput_hasDerivAt_right Q i (Pi.single j 1) t
  rw [Matrix.mulVec_single_one] at h
  convert! h using 1
  · funext u
    simp [flowOutput, Matrix.col]
  · simp only [flowOutput, pow_zero, Matrix.one_mul]
    simp [Matrix.mulVec, dotProduct, Matrix.col, Matrix.mul_apply]

theorem inhomogeneousTransition_const_eq_exp {d : ℕ}
    (Q : Matrix (Fin d) (Fin d) ℝ) (s t : ℝ) :
    inhomogeneousTransition (fun _ => Q) s t = NormedSpace.exp ((t-s) • Q) := by
  have hd : ∀ u i j, HasDerivAt (fun v => NormedSpace.exp ((v-s) • Q) i j)
      ((NormedSpace.exp ((u-s) • Q) * Q) i j) u := by
    intro u i j
    convert! (constant_exp_entry_hasDerivAt Q i j (u-s)).comp u
      ((hasDerivAt_id u).sub_const s) using 1
    simp
  have h := finiteMatrix_solution_eq_transition (fun _ => Q)
    (fun u => NormedSpace.exp ((u-s) • Q)) (fun _ _ => continuous_const) s hd t
  simpa using h.symm

theorem timeVaryingPreRow_const (k : ℕ) (c q r t : ℝ) :
    timeVaryingPreRow k (fun _ => c) (fun _ => q) (fun _ => r) t =
      NormedSpace.exp (t • MarkovChain.Identifiability.generator k c q r) 0 := by
  change inhomogeneousTransition (fun _ => MarkovChain.Identifiability.generator k c q r) 0 t 0 = _
  rw [inhomogeneousTransition_const_eq_exp, sub_zero]

theorem timeVaryingMarkFlux_const (k : ℕ) (c q r : ℝ) (m : Fin 5) (t : ℝ) :
    timeVaryingMarkFlux k (fun _ => c) (fun _ => q) (fun _ => r) m t =
      markFlux k c q r m t := by
  simp only [timeVaryingMarkFlux, timeVaryingPreRow_const,
    markFlux, flowOutput, pow_zero, Matrix.one_mul, Matrix.mulVec, dotProduct]

theorem timeVaryingPairTransition_const (k : ℕ) (c q s t : ℝ) :
    timeVaryingPairTransition k (fun _ => c) (fun _ => q) s t =
      NormedSpace.exp ((t-s) • MarkovChain.Identifiability.pairGenerator k c q) :=
  inhomogeneousTransition_const_eq_exp _ _ _

theorem timeVaryingUpperDensity_const (k : ℕ) (c q r : ℝ) (p : ℝ × ℝ) :
    timeVaryingUpperDensity k (fun _ => c) (fun _ => q) (fun _ => r) p =
      upperDensity k c q r p.1 p.2 := by
  rcases p with ⟨s,t⟩
  rw [timeVaryingUpperDensity_matrix, timeVaryingPairTransition_const]
  simp only [timeVaryingPreRow_const, upperDensity,
    Matrix.mul_apply, Matrix.mulVec, Matrix.vecMul, dotProduct]

theorem timeVaryingJointLaw_const (k : ℕ) {c q r : ℝ}
    (hc : 0 ≤ c) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    timeVaryingJointLaw k (fun _ => c) (fun _ => q) (fun _ => r) = jointLaw k c q r := by
  rw [timeVaryingJointLaw_eq_regular _ _ _ _ continuous_const continuous_const continuous_const,
    commonClockIslandJointLaw_eq_regular k hc hq hr]
  congr 1
  · funext t
    exact timeVaryingMarkFlux_const k c q r 0 t
  · funext p
    exact timeVaryingUpperDensity_const k c q r p

theorem timeVaryingPairExitLaw_const (k : ℕ) (c q : ℝ) (i : Fin 2) :
    timeVaryingPairExitLaw k (fun _ => c) (fun _ => q) 0 i =
      firstExitLaw (MarkovChain.Identifiability.pairGenerator k c q) i := by
  unfold timeVaryingPairExitLaw firstExitLaw
  congr 1
  funext t
  congr 1
  rw [pair_exitRate]
  simp [timeVaryingPairExitDensity, timeVaryingPairTransition_const,
    flowOutput, MarkovChain.Identifiability.pairDensity, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two]

theorem timeVaryingPairSurvival_const_tendsto_zero (k : ℕ) {c q : ℝ}
    (hc : 0 < c) (hq : 0 < q) (s : ℝ) (i : Fin 2) :
    Tendsto (timeVaryingPairSurvival k (fun _ => c) (fun _ => q) s i)
      atTop (𝓝 0) := by
  have he : timeVaryingPairSurvival k (fun _ => c) (fun _ => q) s i =
      fun t => flowOutput (MarkovChain.Identifiability.pairGenerator k c q) i
          MarkovChain.Identifiability.pairSurvival 0 (t-s) := by
    funext t
    simp [timeVaryingPairSurvival, timeVaryingPairTransition_const,
      flowOutput, MarkovChain.Identifiability.pairSurvival, Matrix.mulVec, dotProduct]
  rw [he]
  exact (pair_survival_tendsto_zero k hc hq i).comp (tendsto_atTop_add_const_right atTop (-s)
    tendsto_id)

theorem commonClockIslandJointLaw_map_fst (k : ℕ) {c q r : ℝ}
    (hc : 0 < c) (hq : 0 < q) (hr : 0 ≤ r) :
    (jointLaw k c q r).map Prod.fst = firstExitLaw (MarkovChain.Identifiability.pairGenerator k c q)
        0 := by
  rw [← timeVaryingJointLaw_const k hc.le hq.le hr,
    timeVaryingJointLaw_map_fst _ _ _ _ continuous_const continuous_const continuous_const
      (fun _ _ => hc.le) (fun _ _ => hq.le) (fun _ _ => hr)
      (fun s _ i => timeVaryingPairSurvival_const_tendsto_zero k hc hq s i),
    timeVaryingPairExitLaw_const]

theorem commonClockIslandJointLaw_map_snd (k : ℕ) {c q r : ℝ}
    (hc : 0 < c) (hq : 0 < q) (hr : 0 ≤ r) :
    (jointLaw k c q r).map Prod.snd = firstExitLaw (MarkovChain.Identifiability.pairGenerator k c q)
        0 := by
  rw [← timeVaryingJointLaw_const k hc.le hq.le hr,
    timeVaryingJointLaw_map_snd _ _ _ _ continuous_const continuous_const continuous_const
      (fun _ _ => hc.le) (fun _ _ => hq.le) (fun _ _ => hr)
      (fun s _ i => timeVaryingPairSurvival_const_tendsto_zero k hc hq s i),
    timeVaryingPairExitLaw_const]

end Rhone.Statistics.Identifiability
