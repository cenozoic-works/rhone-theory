/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.AEWitness
public import Mathlib.MeasureTheory.Measure.Prod

/-! # Upper-triangle joint density and its law-level invariant -/

@[expose] public section

open scoped Matrix Matrix.Norms.Operator Topology
open MeasureTheory Filter Set

namespace Rhone.Statistics.Identifiability

noncomputable def firstAKernel (c : ℝ) : Matrix MarkovChain.Identifiability.State (Fin 2) ℝ :=
  fun i j => if j = 0 then c * (MarkovChain.Identifiability.firstAThenBTable i : ℝ)
    else c * ((MarkovChain.Identifiability.firstATable i : ℝ) -
        (MarkovChain.Identifiability.firstAThenBTable i : ℝ))

theorem firstAKernel_density (c : ℝ) : firstAKernel c *ᵥ MarkovChain.Identifiability.pairDensity c =
    MarkovChain.Identifiability.nextB c := by
  ext i
  simp [firstAKernel, MarkovChain.Identifiability.pairDensity, MarkovChain.Identifiability.nextB,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

theorem firstAKernel_survival (c : ℝ) : firstAKernel c *ᵥ MarkovChain.Identifiability.pairSurvival =
    MarkovChain.Identifiability.firstA c := by
  ext i
  simp [firstAKernel, MarkovChain.Identifiability.pairSurvival, MarkovChain.Identifiability.firstA,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

noncomputable def upperDensity (k : Nat) (c q r : ℝ) (s t : ℝ) : ℝ :=
  ((NormedSpace.exp (s • MarkovChain.Identifiability.generator k c q r) * firstAKernel c *
    NormedSpace.exp ((t-s) • MarkovChain.Identifiability.pairGenerator k c q)) *ᵥ
        MarkovChain.Identifiability.pairDensity c) 0

theorem upperDensity_diagonal (k : Nat) (c q r t : ℝ) :
    upperDensity k c q r t t = postBJet k c q r 0 t := by
  simp only [upperDensity, sub_self, zero_smul, NormedSpace.exp_zero, Matrix.mul_one]
  rw [← Matrix.mulVec_mulVec, firstAKernel_density]
  simp [postBJet, flowOutput]

theorem upperDensity_continuous (k : Nat) (c q r : ℝ) :
    Continuous (fun p : ℝ × ℝ => upperDensity k c q r p.1 p.2) := by
  have hQ : Continuous
      (fun p : ℝ × ℝ => NormedSpace.exp (p.1 • MarkovChain.Identifiability.generator k c q r)) :=
    NormedSpace.exp_continuous.comp (continuous_fst.smul continuous_const)
  have hK : Continuous (fun p : ℝ × ℝ =>
      NormedSpace.exp ((p.2-p.1) • MarkovChain.Identifiability.pairGenerator k c q)) :=
    NormedSpace.exp_continuous.comp ((continuous_snd.sub continuous_fst).smul continuous_const)
  exact (continuous_apply 0).comp
    (((hQ.matrix_mul continuous_const).matrix_mul hK).matrix_mulVec continuous_const)

noncomputable def upperCross (k : Nat) (c q r : ℝ) (p : ℝ × ℝ) : ℝ :=
  survivalJet k c q 0 p.1 * upperDensity k c q r p.1 p.2 -
    firstAJet k c q r 0 p.1 * densityJet k c q 0 p.2

theorem upperCross_continuous (k : Nat) (c q r : ℝ) : Continuous (upperCross k c q r) := by
  exact (((flowOutput_continuous (MarkovChain.Identifiability.pairGenerator k c q) 0
      MarkovChain.Identifiability.pairSurvival 0).comp
    continuous_fst).mul (upperDensity_continuous k c q r)).sub
    (((flowOutput_continuous (MarkovChain.Identifiability.generator k c q r) 0
        (MarkovChain.Identifiability.firstA c) 0).comp
      continuous_fst).mul
      ((flowOutput_continuous (MarkovChain.Identifiability.pairGenerator k c q) 0
          (MarkovChain.Identifiability.pairDensity c) 0).comp continuous_snd))

theorem upperCross_diagonal (k : Nat) (c q r t : ℝ) :
    upperCross k c q r (t,t) = witness k c q r t := by
  unfold upperCross witness
  rw [upperDensity_diagonal]
  ring

def upperWedge : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 < p.2}

theorem upperWedge_open : IsOpen upperWedge :=
  (isOpen_lt continuous_const continuous_fst).inter
    (isOpen_lt continuous_fst continuous_snd)

theorem upperCross_not_ae_zero (k : Nat) {c q r : ℝ}
    (hc : 0 < c) (hq : 0 < q) (hr : 0 < r) :
    ¬ (upperCross k c q r =ᵐ[(volume : Measure (ℝ × ℝ)).restrict upperWedge]
      fun _ => 0) := by
  intro hz
  have heq : EqOn (upperCross k c q r) (fun _ => 0) upperWedge :=
    Measure.eqOn_open_of_ae_eq hz upperWedge_open
      (upperCross_continuous k c q r).continuousOn continuous_const.continuousOn
  apply island_witness_not_identically_zero k hc hq hr
  intro t ht
  rcases eq_or_lt_of_le ht with hzero | hpos
  · simp [← hzero]
  have heq' : (fun u => upperCross k c q r (t,u)) =ᶠ[𝓝[>] t] fun _ => (0 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact heq ⟨hpos, hu⟩
  have hlim : Tendsto (fun u => upperCross k c q r (t,u))
      (𝓝[>] t) (𝓝 (upperCross k c q r (t,t))) :=
    (((upperCross_continuous k c q r).comp
      (continuous_const.prodMk continuous_id)).tendsto t).mono_left nhdsWithin_le_nhds
  have hzeroLim : Tendsto (fun u => upperCross k c q r (t,u)) (𝓝[>] t) (𝓝 0) :=
    tendsto_const_nhds.congr' heq'.symm
  have hd := tendsto_nhds_unique hlim hzeroLim
  rwa [upperCross_diagonal] at hd

end Rhone.Statistics.Identifiability
