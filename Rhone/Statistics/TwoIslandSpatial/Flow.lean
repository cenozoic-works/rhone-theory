/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.TwoIslandSpatial.Lumping
public import Rhone.Statistics.TwoIslandSpatial.ExpIntertwining

/-! # Full spatial semigroup and labelled merger-density lumping -/

@[expose] public section

noncomputable section
open scoped Matrix Matrix.Norms.Operator
namespace Rhone.Statistics.TwoIslandSpatial
open MarkovChain.Identifiability Identifiability IslandLabelledCherry

lemma spatial_pre_flow (c m t : ℝ) :
    NormedSpace.exp (t • spatialPre c m) * preLump =
      preLump * NormedSpace.exp (t • labelledPre 0 c m) := by
  apply spatial_exp_intertwining
  rw [Matrix.smul_mul, Matrix.mul_smul, spatial_pre_lumping]

lemma spatial_post_flow (c m t : ℝ) :
    NormedSpace.exp (t • spatialPost c m) * postLump =
      postLump * NormedSpace.exp (t • pairGenerator 0 c m) := by
  apply spatial_exp_intertwining
  rw [Matrix.smul_mul, Matrix.mul_smul, spatial_post_lumping]

lemma preLump_initial (v : Fin 5 → ℝ) : (preLump *ᵥ v) (0,0,0) = v 0 := by
  norm_num [preLump, preShape, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

lemma spatial_absorption_exit (c m : ℝ) :
    spatialAbsorption c = postLump *ᵥ exitRate (pairGenerator 0 c m) := by
  rw [pair_exitRate, spatial_absorption_lumping]
  rfl

def spatialDensity (c m : ℝ) (i : Fin 3) (p : ℝ × ℝ) : ℝ :=
  ((NormedSpace.exp (p.1 • spatialPre c m) * spatialFlux c i *
    NormedSpace.exp ((p.2-p.1) • spatialPost c m)) *ᵥ spatialAbsorption c) (0,0,0)

lemma spatial_density_lumped (c m : ℝ) (i : Fin 3) (p : ℝ × ℝ) :
    spatialDensity c m i p = density 0 c m i p := by
  have he : (NormedSpace.exp (p.1 • spatialPre c m) * spatialFlux c i *
      NormedSpace.exp ((p.2-p.1) • spatialPost c m)) * postLump =
        preLump * (NormedSpace.exp (p.1 • labelledPre 0 c m) * firstFlux c i *
          NormedSpace.exp ((p.2-p.1) • pairGenerator 0 c m)) := by
    rw [Matrix.mul_assoc, spatial_post_flow, ← Matrix.mul_assoc,
      Matrix.mul_assoc (NormedSpace.exp (p.1 • spatialPre c m)), spatial_flux_lumping,
      ← Matrix.mul_assoc, spatial_pre_flow]
    simp only [Matrix.mul_assoc]
  unfold spatialDensity
  rw [spatial_absorption_exit c m, Matrix.mulVec_mulVec, he,
    ← Matrix.mulVec_mulVec, preLump_initial, ← Matrix.mulVec_mulVec]
  unfold density entryFlux IslandThreeTimes.postDensity flowOutput
  simp only [pow_zero, Matrix.one_mul, Matrix.mulVec, dotProduct]

lemma spatial_density_factor (c m : ℝ) (i : Fin 3) (p : ℝ × ℝ) :
    spatialDensity c m i p = (1/3 : ℝ)*IslandThreeTimes.density 0 c m p := by
  rw [spatial_density_lumped, density_factor]

end Rhone.Statistics.TwoIslandSpatial
