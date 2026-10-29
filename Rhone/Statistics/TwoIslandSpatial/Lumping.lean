/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.TwoIslandSpatial.Entries

/-! # Exact lumping identities, checked on the complete two-deme spatial state spaces -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Matrix
namespace Rhone.Statistics.TwoIslandSpatial
open MarkovChain.Identifiability Identifiability IslandLabelledCherry

lemma spatial_pre_lumping (c m : ℝ) :
    spatialPre c m * preLump = preLump * labelledPre 0 c m := by
  ext x j
  simp only [Matrix.mul_apply, labelledPre_entries]
  rcases x with ⟨a,b,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases d <;> fin_cases j <;>
    norm_num [spatialPre, threeDistance, samePairs, preLump, preShape, preEntry,
      totalMigration, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_succ] <;> ring

lemma spatial_post_lumping (c m : ℝ) :
    spatialPost c m * postLump = postLump * pairGenerator 0 c m := by
  ext x j
  simp only [Matrix.mul_apply, pairGenerator_entries]
  rcases x with ⟨a,b⟩
  fin_cases a <;> fin_cases b <;> fin_cases j <;>
    norm_num [spatialPost, twoDistance, postLump, postShape, postEntry,
      totalMigration, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_succ] <;> ring

lemma spatial_flux_lumping (c : ℝ) (i : Fin 3) :
    spatialFlux c i * postLump = preLump * firstFlux c i := by
  ext x j
  simp only [Matrix.mul_apply, firstFlux_entries]
  rcases x with ⟨a,b,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases d <;> fin_cases i <;> fin_cases j <;>
    norm_num [spatialFlux, pairTogether, postDemes, preLump, preShape, postLump, postShape,
      fluxEntry, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_succ]

lemma spatial_absorption_lumping (c : ℝ) :
    spatialAbsorption c = postLump *ᵥ ![c, 0] := by
  ext x
  rcases x with ⟨a,b⟩
  fin_cases a <;> fin_cases b <;>
    norm_num [spatialAbsorption, postLump, postShape,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

end Rhone.Statistics.TwoIslandSpatial
