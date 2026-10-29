/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ConcretePanGrid.MomentValuesSingle
public import Rhone.Statistics.ConcretePanGrid.MomentValuesCross

/-! # Exact quadrature, factored into bounded cell calculations -/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace Rhone.Statistics.ConcretePanGrid
open BinnedPanLaw ConcretePatternMoments QuadratureValues

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem histogram_quadrature_certificate (j : Fin 19) :
    momentQuadrature histogramWeights (exponents j).1 (exponents j).2 = candidateMoments j := by
  fin_cases j
  all_goals norm_num [exponents, candidateMoments, momentQuadrature, mixedQuadrature,
    weighted_value_1, weighted_value_3, weighted_value_5, cube_value_0, cube_value_1,
        cube_value_2, cube_value_3, cube_value_4, cube_value_5, cube_value_6, cube_value_7,
        cross_value_0_1, cross_value_0_3, cross_value_0_5, cross_value_1_1, cross_value_1_3,
        cross_value_1_5, cross_value_2_1, cross_value_2_3, cross_value_2_5, cross_value_3_1,
        cross_value_3_3, cross_value_4_1]

theorem histogram_moment_table : histogramMoments histogramWeights = candidateMoments := by
  funext j
  rw [histogram_table_quadrature (by norm_num) histogramWeights
    histogram_weights_positive histogram_weights_sum, histogram_quadrature_certificate]

end Rhone.Statistics.ConcretePanGrid
