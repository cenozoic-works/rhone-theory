/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.BinnedPanLaw.Observation

/-! # Positive 64-bin candidate weights -/

@[expose] public section

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace Rhone.Statistics.ConcretePanGrid
open Algebra.Identifiability MarkovChain.Identifiability Identifiability BinnedPanLaw ThreeTipSites
    ThreeSiteSeparator
open ConcretePatternMoments

def histogramWeights : Fin 64 → ℝ := ![
  (24120570273 : ℝ) / 1000000000000,
  (10975546197 : ℝ) / 500000000000,
  (20646327367 : ℝ) / 1000000000000,
  (22462176191 : ℝ) / 1000000000000,
  (12199662517 : ℝ) / 500000000000,
  (24164302147 : ℝ) / 1000000000000,
  (11323438107 : ℝ) / 500000000000,
  (18567259773 : ℝ) / 1000000000000,
  (945870313 : ℝ) / 100000000000,
  (352751099 : ℝ) / 100000000000,
  (368153579 : ℝ) / 250000000000,
  (77338021 : ℝ) / 100000000000,
  (24768801 : ℝ) / 50000000000,
  (372015233 : ℝ) / 1000000000000,
  (317021989 : ℝ) / 1000000000000,
  (37437981 : ℝ) / 125000000000,
  (31754961 : ℝ) / 100000000000,
  (421917489 : ℝ) / 1000000000000,
  (453717739 : ℝ) / 500000000000,
  (2251670413 : ℝ) / 500000000000,
  (257013145443 : ℝ) / 1000000000000,
  (412303243 : ℝ) / 1000000000000,
  (52253569 : ℝ) / 500000000000,
  (9805829 : ℝ) / 200000000000,
  (2741103 : ℝ) / 100000000000,
  (16987881 : ℝ) / 1000000000000,
  (11361153 : ℝ) / 1000000000000,
  (8124649 : ℝ) / 1000000000000,
  (3102379 : ℝ) / 500000000000,
  (2534039 : ℝ) / 500000000000,
  (4466753 : ℝ) / 1000000000000,
  (1078963 : ℝ) / 250000000000,
  (4708011 : ℝ) / 1000000000000,
  (6129959 : ℝ) / 1000000000000,
  (5374693 : ℝ) / 500000000000,
  (3574053 : ℝ) / 62500000000,
  (206857015173 : ℝ) / 1000000000000,
  (230481533 : ℝ) / 1000000000000,
  (26446289 : ℝ) / 250000000000,
  (39660843 : ℝ) / 1000000000000,
  (129979 : ℝ) / 6250000000,
  (19907877 : ℝ) / 1000000000000,
  (18683091 : ℝ) / 500000000000,
  (219896889 : ℝ) / 40000000000,
  (4583521927 : ℝ) / 200000000000,
  (16743453691 : ℝ) / 1000000000000,
  (8625274821 : ℝ) / 500000000000,
  (16665878757 : ℝ) / 1000000000000,
  (16577033837 : ℝ) / 1000000000000,
  (2058830657 : ℝ) / 125000000000,
  (16404544953 : ℝ) / 1000000000000,
  (16336596313 : ℝ) / 1000000000000,
  (4067151809 : ℝ) / 250000000000,
  (16188036551 : ℝ) / 1000000000000,
  (4022184429 : ℝ) / 250000000000,
  (15972196693 : ℝ) / 1000000000000,
  (15843631703 : ℝ) / 1000000000000,
  (15696340187 : ℝ) / 1000000000000,
  (15526531609 : ℝ) / 1000000000000,
  (15352229499 : ℝ) / 1000000000000,
  (3766498781 : ℝ) / 250000000000,
  (7573199281 : ℝ) / 500000000000,
  (6916493431 : ℝ) / 500000000000,
  (8638782343 : ℝ) / 500000000000]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem histogram_weights_positive (i : Fin 64) : 0 < histogramWeights i := by
  fin_cases i <;> norm_num [histogramWeights]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem histogram_weights_sum : ∑ i, histogramWeights i = 1 := by
  norm_num [Fin.sum_univ_succ, histogramWeights]

theorem exists_proper_pan_histogram_observer :
    ∃ r : ℝ → ℝ, LocallyIntegrable r volume ∧ (∀ t, 0 ≤ r t) ∧
      Tendsto (integratedClock r) atTop atTop ∧
      ∀ x : Panel 4 3,
        mass (uniformBlockRoots 4 3 (by norm_num)) 2 (PanThreeSample.durationLaw r) x =
          tableMass (histogramMoments histogramWeights) (rowOf x) :=
  exists_pan_full_pattern_histogram (by norm_num) histogramWeights
    histogram_weights_positive histogram_weights_sum

end Rhone.Statistics.ConcretePanGrid
