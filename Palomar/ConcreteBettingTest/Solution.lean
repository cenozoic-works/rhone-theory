module

public import Rhone.Statistics.ConcreteBettingFeatures.Testing

@[expose] public section

noncomputable section
open MeasureTheory Filter
namespace Rhone.Palomar.ConcreteBettingTest
open Rhone.Algebra MarkovChain Statistics
open ConcreteBettingFeatures ThreeTipSites ThreeSiteSeparator
open Algebra.Identifiability MarkovChain.Identifiability Statistics.Identifiability
    Identifiability.FinitePanelSampling

theorem concrete_uniform_pan_size (r : ℝ → ℝ) (hr : LocallyIntegrable r volume)
    (hn : ∀ t, 0 ≤ r t) (ht : Tendsto (integratedClock r) atTop atTop)
    {k : ℝ} (hk : 0 < k) {N : ℕ} (hN : 72000000000 ≤ N) :
    (iidLaw (law (uniformBlockRoots 4 3 (by norm_num)) k (PanThreeSample.durationLaw r)) N).real
      {z | concreteRejects z} ≤ (1 : ℝ) / 20 :=
  ConcreteBettingFeatures.concrete_uniform_pan_size r hr hn ht hk hN

theorem concrete_source_power_eighty :
    (4 : ℝ) / 5 ≤ (iidLaw
      (TwoIslandSpatial.spatialSequenceLaw (uniformBlockRoots 4 3 (by norm_num))
        2 1 (1 / 100)) 72000000000).real {z | concreteRejects z} :=
  ConcreteBettingFeatures.concrete_source_power_eighty

theorem concrete_source_power_ninety_five :
    (19 : ℝ) / 20 ≤ (iidLaw
      (TwoIslandSpatial.spatialSequenceLaw (uniformBlockRoots 4 3 (by norm_num))
        2 1 (1 / 100)) 250000000000).real {z | concreteRejects z} :=
  ConcreteBettingFeatures.concrete_source_power_ninety_five

end Rhone.Palomar.ConcreteBettingTest
end
