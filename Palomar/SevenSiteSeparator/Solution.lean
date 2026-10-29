module

public import Rhone.Statistics.SevenSiteSeparator.Separation

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
namespace Rhone.Palomar.SevenSiteSeparator
open Rhone.Algebra MarkovChain Statistics
open ThreeSiteSeparator Algebra.Identifiability MarkovChain.Identifiability
    Statistics.Identifiability ThreeTipSites

theorem seven_site_separation {K : ℕ} (hK : 2 ≤ K)
    (r : ℝ → ℝ) (hr : LocallyIntegrable r volume) (hn : ∀ t, 0 ≤ r t)
    (ht : Tendsto (integratedClock r) atTop atTop) {k : ℝ} (hk : 0 < k) :
    law (uniformBlockRoots K 7 (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) hK)) 1
        (IslandThreeTimes.durationLaw 0 1 (1 / 100)) ≠
      law (uniformBlockRoots K 7 (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) hK)) k
        (PanThreeSample.durationLaw r) :=
  Statistics.SevenSiteSeparator.seven_site_separation hK r hr hn ht hk

end Rhone.Palomar.SevenSiteSeparator
end
