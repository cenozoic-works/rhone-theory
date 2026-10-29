module

public import Rhone.Statistics.CollapsedGenealogy.Boundary
public import Rhone.Statistics.CollapsedGenealogy.Equivalence

@[expose] public section

namespace Rhone.Palomar.CollapsedGenealogy

open MeasureTheory
open Statistics.ThreeTipSites Statistics.ThreeSiteSeparator
open Statistics.CollapsedGenealogy

theorem all_blocks_iff_collapsed_joint_eq {K : ℕ} (hK : 2 ≤ K)
    {k l : ℝ} (hk : 0 ≤ k) (hl : 0 ≤ l) (μ ν : Measure Joint)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμ : NonnegativeJoint μ) (hν : NonnegativeJoint ν) :
    (∀ L : ℕ,
      jointSequenceLaw (uniformBlockRoots K L (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) hK)) k μ =
        jointSequenceLaw (uniformBlockRoots K L (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) hK)) l ν) ↔
      object k μ = object l ν :=
  Rhone.Statistics.CollapsedGenealogy.all_blocks_iff_collapsed_joint_eq hK hk hl μ ν hμ hν

theorem star_labels_same_sequence_law {K L : ℕ} (hK : 0 < K) (k u : ℝ)
    (q p : Fin 3) :
    jointSequenceLaw (uniformBlockRoots K L hK) k (Measure.dirac ((u, 0), q)) =
      jointSequenceLaw (uniformBlockRoots K L hK) k (Measure.dirac ((u, 0), p)) :=
  Rhone.Statistics.CollapsedGenealogy.star_labels_same_sequence_law hK k u q p

end Rhone.Palomar.CollapsedGenealogy
