module

public import Rhone.Statistics.IslandPairSpatialDesign
public import Rhone.Statistics.SpatialPairDesign.Separation
public import Rhone.Statistics.AsymmetricPairDesign.Separation
public import Rhone.Statistics.LinkedPairMoments.Expansion

@[expose] public section

namespace Rhone.Palomar.KnownStrataPairDesign

open MeasureTheory
open Coalescent.IslandPair Statistics.IslandPairSpatialDesign
open MarkovChain.Identifiability Statistics.Identifiability Statistics.PairObservationChannel

theorem pair_generator_eq_projected (n : ℕ) (c q : ℝ) (i j : Fin 2) :
    pairGenerator n c q i j =
      projectedGenerator (n + 2) ((n + 1) * q) c (transientCategory i)
        (transientCategory j) :=
  pairGenerator_eq_projectedGenerator n c q i j

theorem exit_rate_eq_projected (n : ℕ) (c q : ℝ) (i : Fin 2) :
    exitRate (pairGenerator n c q) i =
      projectedGenerator (n + 2) ((n + 1) * q) c (transientCategory i) none :=
  exitRate_pairGenerator n c q i

theorem spatial_laplace_gap (n : ℕ) {c q k : ℝ} (hc : 0 < c) (hq : 0 < q) (hk : 0 ≤ k) :
    pairLaplace (Rhone.Statistics.SpatialPairDesign.pairLaw n c q 0) k -
        pairLaplace (Rhone.Statistics.SpatialPairDesign.pairLaw n c q 1) k =
      c * k / pairLaplaceDenominator n c q k :=
  Statistics.SpatialPairDesign.pairLaplace_gap n hc hq hk

theorem spatial_separated_iff {K : ℕ} {H : Type*} [Fintype H] (E : Channel K H) (n : ℕ)
    {c q k : ℝ} (hc : 0 < c) (hq : 0 < q) (hk : 0 < k) :
    (∃ x y, reportedMass E
        (pairLaplace (Rhone.Statistics.SpatialPairDesign.pairLaw n c q 0) k) x y ≠
      reportedMass E
        (pairLaplace (Rhone.Statistics.SpatialPairDesign.pairLaw n c q 1) k) x y) ↔
      Informative E := by
  have hgap := Statistics.SpatialPairDesign.pairLaplace_gap n hc hq hk.le
  have hpos : 0 < c * k / pairLaplaceDenominator n c q k :=
    div_pos (mul_pos hc hk) (pairLaplaceDenominator_pos n hc hq hk.le)
  have hne : pairLaplace (Rhone.Statistics.SpatialPairDesign.pairLaw n c q 0) k ≠
      pairLaplace (Rhone.Statistics.SpatialPairDesign.pairLaw n c q 1) k := by
    intro h
    rw [h, sub_self] at hgap
    linarith
  have h := (reported_mass_eq_iff E
    (pairLaplace (Rhone.Statistics.SpatialPairDesign.pairLaw n c q 0) k)
    (pairLaplace (Rhone.Statistics.SpatialPairDesign.pairLaw n c q 1) k)).not
  push Not at h
  rw [h, ← retained_variance_pos_iff]
  constructor
  · rintro ⟨-, hv⟩
    exact lt_of_le_of_ne (retained_variance_nonneg E) (Ne.symm hv)
  · intro hv
    exact ⟨hne, hv.ne'⟩

theorem asymmetric_balance {a b c d k : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (hk : 0 ≤ k) :
    (k + a + b) * Rhone.Statistics.AsymmetricPairDesign.laplace a b c d k 1 =
      b * Rhone.Statistics.AsymmetricPairDesign.laplace a b c d k 0 +
        a * Rhone.Statistics.AsymmetricPairDesign.laplace a b c d k 2 :=
  Statistics.AsymmetricPairDesign.laplace_balance ha hb hc hd hk

theorem asymmetric_laplace_separation {a b c d k : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (hk : 0 < k) :
    Rhone.Statistics.AsymmetricPairDesign.laplace a b c d k 1 <
        Rhone.Statistics.AsymmetricPairDesign.laplace a b c d k 0 ∨
      Rhone.Statistics.AsymmetricPairDesign.laplace a b c d k 1 <
        Rhone.Statistics.AsymmetricPairDesign.laplace a b c d k 2 :=
  Statistics.AsymmetricPairDesign.laplace_separation ha hb hc hd hk

theorem asymmetric_no_common_law {K : ℕ} {H : Type*} [Fintype H] (E : Channel K H)
    (hK : 2 ≤ K) (hE : Informative E)
    {a b c d k : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hk : 0 < k) :
    ¬ ∃ Q : H × H → ℝ, ∀ i : Fin 3, ∀ x y,
      reportedMass E (Rhone.Statistics.AsymmetricPairDesign.laplace a b c d k i) x y =
        Q (x, y) := by
  rintro ⟨Q, hQ⟩
  have heq : ∀ i j : Fin 3,
      Statistics.AsymmetricPairDesign.reportedPairLaw E ha hb hc hd hk.le i =
        Statistics.AsymmetricPairDesign.reportedPairLaw E ha hb hc hd hk.le j := by
    intro i j
    apply Rhone.Statistics.LinkedPairMoments.finite_law_ext
    rintro ⟨x, y⟩
    exact (hQ i x y).trans (hQ j x y).symm
  rcases Statistics.AsymmetricPairDesign.reportedPairLaw_separation E hK hE ha hb hc hd hk
    with h | h
  · exact h (heq 1 0)
  · exact h (heq 1 2)

end Rhone.Palomar.KnownStrataPairDesign
