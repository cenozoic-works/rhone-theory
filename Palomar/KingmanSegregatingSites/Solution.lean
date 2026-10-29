module

public import Rhone.Statistics.WattersonMarkedMoments
public import Rhone.Statistics.TajimaVariance

@[expose] public section

namespace Rhone.Palomar.KingmanSegregatingSites

open Coalescent Probability Statistics MeasureTheory ProbabilityTheory
open scoped NNReal

theorem markedKingmanSegregating_mean {n : ℕ} (hn : 2 ≤ n) (θ : ℝ≥0) :
    (∫ x, markedKingmanSegregating n x ∂markedKingmanLaw n θ) =
      (θ : ℝ) * (tajimaA1 n : ℝ) :=
  Rhone.Statistics.markedKingmanSegregating_mean hn θ

theorem markedKingmanSegregating_variance {n : ℕ} (hn : 2 ≤ n) (θ : ℝ≥0) :
    ProbabilityTheory.variance (markedKingmanSegregating n) (markedKingmanLaw n θ) =
      (θ : ℝ) * (tajimaA1 n : ℝ) + (θ : ℝ) ^ 2 * (tajimaA2 n : ℝ) :=
  Rhone.Statistics.markedKingmanSegregating_variance hn θ

theorem markedKingmanWatterson_mean {n : ℕ} (hn : 2 ≤ n) (θ : ℝ≥0) :
    (∫ x, markedKingmanWatterson n x ∂markedKingmanLaw n θ) = (θ : ℝ) :=
  Rhone.Statistics.markedKingmanWatterson_mean hn θ

theorem markedKingmanWatterson_variance {n : ℕ} (hn : 2 ≤ n) (θ : ℝ≥0) :
    ProbabilityTheory.variance (markedKingmanWatterson n) (markedKingmanLaw n θ) =
      (θ : ℝ) / (tajimaA1 n : ℝ) +
        (θ : ℝ) ^ 2 * (tajimaA2 n : ℝ) / (tajimaA1 n : ℝ) ^ 2 :=
  Rhone.Statistics.markedKingmanWatterson_variance hn θ

theorem markedKingmanPi_mean {n : ℕ} (hn : 2 ≤ n) (θ : ℝ≥0) :
    ∫ x, markedKingmanPi n x ∂markedKingmanLaw n θ = θ :=
  Rhone.Statistics.markedKingmanPi_mean hn θ

theorem markedKingmanPi_variance {n : ℕ} (hn : 2 ≤ n) (θ : ℝ≥0) :
    ∫ x, (markedKingmanPi n x - θ) ^ 2 ∂markedKingmanLaw n θ =
      (Rhone.Statistics.tajimaB1 n : ℝ) * θ +
        (Rhone.Statistics.tajimaB2 n : ℝ) * (θ : ℝ) ^ 2 :=
  Rhone.Statistics.markedKingmanPi_variance hn θ

end Rhone.Palomar.KingmanSegregatingSites
