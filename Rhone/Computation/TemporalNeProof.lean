/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.TemporalNe
public import Rhone.Statistics.TemporalNe
public import Mathlib.Basic.Real.Basic

/-! # Executable temporal moments equal the specification -/

@[expose] public section
namespace Rhone.Computation.TemporalNe
open MarkovChain Statistics.TemporalNe

theorem retention_eq (N t : Nat) :
    ((retention N t : Rat) : ℝ) = (1 - 1 / (N : ℝ)) ^ t := by
  simp [retention]

theorem p0_eq (N i : Nat) : ((p0 N i : Rat) : ℝ) = (i : ℝ) / N := by
  simp [p0]

theorem driftSecondMoment_eq (N t : Nat) (i : Fin (N + 1)) :
    ((driftSecondMoment N t i : Rat) : ℝ) =
      (wf N).expectIter t (fun j => ((j : ℝ) / N - (i : ℝ) / N) ^ 2) i := by
  rw [wf_drift_second_moment]
  simp [driftSecondMoment, retention, p0]

theorem standardizedDrift_eq (N t : Nat) (i : Fin (N + 1)) (h0 : 0 < (i : ℕ))
    (hN : (i : ℕ) < N) :
    ((standardizedDrift N t : Rat) : ℝ) =
      (wf N).expectIter t (fun j => ((j : ℝ) / N - (i : ℝ) / N) ^ 2) i /
        (((i : ℝ) / N) * (1 - (i : ℝ) / N)) := by
  rw [wf_standardized_drift_variance N t i h0 hN]
  simp [standardizedDrift, retention]

theorem expectedFrequencyHet_eq (N t : Nat) (i : Fin (N + 1)) :
    ((expectedFrequencyHet N t i : Rat) : ℝ) =
      (wf N).expectIter t (fun j => ((j : ℝ) / N) * (1 - (j : ℝ) / N)) i := by
  rw [wf_expected_frequency_het]
  simp [expectedFrequencyHet, retention, p0]

theorem sampledMsd_eq (N t S0 St : Nat) (i : Fin (N + 1)) (hS0 : 0 < S0) (hSt : 0 < St) :
    ((sampledMsd N t S0 St i : Rat) : ℝ) =
      sampledExpect N t S0 St i (fun x0 xt => ((xt : ℝ) / St - (x0 : ℝ) / S0) ^ 2) := by
  rw [temporal_sampled_msd_closed N t S0 St i hS0 hSt]
  simp [sampledMsd, retention, p0]

end Rhone.Computation.TemporalNe
