/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.EventSemantics
public import Rhone.Statistics.Identifiability.Panmixia

/-! # The full three-state panmictic generator before either locus coalesces -/

@[expose] public section

open scoped Matrix
namespace Rhone.Statistics.Identifiability

def panPreRateCount
    (events : MarkovChain.Identifiability.Shape → List MarkovChain.Identifiability.Shape)
    (killed : MarkovChain.Identifiability.Shape → Nat)
    (i j : PanState) : Int :=
  ((events (panShape i)).countP (fun s => s == panShape j) : Int) -
    if i = j then (events (panShape i)).length + killed (panShape i) else 0

theorem panPre_events_checked :
    (∀ i j, panPreRateCount MarkovChain.Identifiability.coalescenceEvents
        MarkovChain.Identifiability.killedCount i j =
      (!![-1,0,0;1,-3,0;0,4,-6] : Matrix PanState PanState Int) i j) ∧
    (∀ i j, panPreRateCount MarkovChain.Identifiability.recombinationEvents (fun _ => 0) i j =
      (!![-2,2,0;0,-1,1;0,0,0] : Matrix PanState PanState Int) i j) := by
  constructor <;> intro i j <;> fin_cases i <;> fin_cases j <;> decide

noncomputable def panPreGenerator (rate recomb : ℝ) : Matrix PanState PanState ℝ :=
  !![-rate-2*recomb,2*recomb,0;
     rate,-3*rate-recomb,recomb;
     0,4*rate,-6*rate]

theorem panPreGenerator_event_formula (rate recomb : ℝ) (i j : PanState) :
    panPreGenerator rate recomb i j =
      rate * (panPreRateCount MarkovChain.Identifiability.coalescenceEvents
          MarkovChain.Identifiability.killedCount i j : ℝ) +
      recomb * (panPreRateCount MarkovChain.Identifiability.recombinationEvents (fun _ => 0) i j :
          ℝ) := by
  rw [panPre_events_checked.1,panPre_events_checked.2]
  fin_cases i <;> fin_cases j <;> norm_num [panPreGenerator] <;> ring

theorem panPreGenerator_forward (rate recomb D R U : ℝ) :
    (fun i => ∑ j : PanState, (![D,R,U] : PanState → ℝ) j * panPreGenerator rate recomb j i) =
      ![-(rate+2*recomb)*D+rate*R,
        2*recomb*D-(3*rate+recomb)*R+4*rate*U,
        recomb*R-6*rate*U] := by
  ext i
  fin_cases i <;> simp [panPreGenerator,Fin.sum_univ_succ] <;> ring

theorem panPre_firstA_flux (rate D R U : ℝ) :
    panFirstA rate ![D,R,U] = rate*(R+U) := by
  simp [panFirstA,pan_event_counts.1,Fin.sum_univ_succ]

end Rhone.Statistics.Identifiability
