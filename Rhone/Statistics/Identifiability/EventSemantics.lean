/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.PanPostPair

/-! # Finite closure and material-conservation certificates for the ARG shapes -/

@[expose] public section

namespace Rhone.Statistics.Identifiability

def aCopies (s : MarkovChain.Identifiability.Shape) : Nat :=
  (s.map (fun g => g.countP MarkovChain.Identifiability.carriesA)).sum

def bCopies (s : MarkovChain.Identifiability.Shape) : Nat :=
  (s.map (fun g => g.countP MarkovChain.Identifiability.carriesB)).sum

def registeredShape (s : MarkovChain.Identifiability.Shape) : Bool :=
    (List.ofFn MarkovChain.Identifiability.shape).contains s

theorem shapes_distinct : (List.ofFn MarkovChain.Identifiability.shape).Nodup := by decide

theorem shape_material_counts : ∀ i : MarkovChain.Identifiability.State, aCopies
    (MarkovChain.Identifiability.shape i) = 2 ∧ bCopies (MarkovChain.Identifiability.shape i) = 2 :=
    by
  intro i
  fin_cases i <;> decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
theorem event_shapes_closed : ∀ i : MarkovChain.Identifiability.State,
    (MarkovChain.Identifiability.occupiedEvents (MarkovChain.Identifiability.shape i)).all
        registeredShape = true ∧
    (MarkovChain.Identifiability.emptyEvents (MarkovChain.Identifiability.shape i)).all
        registeredShape = true ∧
    (MarkovChain.Identifiability.recombinationEvents (MarkovChain.Identifiability.shape i)).all
        registeredShape = true ∧
    (MarkovChain.Identifiability.coalescenceEvents (MarkovChain.Identifiability.shape i)).all
        registeredShape = true := by
  intro i
  fin_cases i <;> decide

def mergerMaterialValid (e : Nat × MarkovChain.Identifiability.Shape) : Bool :=
  if e.1 == 0 then aCopies e.2 == 2 && bCopies e.2 == 2 else
  if e.1 == 1 then aCopies e.2 == 1 && bCopies e.2 == 2 else
  if e.1 == 2 then aCopies e.2 == 2 && bCopies e.2 == 1 else
  e.1 == 3 && aCopies e.2 == 1 && bCopies e.2 == 1

theorem merger_material_conservation : ∀ i : MarkovChain.Identifiability.State,
    (MarkovChain.Identifiability.mergerEvents (MarkovChain.Identifiability.shape i)).all
        mergerMaterialValid = true := by
  intro i
  fin_cases i <;> decide

theorem panPost_material_counts : ∀ i : Fin 2,
    aCopies (panPostShape i) = 1 ∧ bCopies (panPostShape i) = 2 := by decide

theorem panPost_events_closed : ∀ i : Fin 2,
    (MarkovChain.Identifiability.recombinationEvents (panPostShape i)).all
      (fun s => (List.ofFn panPostShape).contains s) = true ∧
    (MarkovChain.Identifiability.coalescenceEvents (panPostShape i)).all
      (fun s => (List.ofFn panPostShape).contains s) = true := by
  decide

theorem panPostGenerator_event_formula (rate recomb : ℝ) (i j : Fin 2) :
    panPostGenerator rate recomb i j =
      rate * (panPostRateCount MarkovChain.Identifiability.coalescenceEvents
          MarkovChain.Identifiability.killedCount i j : ℝ) +
      recomb * (panPostRateCount MarkovChain.Identifiability.recombinationEvents (fun _ => 0) i j :
          ℝ) := by
  rw [panPost_events_checked.1, panPost_events_checked.2.1]
  fin_cases i <;> fin_cases j <;> norm_num [panPostGenerator] <;> ring

end Rhone.Statistics.Identifiability
