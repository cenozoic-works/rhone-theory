/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.TwoIslandSpatial.Generators

/-! # Entrywise generator formulas without nested matrix-literal normalization -/

@[expose] public section

noncomputable section
namespace Rhone.Statistics.TwoIslandSpatial
open MarkovChain.Identifiability Identifiability IslandLabelledCherry

def preEntry (c m : ℝ) (i j : Fin 5) : ℝ :=
  if i.val = 0 then (if j.val = 0 then -3*c-3*m else if j.val = 4 then 0 else m) else
    if i.val = 4 then (if j.val = 0 then 0 else if j.val = 4 then -6*m else 2*m) else
      if j.val = 0 then m else if j.val = 4 then 0 else if i.val = j.val then -c-3*m else m

lemma labelledPre_entries (c m : ℝ) (i j : Fin 5) : labelledPre 0 c m i j = preEntry c m i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [labelledPre, totalMigration, preEntry]

def postEntry (c m : ℝ) (i j : Fin 2) : ℝ :=
  if i.val = 0 then (if j.val = 0 then -c-2*m else 2*m) else
    if j.val = 0 then 2*m else -2*m

lemma pairGenerator_entries (c m : ℝ) (i j : Fin 2) :
    pairGenerator 0 c m i j = postEntry c m i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [pairGenerator, totalMigration, postEntry]

def fluxEntry (c : ℝ) (i : Fin 3) (a : Fin 5) (b : Fin 2) : ℝ :=
  if a.val = 0 then (if b.val = 0 then c else 0) else
    if a.val = i.val+1 ∧ b.val = 1 then c else 0

lemma firstFlux_entries (c : ℝ) (i : Fin 3) (a : Fin 5) (b : Fin 2) :
    firstFlux c i a b = fluxEntry c i a b := by
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    norm_num [firstFlux, fluxEntry, Fin.ext_iff]

end Rhone.Statistics.TwoIslandSpatial
