/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.IslandLabelledCherry.Factorization

/-! # Full labelled spatial generators for three and two lineages in two demes -/

@[expose] public section

noncomputable section
open scoped BigOperators Matrix
namespace Rhone.Statistics.TwoIslandSpatial
open MarkovChain.Identifiability Identifiability IslandLabelledCherry

abbrev ThreeDemes := Fin 2 × Fin 2 × Fin 2
abbrev TwoDemes := Fin 2 × Fin 2

def samePairs (x : ThreeDemes) : ℝ :=
  (if x.1 = x.2.1 then 1 else 0)+(if x.1 = x.2.2 then 1 else 0)+
    (if x.2.1 = x.2.2 then 1 else 0)

def threeDistance (x y : ThreeDemes) : ℕ :=
  (if x.1 = y.1 then 0 else 1)+(if x.2.1 = y.2.1 then 0 else 1)+
    (if x.2.2 = y.2.2 then 0 else 1)

def spatialPre (c m : ℝ) : Matrix ThreeDemes ThreeDemes ℝ := fun x y =>
  if x = y then -(3*m+c*samePairs x) else if threeDistance x y = 1 then m else 0

def preShape (x : ThreeDemes) : Fin 5 :=
  if x.1 = x.2.1 ∧ x.1 = x.2.2 then 0 else
    if x.1 = x.2.1 then 1 else if x.2.1 = x.2.2 then 2 else 3

def preLump : Matrix ThreeDemes (Fin 5) ℝ := fun x i =>
  if i.val = 0 then (if x.1 = x.2.1 ∧ x.1 = x.2.2 then 1 else 0) else
    if i.val = 1 then (if x.1 = x.2.1 ∧ x.1 ≠ x.2.2 then 1 else 0) else
      if i.val = 2 then (if x.2.1 = x.2.2 ∧ x.1 ≠ x.2.1 then 1 else 0) else
        if i.val = 3 then (if x.1 = x.2.2 ∧ x.1 ≠ x.2.1 then 1 else 0) else 0

def twoDistance (x y : TwoDemes) : ℕ :=
  (if x.1 = y.1 then 0 else 1)+(if x.2 = y.2 then 0 else 1)

def spatialPost (c m : ℝ) : Matrix TwoDemes TwoDemes ℝ := fun x y =>
  if x = y then -(2*m+if x.1 = x.2 then c else 0) else
    if twoDistance x y = 1 then m else 0

def postShape (x : TwoDemes) : Fin 2 := if x.1 = x.2 then 0 else 1

def postLump : Matrix TwoDemes (Fin 2) ℝ := fun x i =>
  if i.val = 0 then (if x.1 = x.2 then 1 else 0) else (if x.1 = x.2 then 0 else 1)

def pairTogether (x : ThreeDemes) (i : Fin 3) : Prop :=
  if i.val = 0 then x.1 = x.2.1 else if i.val = 1 then x.2.1 = x.2.2 else x.1 = x.2.2

instance pairTogether_decidable (x : ThreeDemes) (i : Fin 3) : Decidable (pairTogether x i) := by
  unfold pairTogether
  infer_instance

def postDemes (x : ThreeDemes) (i : Fin 3) : TwoDemes :=
  if i.val = 0 then (x.1, x.2.2) else if i.val = 1 then (x.2.1, x.1) else (x.1, x.2.1)

def spatialFlux (c : ℝ) (i : Fin 3) : Matrix ThreeDemes TwoDemes ℝ := fun x y =>
  if pairTogether x i ∧ postDemes x i = y then c else 0

def spatialAbsorption (c : ℝ) (x : TwoDemes) : ℝ := if x.1 = x.2 then c else 0

end Rhone.Statistics.TwoIslandSpatial
