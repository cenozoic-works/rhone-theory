/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.JointRestriction

/-! # Separately observable diagonal and triangular parts of a symmetric joint law -/

@[expose] public section

open Set MeasureTheory
namespace Rhone.Statistics.Identifiability

set_option backward.isDefEq.respectTransparency false

def timeDiagonal : Set (ℝ × ℝ) := {p | p.1 = p.2}

theorem timeDiagonal_measurable : MeasurableSet timeDiagonal :=
  (isClosed_eq continuous_fst continuous_snd).measurableSet

noncomputable def diagonalDensityLaw (δ : ℝ → ℝ) : Measure (ℝ × ℝ) :=
  ((volume.restrict (Ioi (0 : ℝ))).withDensity (fun t => ENNReal.ofReal (δ t))).map
    (fun t => (t,t))
noncomputable def triangularDensityLaw (j : ℝ × ℝ → ℝ) : Measure (ℝ × ℝ) :=
  (planeVolume.restrict upperWedge).withDensity (fun p => ENNReal.ofReal (j p))
noncomputable def regularJointLaw (δ : ℝ → ℝ) (j : ℝ × ℝ → ℝ) : Measure (ℝ × ℝ) :=
  diagonalDensityLaw δ + triangularDensityLaw j + (triangularDensityLaw j).map Prod.swap

theorem upper_inter_diagonal_empty : timeDiagonal ∩ upperWedge = ∅ := by
  ext p
  simp only [mem_inter_iff,mem_empty_iff_false,iff_false,not_and]
  intro hd hu
  have : p.1 = p.2 := hd
  have : p.1 < p.2 := hu.2
  linarith

theorem swapped_upper_inter_upper_empty : Prod.swap ⁻¹' upperWedge ∩ upperWedge = ∅ := by
  ext p
  simp only [mem_inter_iff,mem_empty_iff_false,iff_false,not_and]
  intro hs hu
  have h₁ : p.2 < p.1 := hs.2
  have h₂ : p.1 < p.2 := hu.2
  linarith

theorem triangular_restrict_diagonal (j : ℝ × ℝ → ℝ) :
    (triangularDensityLaw j).restrict timeDiagonal = 0 := by
  rw [triangularDensityLaw,restrict_withDensity timeDiagonal_measurable,
    Measure.restrict_restrict timeDiagonal_measurable,upper_inter_diagonal_empty,
    Measure.restrict_empty,withDensity_zero_left]

theorem triangular_restrict_upper (j : ℝ × ℝ → ℝ) :
    (triangularDensityLaw j).restrict upperWedge = triangularDensityLaw j := by
  rw [triangularDensityLaw,restrict_withDensity upperWedge_open.measurableSet,
    Measure.restrict_restrict upperWedge_open.measurableSet,inter_self]

theorem swapped_triangular_restrict_upper (j : ℝ × ℝ → ℝ) :
    ((triangularDensityLaw j).map Prod.swap).restrict upperWedge = 0 := by
  rw [Measure.restrict_map (f := Prod.swap)
    (measurable_snd.prodMk measurable_fst) upperWedge_open.measurableSet]
  have hm : MeasurableSet (Prod.swap ⁻¹' upperWedge) :=
    upperWedge_open.measurableSet.preimage (measurable_snd.prodMk measurable_fst)
  rw [triangularDensityLaw,restrict_withDensity hm,Measure.restrict_restrict hm,
    swapped_upper_inter_upper_empty,Measure.restrict_empty,withDensity_zero_left,Measure.map_zero]

theorem diagonal_restrict_upper (δ : ℝ → ℝ) :
    (diagonalDensityLaw δ).restrict upperWedge = 0 := by
  rw [diagonalDensityLaw,Measure.restrict_map (f := fun t : ℝ => (t,t))
    (measurable_id.prodMk measurable_id)
    upperWedge_open.measurableSet]
  have hs : (fun t : ℝ => (t,t)) ⁻¹' upperWedge = ∅ := by
    ext t
    simp [upperWedge]
  rw [hs,Measure.restrict_empty,Measure.map_zero]

theorem diagonal_restrict_diagonal (δ : ℝ → ℝ) :
    (diagonalDensityLaw δ).restrict timeDiagonal = diagonalDensityLaw δ := by
  rw [diagonalDensityLaw,Measure.restrict_map (f := fun t : ℝ => (t,t))
    (measurable_id.prodMk measurable_id)
    timeDiagonal_measurable]
  have hs : (fun t : ℝ => (t,t)) ⁻¹' timeDiagonal = univ := by
    ext t
    simp [timeDiagonal]
  rw [hs,Measure.restrict_univ]

theorem swapped_triangular_restrict_diagonal (j : ℝ × ℝ → ℝ) :
    ((triangularDensityLaw j).map Prod.swap).restrict timeDiagonal = 0 := by
  rw [Measure.restrict_map (f := Prod.swap)
    (measurable_snd.prodMk measurable_fst) timeDiagonal_measurable]
  have hs : Prod.swap ⁻¹' timeDiagonal = timeDiagonal := by
    ext p
    simp [timeDiagonal,eq_comm]
  rw [hs,triangular_restrict_diagonal,Measure.map_zero]

theorem regularJointLaw_restrict_upper (δ : ℝ → ℝ) (j : ℝ × ℝ → ℝ) :
    (regularJointLaw δ j).restrict upperWedge = triangularDensityLaw j := by
  rw [regularJointLaw,Measure.restrict_add,Measure.restrict_add,
    diagonal_restrict_upper,triangular_restrict_upper,swapped_triangular_restrict_upper]
  simp

theorem regularJointLaw_restrict_diagonal (δ : ℝ → ℝ) (j : ℝ × ℝ → ℝ) :
    (regularJointLaw δ j).restrict timeDiagonal = diagonalDensityLaw δ := by
  rw [regularJointLaw,Measure.restrict_add,Measure.restrict_add,
    diagonal_restrict_diagonal,triangular_restrict_diagonal,swapped_triangular_restrict_diagonal]
  simp

theorem diagonalDensityLaw_map_fst (δ : ℝ → ℝ) :
    (diagonalDensityLaw δ).map Prod.fst =
      (volume.restrict (Ioi (0 : ℝ))).withDensity (fun t => ENNReal.ofReal (δ t)) := by
  rw [diagonalDensityLaw,Measure.map_map (f := fun t : ℝ => (t,t))
    measurable_fst (measurable_id.prodMk measurable_id)]
  change Measure.map id _ = _
  rw [Measure.map_id]

end Rhone.Statistics.Identifiability
