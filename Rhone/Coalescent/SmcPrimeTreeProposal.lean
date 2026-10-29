/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.FiniteIntervalMaterialSampler
public import Mathlib.MeasureTheory.Constructions.Pi
public import Rhone.Coalescent.FiniteIntervalMaterialSelectionMass
public import Rhone.Coalescent.FiniteIntervalMaterialClock

/-!
# SMC′ tree proposals with old-branch retention during attachment

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess MeasureTheory

abbrev Branch (N : ℕ) := Finset (Fin N) × ℝ × ℝ

abbrev Tree (N : ℕ) := Σ m : ℕ, Fin m → Branch N

noncomputable def branchLength {N : ℕ} (b : Branch N) : ℝ := by
  classical
  exact if b.1 = ∅ ∨ b.1 = Finset.univ then 0 else max 0 (b.2.2 - b.2.1)

noncomputable def treeLength {N : ℕ} (T : Tree N) : ℝ := ∑ i, branchLength (T.2 i)

noncomputable def rootHeight {N : ℕ} (T : Tree N) : ℝ :=
  ((List.finRange T.1).map
    (fun i => if 0 < branchLength (T.2 i) then (T.2 i).2.2 else 0)).foldr max 0

noncomputable def activeBranches {N : ℕ} (T : Tree N) (t : ℝ) : Finset (Fin T.1) := by
  classical
  exact Finset.univ.filter (fun i => 0 < branchLength (T.2 i) ∧
    (T.2 i).2.1 ≤ t ∧ t < (T.2 i).2.2)

noncomputable def attachmentRate {N : ℕ} (T : Tree N) (t : ℝ) : ℝ :=
  if rootHeight T ≤ t then 1 else (activeBranches T t).card

noncomputable def nextBoundary {N : ℕ} (T : Tree N) (t : ℝ) : ℝ :=
  ((List.finRange T.1).flatMap (fun i => [(T.2 i).2.1, (T.2 i).2.2])).foldr
    (fun h a => if t < h then min h a else a) (rootHeight T)

noncomputable def attachmentAux {N : ℕ} (T : Tree N) : ℕ → ℝ → ℝ → ℝ
  | 0, t, e => t + e
  | k + 1, t, e =>
      if rootHeight T ≤ t then t + e else
        let h := nextBoundary T t
        let rate := attachmentRate T t
        if e < rate * (h - t) then t + e / rate
        else attachmentAux T k h (e - rate * (h - t))

noncomputable def attachmentTime {N : ℕ} (T : Tree N) (t e : ℝ) : ℝ :=
  attachmentAux T (2 * T.1 + 1) t e

noncomputable def cutPoint {N : ℕ} (T : Tree N) (u v : ℝ) : Option (Finset (Fin N) × ℝ) :=
  match chooseByRate (fun i => branchLength (T.2 i)) (List.finRange T.1)
      (u * treeLength T) with
  | none => none
  | some i => some ((T.2 i).1, (T.2 i).2.1 + ((T.2 i).2.2 - (T.2 i).2.1) * v)

noncomputable def attachmentTarget {N : ℕ} (T : Tree N) (t u : ℝ) : Finset (Fin N) :=
  if rootHeight T ≤ t then Finset.univ else
    match chooseByRate (fun _ => (1 : ℝ)) (activeBranches T t).toList
        (u * (activeBranches T t).card) with
    | none => Finset.univ
    | some i => (T.2 i).1

noncomputable def finiteBranch {N : ℕ} (c : Finset (Fin N)) (lo hi : ℝ) : Branch N := by
  classical
  exact (c, lo, if c = ∅ ∨ c = Finset.univ then lo else max lo hi)

noncomputable def belowCut {N : ℕ} (b : Branch N) (t : ℝ) : Branch N :=
  finiteBranch b.1 b.2.1 (min b.2.2 t)

noncomputable def betweenCutAttachment {N : ℕ} (b : Branch N)
    (s : Finset (Fin N)) (t a : ℝ) : Branch N :=
  finiteBranch (b.1 \ s) (max b.2.1 t) (min b.2.2 a)

noncomputable def aboveAttachment {N : ℕ} (b : Branch N)
    (s target : Finset (Fin N)) (a : ℝ) : Branch N := by
  classical
  exact finiteBranch ((b.1 \ s) ∪ if (b.1 ∩ target).Nonempty then s else ∅)
    (max b.2.1 a) b.2.2

def treeOfList {N : ℕ} (l : List (Branch N)) : Tree N := ⟨l.length, fun i => l.get i⟩

noncomputable def regraft {N : ℕ} (T : Tree N) (s target : Finset (Fin N))
    (t a : ℝ) : Tree N :=
  treeOfList
    (((List.finRange T.1).map (fun i => belowCut (T.2 i) t)) ++
      ((List.finRange T.1).map (fun i => betweenCutAttachment (T.2 i) s t a)) ++
      ((List.finRange T.1).map (fun i => aboveAttachment (T.2 i) s target a)) ++
      [finiteBranch s t a, finiteBranch (Finset.univ \ s) (rootHeight T) a])

abbrev ProposalNoise := Fin 5 → ℝ

abbrev Proposal (N : ℕ) := ℝ × (Unit ⊕ (Finset (Fin N) × ℝ × ℝ × Finset (Fin N))) × Tree N

noncomputable def proposal {N : ℕ} (R : ℝ) (T : Tree N) (u : ProposalNoise) : Proposal N :=
  let distance := -Real.log (u 0) / (R / 2 * treeLength T)
  match cutPoint T (u 1) (u 2) with
  | none => (distance, .inl (), T)
  | some (s, t) =>
      let a := attachmentTime T t (-Real.log (u 3))
      let target := attachmentTarget T a (u 4)
      (distance, .inr (s, t, a, target), regraft T s target t a)

theorem branchLength_nonneg {N : ℕ} (b : Branch N) : 0 ≤ branchLength b := by
  classical
  unfold branchLength
  split_ifs
  · exact le_rfl
  · exact le_max_left _ _

theorem treeLength_nonneg {N : ℕ} (T : Tree N) : 0 ≤ treeLength T :=
  Finset.sum_nonneg (fun i _ => branchLength_nonneg (T.2 i))

theorem branchChoice_mass {N : ℕ} (T : Tree N) (hT : 0 < treeLength T)
    (i : Fin T.1) :
    unitUniform {u | chooseByRate (fun j => branchLength (T.2 j))
      (List.finRange T.1) (u * treeLength T) = some i} =
      ENNReal.ofReal (branchLength (T.2 i) / treeLength T) := by
  have hs : ((List.finRange T.1).map (fun j => branchLength (T.2 j))).sum =
      treeLength T := by
    rw [← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]
    rfl
  simpa only [hs] using chooseByRate_uniform_mass_general
    (fun j => branchLength (T.2 j)) (List.finRange T.1) (List.nodup_finRange _)
    (fun j _ => branchLength_nonneg _) (hs ▸ hT) i (by simp)

theorem spatialDistance_cdf {N : ℕ} (R : ℝ) (T : Tree N)
    (h : 0 < R / 2 * treeLength T) (x : ℝ) :
    (unitUniform.map (fun u => -Real.log u / (R / 2 * treeLength T))) (Set.Iic x) =
      ENNReal.ofReal (1 - Real.exp (-(R / 2 * treeLength T * x))) :=
  inverseClock_cdf _ h x

end Rhone.Coalescent.SmcPrime
