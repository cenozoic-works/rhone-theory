/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeTreeProposal
public import Rhone.Coalescent.FiniteIntervalGenealogyLawSupport

/-! # Finite Kingman histories for SMC′ initialization and one-split skeletons -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess MeasureTheory

abbrev KingmanHistory (N : ℕ) := Fin N → AugmentedState

noncomputable def kingmanHistoryLaw (N : ℕ) : Measure (KingmanHistory N) :=
  ((eventProcess false 0).pathLaw (initialState N, (0, .inl ()))).map
    (fun ω => fun k : Fin N => ω k.val)

def historyExtension (N : ℕ) (h : KingmanHistory N) : EventPath :=
  fun k => if hk : k < N then h ⟨k, hk⟩ else (initialState N, (0, .inl ()))

def leftBoundaryProbe : GenomicProbe := ⟨0, by norm_num⟩

noncomputable def pairBirthTime (ω : EventPath) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | k + 1, a =>
    match (ω (k + 1)).2.2 with
    | .inr (.inl ij) =>
      if ij.1 < ij.2 ∧ ij.2 < (ω k).1.2.2.1 ∧ a = (ω k).1.2.1 then
        (ω (k + 1)).1.1 else pairBirthTime ω k a
    | _ => pairBirthTime ω k a

noncomputable def historyClade (N : ℕ) (h : KingmanHistory N) (k a : ℕ) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter (fun i => ancestorLabel N (historyExtension N h)
    leftBoundaryProbe i k = a)

noncomputable def historyChildBranch (N : ℕ) (h : KingmanHistory N)
    (k : Fin (N - 1)) (right : Bool) : Branch N :=
  let ω := historyExtension N h
  match (ω (k.val + 1)).2.2 with
  | .inr (.inl ij) =>
    if ij.1 < ij.2 ∧ ij.2 < (ω k.val).1.2.2.1 then
      let index := if right then ij.2 else ij.1
      let a := liveLabelAt (ω k.val).1 index
      finiteBranch (historyClade N h k.val a) (pairBirthTime ω k.val a) (ω (k.val + 1)).1.1
    else finiteBranch ∅ 0 0
  | _ => finiteBranch ∅ 0 0

noncomputable def metricTreeFromHistory (N : ℕ) (h : KingmanHistory N) : Tree N :=
  treeOfList ((List.finRange (N - 1)).flatMap
    (fun k => [historyChildBranch N h k false, historyChildBranch N h k true]))

abbrev OneSplitSkeleton (N : ℕ) :=
  KingmanHistory N × ℕ × ℝ × ℝ × ℝ × Finset (Fin N)

theorem kingmanHistoryMap_measurable (N : ℕ) :
    Measurable (fun ω : EventPath => fun k : Fin N => ω k.val) :=
  measurable_pi_iff.mpr (fun k => measurable_pi_apply k.val)

instance kingmanHistoryLaw_probability (N : ℕ) : IsProbabilityMeasure (kingmanHistoryLaw N) := by
  unfold kingmanHistoryLaw
  infer_instance

end Rhone.Coalescent.SmcPrime
