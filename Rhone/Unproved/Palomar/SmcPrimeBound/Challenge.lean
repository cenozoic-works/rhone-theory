module

public import Mathlib

set_option maxSynthPendingDepth 3

@[expose] public section

elab "clear_aux_proof_cache" : command => do
  Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
  let ext ← unsafe Lean.Elab.Command.liftCoreM
    (Lean.evalConst (Lean.EnvExtension (Lean.PersistentHashMap Nat Nat))
      (Lean.Name.mkNum `_private.Lean.Meta.Match.Match 0 ++ `Lean.Meta.Match.matcherExt))
  Lean.modifyEnv fun env => ext.setState env {}

elab "set_main_module " m:ident : command =>
  Lean.modifyEnv fun env => env.setMainModule m.getId

clear_aux_proof_cache
set_main_module Rhone.Coalescent.SmcBound.Race

noncomputable section
namespace Rhone.Coalescent.SmcBound

def raceBound (h : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => raceBound h n + h n * (1 - raceBound h n)

def hazard (R : ℝ) (j : ℕ) : ℝ := R / ((j : ℝ) + 1 + R)

def harmonic : ℕ → ℝ
  | 0 => 0
  | n + 1 => harmonic n + 1 / ((n : ℝ) + 1)

end Rhone.Coalescent.SmcBound
end

clear_aux_proof_cache
set_main_module Rhone.Coalescent.SmcBound.Bounds

noncomputable section
namespace Rhone.Coalescent.SmcBound

def doubleBound (R : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => (1 - hazard R n) * doubleBound R n +
      hazard R n * raceBound (hazard R) (n + 2)

def quadraticCoefficient : ℕ → ℝ
  | 0 => 0
  | n + 1 => quadraticCoefficient n + harmonic (n + 2) / ((n : ℝ) + 1)

end Rhone.Coalescent.SmcBound
end

clear_aux_proof_cache
set_main_module Rhone.Probability.ProbabilityTotalVariation

namespace Rhone.Probability
open MeasureTheory
open scoped ENNReal symmDiff
variable {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
  [MeasurableSpace β]
attribute [-instance] CompletePartialOrder.toSupSet

noncomputable def eventTV (ν κ : Measure α) : ℝ≥0∞ :=
  ⨆ (s : Set α) (_ : MeasurableSet s), ENNReal.ofReal |ν.real s - κ.real s|

end Rhone.Probability

clear_aux_proof_cache
set_main_module Rhone.MarkovChain.Process

namespace Rhone.MarkovChain

open MeasureTheory ProbabilityTheory Finset Preorder

structure DiscreteProcess (S : Type*) [MeasurableSpace S] where

  step : Kernel S S

  [isMarkov : IsMarkovKernel step]

namespace DiscreteProcess

variable {S : Type*} [MeasurableSpace S] (P : DiscreteProcess S)

instance : IsMarkovKernel P.step := P.isMarkov

noncomputable def stepSeq (m : ℕ) : Kernel ((_ : Iic m) → S) S :=
  P.step.comap (fun x => x ⟨m, mem_Iic.2 le_rfl⟩) (measurable_pi_apply _)

instance (m : ℕ) : IsMarkovKernel (P.stepSeq m) := by
  rw [stepSeq]
  infer_instance

noncomputable def traj : Kernel S (ℕ → S) :=
  (Kernel.traj (X := fun _ => S) P.stepSeq 0).comap (fun x _ => x)
    (measurable_pi_iff.2 fun _ => measurable_id)

instance : IsMarkovKernel P.traj := by
  rw [traj]
  infer_instance

noncomputable def pathLaw (x : S) : Measure (ℕ → S) := P.traj x

instance (x : S) : IsProbabilityMeasure (P.pathLaw x) := by
  rw [pathLaw]
  infer_instance

noncomputable def law (μ₀ : Measure S) : Measure (ℕ → S) := μ₀.bind P.traj

end DiscreteProcess

end Rhone.MarkovChain

clear_aux_proof_cache
set_main_module Rhone.Coalescent.FiniteIntervalMaterialState

namespace Rhone.Coalescent.IntervalProcess

abbrev Material := (k : ℕ) × (Fin (k + 1) → (ℝ × ℝ))
abbrev LiveState := (m : ℕ) × (Fin m → (ℕ × Material))
abbrev State := ℝ × ℕ × LiveState
abbrev Event := Unit ⊕ ((ℕ × ℕ) ⊕ (ℕ × ℝ))
abbrev EventRecord := ℝ × Event
abbrev Noise := Fin 3 → ℝ
abbrev Mode := Bool

noncomputable def hullLo (a : Material) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty
    (fun i => if (a.2 i).1 < (a.2 i).2 then (a.2 i).1 else 1)

noncomputable def hullHi (a : Material) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun i => if (a.2 i).1 < (a.2 i).2 then (a.2 i).2 else 0)

noncomputable def hullLength (a : Material) : ℝ := max 0 (hullHi a - hullLo a)

noncomputable def touches (a b : Material) : Prop :=
  hullLo a ≤ hullHi b ∧ hullLo b ≤ hullHi a

noncomputable def splitMaterial (a : Material) (x : ℝ) : Material × Material :=
  (⟨a.1, fun i => ((a.2 i).1, max (a.2 i).1 (min (a.2 i).2 x))⟩,
   ⟨a.1, fun i => (max (a.2 i).1 (min (a.2 i).2 x), (a.2 i).2)⟩)

def mergeMaterial (a b : Material) : Material :=
  ⟨a.1 + b.1 + 1, fun i =>
    if h : i.val < a.1 + 1 then a.2 ⟨i.val, h⟩
    else b.2 ⟨i.val - (a.1 + 1), by omega⟩⟩

def liveOfList (l : List (ℕ × Material)) : LiveState :=
  ⟨l.length, fun i => l.get i⟩

def coalSuccessor (s : State) (i j : Fin s.2.2.1) : State :=
  if i.val < j.val then
    let survivors := (List.finRange s.2.2.1).filter (fun k => k ≠ i ∧ k ≠ j)
    let lineages := survivors.map s.2.2.2 ++
      [(s.2.1, mergeMaterial (s.2.2.2 i).2 (s.2.2.2 j).2)]
    (s.1, s.2.1 + 1, liveOfList lineages)
  else s

def initialState (n : ℕ) : State :=
  (0, n, ⟨n, fun i => (i.val, ⟨0, fun _ => (0, 1)⟩)⟩)

noncomputable def splitSuccessor (s : State) (i : Fin s.2.2.1) (x : ℝ) : State :=
  let survivors := (List.finRange s.2.2.1).filter (fun k => k ≠ i)
  let daughters := splitMaterial (s.2.2.2 i).2 x
  let lineages := survivors.map s.2.2.2 ++
    [(s.2.1, daughters.1), (s.2.1 + 1, daughters.2)]
  (s.1, s.2.1 + 2, liveOfList lineages)

end Rhone.Coalescent.IntervalProcess

clear_aux_proof_cache
set_main_module Rhone.Coalescent.FiniteIntervalMaterialMarked

namespace Rhone.Coalescent.IntervalProcess

open scoped BigOperators
open MeasureTheory
open scoped ENNReal NNReal

noncomputable def unitUniform : Measure ℝ := volume.restrict (Set.Ioo 0 1)

instance unitUniform_probability : IsProbabilityMeasure unitUniform where
  measure_univ := by simp [unitUniform, Real.volume_Ioo]

abbrev ActionIndex (s : State) :=
  (Fin s.2.2.1 × Fin s.2.2.1) ⊕ Fin s.2.2.1

noncomputable def candidateRate (mode : Mode) (R : ℝ) (s : State) : ActionIndex s → ℝ≥0 := by
  classical
  exact fun
  | .inl ij => if ij.1.val < ij.2.val ∧
      (mode = false ∨ touches (s.2.2.2 ij.1).2 (s.2.2.2 ij.2).2) then 1 else 0
  | .inr i => R.toNNReal / 2 * ⟨hullLength (s.2.2.2 i).2, le_max_left _ _⟩

noncomputable def totalRate (mode : Mode) (R : ℝ) (s : State) : ℝ≥0 :=
  ∑ a : ActionIndex s, candidateRate mode R s a

end Rhone.Coalescent.IntervalProcess

clear_aux_proof_cache
set_main_module Rhone.Coalescent.FiniteIntervalMaterialSampler

namespace Rhone.Coalescent.IntervalProcess

noncomputable def chooseByRate {α : Type*} (rate : α → ℝ) : List α → ℝ → Option α
  | [], _ => none
  | a :: rest, u => if u < rate a then some a else chooseByRate rate rest (u-rate a)

noncomputable def selectedAction (mode : Mode) (R : ℝ) (s : State) (u : Noise) :
    Option (ActionIndex s) := by
  classical
  exact chooseByRate (fun a => (candidateRate mode R s a : ℝ))
    Finset.univ.toList (u 0 * (totalRate mode R s : ℝ))

def atTime (t : ℝ) (s : State) : State := (t, s.2)

noncomputable def sampleStep (mode : Mode) (R : ℝ) (s : State) (u : Noise) :
    State × EventRecord := by
  classical
  exact if s.2.2.1 ≤ 1 ∨ totalRate mode R s = 0 then (s, (s.1, .inl ())) else
    let t := s.1 - Real.log (u 1) / (totalRate mode R s : ℝ)
    match selectedAction mode R s u with
    | none => (s, (s.1, .inl ()))
    | some (.inl ij) =>
        (atTime t (coalSuccessor s ij.1 ij.2),
          (t, .inr (.inl (ij.1.val, ij.2.val))))
    | some (.inr i) =>
        let x := hullLo (s.2.2.2 i).2 + hullLength (s.2.2.2 i).2 * u 2
        (atTime t (splitSuccessor s i x), (t, .inr (.inr (i.val, x))))

end Rhone.Coalescent.IntervalProcess

clear_aux_proof_cache
set_main_module Rhone.Coalescent.FiniteIntervalMaterialKernel

namespace Rhone.Coalescent.IntervalProcess

open MeasureTheory ProbabilityTheory

abbrev AugmentedState := State × EventRecord

noncomputable def noiseLaw : Measure Noise := Measure.pi (fun _ : Fin 3 => unitUniform)

noncomputable def augmentedStep (mode : Mode) (R : ℝ) :
    AugmentedState × Noise → AugmentedState :=
  fun p => sampleStep mode R p.1.1 p.2

noncomputable def eventKernel (mode : Mode) (R : ℝ) : Kernel AugmentedState AugmentedState :=
  (Kernel.id.prod (Kernel.const AugmentedState noiseLaw)).map (augmentedStep mode R)

end Rhone.Coalescent.IntervalProcess

clear_aux_proof_cache
set_main_module Rhone.Coalescent.FiniteIntervalGenealogy

namespace Rhone.Coalescent.IntervalProcess

open MeasureTheory
open scoped ENNReal NNReal

abbrev GenomicProbe := {q : ℚ // 0 ≤ q ∧ q < 1}

abbrev Genealogy (N : ℕ) := GenomicProbe → Fin N → Fin N → ℝ≥0∞

abbrev EventPath := ℕ → AugmentedState

def liveLabelAt (s : State) (i : ℕ) : ℕ :=
  if h : i < s.2.2.1 then (s.2.2.2 ⟨i, h⟩).1 else 0

noncomputable def ancestorStep (s : State) (e : Event)
    (q : GenomicProbe) (a : ℕ) : ℕ :=
  match e with
  | .inl _ => a
  | .inr (.inl ij) =>
      if ij.1 < ij.2 ∧ ij.2 < s.2.2.1 then
        if a = liveLabelAt s ij.1 ∨ a = liveLabelAt s ij.2 then s.2.1 else a
      else a
  | .inr (.inr ix) =>
      if ix.1 < s.2.2.1 ∧ a = liveLabelAt s ix.1 then
        if (q.val : ℝ) < ix.2 then s.2.1 else s.2.1 + 1
      else a

noncomputable def ancestorLabel (N : ℕ) (ω : EventPath)
    (q : GenomicProbe) (i : Fin N) : ℕ → ℕ
  | 0 => i.val
  | k + 1 => ancestorStep (ω k).1 (ω (k + 1)).2.2 q
      (ancestorLabel N ω q i k)

noncomputable def genealogyObservation (N : ℕ) (ω : EventPath) : Genealogy N :=
  fun q i j => ⨅ k : ℕ,
    if ancestorLabel N ω q i k = ancestorLabel N ω q j k
    then ENNReal.ofReal (ω k).1.1 else ⊤

end Rhone.Coalescent.IntervalProcess

clear_aux_proof_cache
set_main_module Rhone.Coalescent.SmcPrimeTreeProposal

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

end Rhone.Coalescent.SmcPrime

clear_aux_proof_cache
set_main_module Rhone.Coalescent.SmcPrimeProposalKernel

namespace Rhone.Coalescent.SmcPrime

open IntervalProcess MeasureTheory ProbabilityTheory

noncomputable def proposalNoiseLaw : Measure ProposalNoise :=
  Measure.pi (fun _ : Fin 5 => unitUniform)

end Rhone.Coalescent.SmcPrime

clear_aux_proof_cache
set_main_module Rhone.Coalescent.SmcPrimeSpatialProcess

namespace Rhone.Coalescent.SmcPrime

open MeasureTheory ProbabilityTheory IntervalProcess

abbrev SpatialState (N : ℕ) := ℝ × Tree N

noncomputable def spatialStep (N : ℕ) (R : ℝ)
    (z : SpatialState N) (u : ProposalNoise) : SpatialState N :=
  if 1 ≤ z.1 ∨ R ≤ 0 ∨ treeLength z.2 ≤ 0 then (1, z.2)
  else let p := proposal R z.2 u
       if z.1 + p.1 < 1 then (z.1 + p.1, p.2.2) else (1, z.2)

noncomputable def spatialKernel (N : ℕ) (R : ℝ) :
    Kernel (SpatialState N) (SpatialState N) :=
  (Kernel.id.prod (Kernel.const (SpatialState N) proposalNoiseLaw)).map
    (fun p => spatialStep N R p.1 p.2)

end Rhone.Coalescent.SmcPrime

clear_aux_proof_cache
set_main_module Rhone.Coalescent.SmcPrimeKingmanHistory

namespace Rhone.Coalescent.SmcPrime

open IntervalProcess MeasureTheory

attribute [-instance] StarOrderedRing.toIsOrderedRing

abbrev KingmanHistory (N : ℕ) := Fin N → AugmentedState

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

end Rhone.Coalescent.SmcPrime

clear_aux_proof_cache
set_main_module Rhone.Coalescent.SmcPrimeGenealogyLaw

namespace Rhone.Coalescent.SmcPrime

open MeasureTheory IntervalProcess
open scoped ENNReal

noncomputable def treePairMRCA {N : ℕ} (T : Tree N) (i j : Fin N) : ℝ≥0∞ :=
  if i = j then 0 else
  ENNReal.ofReal (rootHeight T) ⊓ ⨅ b : Fin T.1,
    if i ∈ (T.2 b).1 ∧ j ∈ (T.2 b).1 ∧ 0 < branchLength (T.2 b)
    then ENNReal.ofReal (T.2 b).2.1 else ⊤

noncomputable def spatialGenealogyObservation (N : ℕ)
    (ω : ℕ → SpatialState N) : Genealogy N :=
  fun q i j => ⨅ k : ℕ,
    if (ω k).1 ≤ (q.val : ℝ) ∧ (q.val : ℝ) < (ω (k + 1)).1
    then treePairMRCA (ω k).2 i j else ⊤

end Rhone.Coalescent.SmcPrime

clear_aux_proof_cache
set_main_module Rhone.Coalescent.SmcSupport.CountBudget

namespace Rhone.Coalescent.SmcSupport

noncomputable def countSlope (C : ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 3
  | k + 1, n => (C * countSlope C k (n + 1) + C + (n : ℝ)) / (n : ℝ)

noncomputable def countBudget (C : ℝ) (M n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, countSlope C (M - (j + 1)) (j + 1)

end Rhone.Coalescent.SmcSupport

clear_aux_proof_cache
set_main_module Rhone.Coalescent.FullARGTerminationDrift

namespace Rhone.Coalescent.IntervalProcess
open MeasureTheory ProbabilityTheory SmcSupport
open scoped ENNReal

noncomputable def absorptionBudget (R : ℝ) (m : ℕ) : ℝ :=
  countBudget R ⌈2 * R⌉₊ (m - 1)

end Rhone.Coalescent.IntervalProcess

clear_aux_proof_cache
set_main_module Palomar.SmcPrimeBound.Solution

namespace Rhone.Palomar.SmcPrimeBound

open MeasureTheory ProbabilityTheory MarkovChain Coalescent.IntervalProcess
open Coalescent.SmcPrime

noncomputable def processOfKernel {S : Type*} [MeasurableSpace S] (κ : Kernel S S) :
    DiscreteProcess S := by
  classical
  exact if h : IsMarkovKernel κ then { step := κ, isMarkov := h } else { step := Kernel.id }

noncomputable def fullARGLaw (N : ℕ) (R : ℝ) : Measure (Genealogy N) :=
  ((processOfKernel (eventKernel false R)).pathLaw (initialState N, (0, .inl ()))).map
    (genealogyObservation N)

noncomputable def initialTreeLaw (N : ℕ) : Measure (Tree N) :=
  (((processOfKernel (eventKernel false 0)).pathLaw (initialState N, (0, .inl ()))).map
    (fun ω => fun k : Fin N => ω k.val) : Measure (KingmanHistory N)).map
      (metricTreeFromHistory N)

noncomputable def smcPrimeLaw (N : ℕ) (R : ℝ) : Measure (Genealogy N) :=
  ((processOfKernel (spatialKernel N R)).law ((initialTreeLaw N).map (fun T => (0, T)))).map
    (spatialGenealogyObservation N)

clear_aux_proof_cache
set_main_module Palomar.SmcPrimeBound.Challenge

open Coalescent.SmcBound MarkovChain Probability

theorem eventKernel_isMarkovKernel (mode : Mode) (R : ℝ) :
    IsMarkovKernel (eventKernel mode R) := by
  sorry

theorem spatialKernel_isMarkovKernel (N : ℕ) (R : ℝ) :
    IsMarkovKernel (spatialKernel N R) := by
  sorry

theorem fullARG_smcPrime_tv_bound (N : ℕ) (hN : 1 ≤ N)
    (R : ℝ) (hR : 0 ≤ R) :
    eventTV (fullARGLaw N R) (smcPrimeLaw N R) ≤
      ENNReal.ofReal (doubleBound R (N - 1)) ∧
    doubleBound R (N - 1) ≤ min 1 (R ^ 2 * quadraticCoefficient (N - 1)) := by
  sorry

theorem fullARG_smcPrime_tv_quadratic (N : ℕ) (hN : 1 ≤ N)
    (R : ℝ) (hR : 0 ≤ R) :
    eventTV (fullARGLaw N R) (smcPrimeLaw N R) ≤
      ENNReal.ofReal (min 1 (R ^ 2 * quadraticCoefficient (N - 1))) := by
  sorry

theorem fullARG_smcPrime_tv_one_sample (R : ℝ) (hR : 0 ≤ R) :
    eventTV (fullARGLaw 1 R) (smcPrimeLaw 1 R) = 0 := by
  sorry

theorem fullARG_smcPrime_tv_zero_recombination (N : ℕ) (hN : 1 ≤ N) :
    eventTV (fullARGLaw N 0) (smcPrimeLaw N 0) = 0 := by
  sorry

theorem fullARGGenealogyLaw_probability (N : ℕ) (R : ℝ) :
    IsProbabilityMeasure (fullARGLaw N R) := by
  sorry

theorem smcPrimeGenealogyLaw_probability (N : ℕ) (R : ℝ) :
    IsProbabilityMeasure (smcPrimeLaw N R) := by
  sorry

theorem eventProcess_liveCount_reaches_one (N : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∀ᵐ ω ∂(processOfKernel (eventKernel false R)).pathLaw (initialState N, (0, .inl ())),
      ∃ K, ∀ k, K ≤ k → (ω k).1.2.2.1 ≤ 1 := by
  sorry

theorem eventProcess_active_events_le (N : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∑' k, (processOfKernel (eventKernel false R)).pathLaw (initialState N, (0, .inl ()))
      {ω | 2 ≤ (ω k).1.2.2.1} ≤ ENNReal.ofReal (absorptionBudget R N) := by
  sorry

theorem fullARGGenealogyLaw_ae_finite (N : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∀ᵐ G ∂fullARGLaw N R, ∀ q i j, G q i j < ⊤ := by
  sorry

section

attribute [-instance] CompletePartialOrder.toSupSet

theorem eventProcess_total_time_le (N : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∫⁻ ω, ⨆ k, ENNReal.ofReal (ω k).1.1
      ∂(processOfKernel (eventKernel false R)).pathLaw (initialState N, (0, .inl ())) ≤
      ENNReal.ofReal (absorptionBudget R N) := by
  sorry

theorem fullARGGenealogyLaw_lintegral_iSup_le (N : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∫⁻ G, ⨆ q, ⨆ i, ⨆ j, G q i j ∂fullARGLaw N R ≤
      ENNReal.ofReal (absorptionBudget R N) := by
  sorry

end

end Rhone.Palomar.SmcPrimeBound
