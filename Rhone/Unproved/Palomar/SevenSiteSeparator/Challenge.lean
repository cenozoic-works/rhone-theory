module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Calculus.TangentCone.Real
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Stochastic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
public import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.Tactic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Instances.Real.Lemmas

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

set_main_module Rhone.MarkovChain.Identifiability.Generator
clear_aux_proof_cache
section
open scoped Matrix
namespace Rhone.MarkovChain.Identifiability
noncomputable def totalMigration (k : Nat) (q : ℝ) : ℝ := (k + 1) * q
noncomputable def pairGenerator (k : Nat) (c q : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![-c - 2 * totalMigration k q, 2 * totalMigration k q], ![2*q, -2*q]]
end Rhone.MarkovChain.Identifiability
end

set_main_module Rhone.Statistics.Identifiability.MatrixFlow
clear_aux_proof_cache
section
open scoped Matrix Matrix.Norms.Operator
namespace Rhone.Statistics.Identifiability
noncomputable def flowOutput {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ)
    (i : Fin d) (v : Fin d → ℝ) (k : Nat) (t : ℝ) : ℝ :=
  ((Q ^ k * NormedSpace.exp (t • Q)) *ᵥ v) i
end Rhone.Statistics.Identifiability
end

set_main_module Rhone.Statistics.Identifiability.JointDensity
clear_aux_proof_cache
section
open scoped Matrix Matrix.Norms.Operator Topology
open MeasureTheory Filter Set
namespace Rhone.Statistics.Identifiability
def upperWedge : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ p.1 < p.2}
end Rhone.Statistics.Identifiability
end

set_main_module Rhone.Statistics.Identifiability.FirstExit
clear_aux_proof_cache
section
open scoped Matrix Matrix.Norms.Operator
open MeasureTheory Set
namespace Rhone.Statistics.Identifiability
noncomputable def exitRate {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ) : Fin d → ℝ :=
  -(Q *ᵥ (fun _ => 1))
end Rhone.Statistics.Identifiability
end

set_main_module Rhone.Statistics.Identifiability.ShearDensity
clear_aux_proof_cache
section
open scoped ENNReal
open Set MeasureTheory
namespace Rhone.Statistics.Identifiability
noncomputable abbrev planeVolume : Measure (ℝ × ℝ) :=
  (volume : Measure ℝ).prod (volume : Measure ℝ)
end Rhone.Statistics.Identifiability
end

set_main_module Rhone.Statistics.Identifiability.RegularJointLaw
clear_aux_proof_cache
section
open Set MeasureTheory
namespace Rhone.Statistics.Identifiability
set_option backward.isDefEq.respectTransparency false
noncomputable def triangularDensityLaw (j : ℝ × ℝ → ℝ) : Measure (ℝ × ℝ) :=
  (planeVolume.restrict upperWedge).withDensity (fun p => ENNReal.ofReal (j p))
end Rhone.Statistics.Identifiability
end

set_main_module Rhone.Statistics.Identifiability.ConditionalClockLaw
clear_aux_proof_cache
section
open scoped Topology
open Filter Set MeasureTheory
namespace Rhone.Statistics.Identifiability
set_option backward.isDefEq.respectTransparency false
noncomputable def conditionalPairDensity (rate H : ℝ → ℝ) (s t : ℝ) : ℝ :=
  rate t * Real.exp (H s-H t)
end Rhone.Statistics.Identifiability
end

set_main_module Rhone.Statistics.Identifiability.IntegratedClock
clear_aux_proof_cache
section
open Set Filter MeasureTheory
namespace Rhone.Statistics.Identifiability
noncomputable def integratedClock (rate : ℝ → ℝ) (t : ℝ) : ℝ := ∫ x in 0..t, rate x
end Rhone.Statistics.Identifiability
end

set_main_module Rhone.Statistics.Identifiability.EqualRatesMutationSemigroup
clear_aux_proof_cache
section
open Set MeasureTheory Matrix
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Rhone.Statistics.Identifiability.EqualRatesMutation
abbrev State (K : ℕ) := Fin K
abbrev MutationMatrix (K : ℕ) := Matrix (State K) (State K) ℝ

def uniform (K : ℕ) : MutationMatrix K := fun _ _ => 1 / (K : ℝ)

def transition (K : ℕ) (k t : ℝ) : MutationMatrix K :=
  Real.exp (-(k/2)*t) • 1 + (1-Real.exp (-(k/2)*t)) • uniform K

lemma uniform_weights_sum {K : ℕ} (hK : 0 < K) :
    ∑ _root : State K, (1 / (K : ℝ)) = 1 := by
  have hn : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hK)
  simp [hn]
end Rhone.Statistics.Identifiability.EqualRatesMutation
end
end

set_main_module Rhone.Statistics.ThreeTipSites.Channel
clear_aux_proof_cache
section
open MeasureTheory
open scoped BigOperators ENNReal
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Rhone.Statistics.ThreeTipSites
open Identifiability.EqualRatesMutation
abbrev Triple (K : ℕ) := Fin K × (Fin K × Fin K)
abbrev Panel (K L : ℕ) := Fin L → Triple K

structure Roots (K L : ℕ) where
  weight : Fin L → Fin K → ℝ
  nonneg : ∀ s r, 0 ≤ weight s r
  normalized : ∀ s, ∑ r, weight s r = 1

def cycle (K : ℕ) : Triple K ≃ Triple K where
  toFun x := (x.2.1, x.2.2, x.1)
  invFun x := (x.2.2, x.1, x.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

def orientation (K : ℕ) (q : Fin 3) : Triple K ≃ Triple K :=
  if q = 0 then Equiv.refl _ else if q = 1 then cycle K else (cycle K).symm

def site (K : ℕ) (π : Fin K → ℝ) (k : ℝ) (t : ℝ × ℝ) (x : Triple K) : ℝ :=
  ∑ r, ∑ z, π r * transition K k t.2 r z * transition K k t.1 z x.1 *
    transition K k t.1 z x.2.1 * transition K k (t.1 + t.2) r x.2.2

def fixedTopology {K L : ℕ} (π : Roots K L) (k : ℝ) (t : ℝ × ℝ)
    (q : Fin 3) (x : Panel K L) : ℝ :=
  ∏ s, site K (π.weight s) k t (orientation K q (x s))

def conditional {K L : ℕ} (π : Roots K L) (k : ℝ) (t : ℝ × ℝ)
    (x : Panel K L) : ℝ := (1 / 3 : ℝ) * ∑ q : Fin 3, fixedTopology π k t q x

def mass {K L : ℕ} (π : Roots K L) (k : ℝ) (μ : Measure (ℝ × ℝ))
    (x : Panel K L) : ℝ := ∫ t, conditional π k t x ∂μ

def law {K L : ℕ} (π : Roots K L) (k : ℝ) (μ : Measure (ℝ × ℝ)) :
    Measure (Panel K L) :=
  Measure.sum fun x => ENNReal.ofReal (mass π k μ x) • Measure.dirac x
end Rhone.Statistics.ThreeTipSites
end
end

set_main_module Rhone.Statistics.ThreeSiteSeparator.BlockExpectations
clear_aux_proof_cache
section
noncomputable section
open scoped BigOperators
namespace Rhone.Statistics.ThreeSiteSeparator
open ThreeTipSites
def uniformBlockRoots (K L : ℕ) (hK : 0 < K) : Roots K L where
  weight := fun _ _ => 1/(K : ℝ)
  nonneg := fun _ _ => by positivity
  normalized := fun _ => Identifiability.EqualRatesMutation.uniform_weights_sum hK
end Rhone.Statistics.ThreeSiteSeparator
end
end

set_main_module Rhone.Statistics.Identifiability.ThreeGenerator
clear_aux_proof_cache
section
open scoped Matrix Matrix.Norms.Operator
namespace Rhone.Statistics.Identifiability
abbrev ThreeState := Fin 3
noncomputable def threeGenerator (k : Nat) (c q : ℝ) : Matrix ThreeState ThreeState ℝ :=
  ![![-3*c-3*MarkovChain.Identifiability.totalMigration k
      q,3*MarkovChain.Identifiability.totalMigration k q,0],
    ![q,-c-(2*k+1)*q,2*k*q], ![0,6*q,-6*q]]
end Rhone.Statistics.Identifiability
end

set_main_module Rhone.Statistics.Identifiability.IslandThreeJointTimes
clear_aux_proof_cache
section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Matrix Matrix.Norms.Operator Topology ENNReal
open MeasureTheory Set Filter
namespace Rhone.Statistics.Identifiability
namespace IslandThreeTimes

def firstRate (c : ℝ) : Matrix (Fin 3) (Fin 2) ℝ := !![3*c, 0; 0, c; 0, 0]
def entryFlux (k : ℕ) (c q : ℝ) (j : Fin 2) (s : ℝ) : ℝ :=
  flowOutput (threeGenerator k c q) 0 (fun i => firstRate c i j) 0 s
def postDensity (k : ℕ) (c q : ℝ) (j : Fin 2) (u : ℝ) : ℝ :=
  flowOutput (MarkovChain.Identifiability.pairGenerator k c q) j
      (exitRate (MarkovChain.Identifiability.pairGenerator k c q)) 0 u

def density (k : ℕ) (c q : ℝ) (p : ℝ × ℝ) : ℝ :=
  ∑ j : Fin 2, entryFlux k c q j p.1 * postDensity k c q j (p.2-p.1)
def law (k : ℕ) (c q : ℝ) : Measure (ℝ × ℝ) := triangularDensityLaw (density k c q)
end IslandThreeTimes
end Rhone.Statistics.Identifiability
end
end

set_main_module Rhone.Statistics.Identifiability.PanThreeSampleLaw
clear_aux_proof_cache
section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Rhone.Statistics.Identifiability
namespace PanThreeSample
set_option backward.isDefEq.respectTransparency false
def firstDensity (rate : ℝ → ℝ) (s : ℝ) : ℝ :=
  3 * rate s * Real.exp (-3 * integratedClock rate s)
def jointDensity (rate : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  firstDensity rate p.1 * conditionalPairDensity rate (integratedClock rate) p.1 p.2
def law (rate : ℝ → ℝ) : Measure (ℝ × ℝ) :=
  triangularDensityLaw (jointDensity rate)

def toDurations (p : ℝ × ℝ) : ℝ × ℝ := (p.1, p.2 - p.1)
def durationLaw (rate : ℝ → ℝ) : Measure (ℝ × ℝ) := (law rate).map toDurations
end PanThreeSample
end Rhone.Statistics.Identifiability
end
end

set_main_module Rhone.Statistics.Identifiability.IslandThreeFirstMarginal
clear_aux_proof_cache
section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Matrix Matrix.Norms.Operator Topology ENNReal
open MeasureTheory Set Filter
namespace Rhone.Statistics.Identifiability
namespace IslandThreeTimes

def toDurations (p : ℝ × ℝ) : ℝ × ℝ := (p.1,p.2-p.1)
def durationLaw (k : ℕ) (c q : ℝ) : Measure (ℝ × ℝ) := (law k c q).map toDurations
end IslandThreeTimes
end Rhone.Statistics.Identifiability
end
end

set_main_module Rhone.Unproved.Palomar.SevenSiteSeparator.Challenge
clear_aux_proof_cache

noncomputable section
open Set Filter MeasureTheory
namespace Rhone.Palomar.SevenSiteSeparator
open MarkovChain Statistics
open ThreeSiteSeparator MarkovChain.Identifiability Statistics.Identifiability ThreeTipSites

theorem seven_site_separation {K : ℕ} (hK : 2 ≤ K)
    (r : ℝ → ℝ) (hr : LocallyIntegrable r volume) (hn : ∀ t, 0 ≤ r t)
    (ht : Tendsto (integratedClock r) atTop atTop) {k : ℝ} (hk : 0 < k) :
    law (uniformBlockRoots K 7 (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) hK)) 1
        (IslandThreeTimes.durationLaw 0 1 (1 / 100)) ≠
      law (uniformBlockRoots K 7 (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) hK)) k
        (PanThreeSample.durationLaw r) := by
  sorry

end Rhone.Palomar.SevenSiteSeparator
end
