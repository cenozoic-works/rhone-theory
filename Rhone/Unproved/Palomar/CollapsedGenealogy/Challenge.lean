module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Calculus.TangentCone.Real
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Stochastic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Tactic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.Module.FiniteDimension

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

set_main_module Rhone.Statistics.Identifiability.EqualRatesMutationSemigroup
clear_aux_proof_cache

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

set_main_module Rhone.Statistics.ThreeTipSites.Channel
clear_aux_proof_cache

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

end Rhone.Statistics.ThreeTipSites
end

set_main_module Rhone.Statistics.ThreeSiteSeparator.BlockExpectations
clear_aux_proof_cache

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

set_main_module Rhone.Statistics.CollapsedGenealogy.Boundary
clear_aux_proof_cache

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace Rhone.Statistics.CollapsedGenealogy
open ThreeTipSites ThreeSiteSeparator
open Identifiability.EqualRatesMutation

abbrev Joint := (ℝ × ℝ) × Fin 3

def jointMass {K L : ℕ} (π : Roots K L) (k : ℝ) (μ : Measure Joint)
    (x : Panel K L) : ℝ := ∫ g, fixedTopology π k g.1 g.2 x ∂μ

def jointSequenceLaw {K L : ℕ} (π : Roots K L) (k : ℝ) (μ : Measure Joint) :
    Measure (Panel K L) :=
  Measure.sum fun x => ENNReal.ofReal (jointMass π k μ x) • Measure.dirac x

end Rhone.Statistics.CollapsedGenealogy
end

set_main_module Rhone.Statistics.CollapsedGenealogy.Object
clear_aux_proof_cache

noncomputable section
open MeasureTheory
namespace Rhone.Statistics.CollapsedGenealogy
open ThreeTipSites ThreeSiteSeparator
open Identifiability.EqualRatesMutation

def collapse (g : Joint) : Joint := (g.1, if g.1.2 = 0 then 0 else g.2)

def scale (k : ℝ) (g : Joint) : Joint := ((k * g.1.1, k * g.1.2), g.2)

def object (k : ℝ) (μ : Measure Joint) : Measure Joint := Measure.map (collapse ∘ scale k) μ

end Rhone.Statistics.CollapsedGenealogy
end

set_main_module Rhone.Statistics.CollapsedGenealogy.Moments
clear_aux_proof_cache

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Rhone.Statistics.CollapsedGenealogy
open ThreeTipSites ThreeSiteSeparator

abbrev NonnegativeJoint (μ : Measure Joint) : Prop := ∀ᵐ g ∂μ, 0 ≤ g.1.1 ∧ 0 ≤ g.1.2

end Rhone.Statistics.CollapsedGenealogy
end

set_main_module Rhone.Unproved.Palomar.CollapsedGenealogy.Challenge
clear_aux_proof_cache

namespace Rhone.Palomar.CollapsedGenealogy

open MeasureTheory
open Statistics.ThreeTipSites Statistics.ThreeSiteSeparator
open Statistics.CollapsedGenealogy

theorem all_blocks_iff_collapsed_joint_eq {K : ℕ} (hK : 2 ≤ K)
    {k l : ℝ} (hk : 0 ≤ k) (hl : 0 ≤ l) (μ ν : Measure Joint)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμ : NonnegativeJoint μ) (hν : NonnegativeJoint ν) :
    (∀ L : ℕ,
      jointSequenceLaw (uniformBlockRoots K L (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) hK)) k μ =
        jointSequenceLaw (uniformBlockRoots K L (Nat.lt_of_lt_of_le (Nat.zero_lt_succ 1) hK)) l ν) ↔
      object k μ = object l ν := by
  sorry

theorem star_labels_same_sequence_law {K L : ℕ} (hK : 0 < K) (k u : ℝ)
    (q p : Fin 3) :
    jointSequenceLaw (uniformBlockRoots K L hK) k (Measure.dirac ((u, 0), q)) =
      jointSequenceLaw (uniformBlockRoots K L hK) k (Measure.dirac ((u, 0), p)) := by
  sorry

end Rhone.Palomar.CollapsedGenealogy
