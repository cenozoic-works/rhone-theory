module

public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Data.Fintype.Option

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

open scoped BigOperators

set_main_module Rhone.Coalescent.IslandPairRates
clear_aux_proof_cache

namespace Rhone.Coalescent.IslandPair

noncomputable def destinationRate (d : Nat) (m : Real) : Real := m / (d - 1 : Nat)

set_main_module Rhone.Coalescent.IslandPairLumping
clear_aux_proof_cache

abbrev Category := Option Bool

noncomputable def projectedGenerator (d : Nat) (m c : Real) : Category → Category → Real
  | none, _ => 0
  | some true, none => c
  | some true, some true => -(c + 2 * m)
  | some true, some false => 2 * m
  | some false, none => 0
  | some false, some true => 2 * destinationRate d m
  | some false, some false => -(2 * destinationRate d m)

end Rhone.Coalescent.IslandPair

set_main_module Rhone.Statistics.Identifiability.MatrixFlow
clear_aux_proof_cache

namespace Rhone
open scoped Matrix Matrix.Norms.Operator ENNReal
open Set MeasureTheory

noncomputable def Statistics.Identifiability.flowOutput {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ)
    (i : Fin d) (v : Fin d → ℝ) (k : Nat) (t : ℝ) : ℝ :=
  ((Q ^ k * NormedSpace.exp (t • Q)) *ᵥ v) i

set_main_module Rhone.Statistics.Identifiability.FirstExit
clear_aux_proof_cache

noncomputable def Statistics.Identifiability.exitRate {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ) : Fin
    d → ℝ :=
  -(Q *ᵥ (fun _ => 1))

set_main_module Rhone.Statistics.Identifiability.FirstExitLaw
clear_aux_proof_cache

noncomputable def Statistics.Identifiability.firstExitLaw {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ)
    (i : Fin d) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity
      (fun t => ENNReal.ofReal
      (Statistics.Identifiability.flowOutput Q i (Statistics.Identifiability.exitRate Q) 0 t))

set_main_module Rhone.MarkovChain.Identifiability.Generator
clear_aux_proof_cache

noncomputable def MarkovChain.Identifiability.totalMigration (k : Nat) (q : ℝ) : ℝ := (k + 1) * q

noncomputable def MarkovChain.Identifiability.pairGenerator (k : Nat) (c q : ℝ) : Matrix (Fin 2)
    (Fin 2) ℝ :=
  ![![-c - 2 * MarkovChain.Identifiability.totalMigration k q, 2 *
      MarkovChain.Identifiability.totalMigration k q], ![2*q, -2*q]]

set_main_module Rhone.Statistics.Identifiability.PairLaplaceTransform
clear_aux_proof_cache

noncomputable def Statistics.Identifiability.pairLaplaceDenominator (k : Nat) (c q s : ℝ) : ℝ :=
  s ^ 2 + s * (c + 2 * ((k : ℝ) + 2) * q) + 2 * c * q

end Rhone

set_main_module Rhone.Statistics.PairObservationChannel.Channel
clear_aux_proof_cache

namespace Rhone.Statistics.PairObservationChannel

structure Channel (K : ℕ) (H : Type*) [Fintype H] where
  positive : 0 < K
  row : Fin K → H → ℝ
  nonneg : ∀ i y, 0 ≤ row i y
  normalized : ∀ i, ∑ y, row i y = 1

variable {K : ℕ} {H : Type*} [Fintype H]

noncomputable def columnMean (E : Channel K H) (y : H) : ℝ :=
  (∑ i, E.row i y) / K

def Informative (E : Channel K H) : Prop := ∃ i j y, E.row i y ≠ E.row j y

end Rhone.Statistics.PairObservationChannel

set_main_module Rhone.Statistics.PairObservationChannel.Agreement
clear_aux_proof_cache

namespace Rhone.Statistics.PairObservationChannel
variable {K : ℕ} {H : Type*} [Fintype H]

noncomputable def sharedMass (E : Channel K H) (x y : H) : ℝ :=
  (∑ i, E.row i x * E.row i y) / K

noncomputable def reportedMass (E : Channel K H) (ℓ : ℝ) (x y : H) : ℝ :=
  (1-ℓ)*columnMean E x*columnMean E y + ℓ*sharedMass E x y

end Rhone.Statistics.PairObservationChannel

set_main_module Rhone.Statistics.PairObservationChannel.LaplaceKernel
clear_aux_proof_cache

namespace Rhone.Statistics.PairObservationChannel
open MeasureTheory

attribute [-instance] RCLike.toInnerProductSpaceReal RCLike.innerProductSpace in
noncomputable def pairLaplace (μ : Measure ℝ) (k : ℝ) : ℝ :=
  ∫ t, Real.exp (-k*t) ∂μ

end Rhone.Statistics.PairObservationChannel

set_main_module Rhone.Statistics.SpatialPairDesign.Laplace
clear_aux_proof_cache

namespace Rhone.Statistics.SpatialPairDesign
open MeasureTheory
open MarkovChain.Identifiability Identifiability

noncomputable def pairLaw (n : ℕ) (c q : ℝ) (i : Fin 2) : Measure ℝ :=
  firstExitLaw (pairGenerator n c q) i

end Rhone.Statistics.SpatialPairDesign

set_main_module Rhone.Statistics.AsymmetricPairDesign.Generator
clear_aux_proof_cache

namespace Rhone.Statistics.AsymmetricPairDesign
open MeasureTheory
open MarkovChain.Identifiability Identifiability

noncomputable def generator (a b c d : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-c - 2 * a, 2 * a, 0; b, -a - b, a; 0, 2 * b, -d - 2 * b]

noncomputable def pairLaw (a b c d : ℝ) (i : Fin 3) : Measure ℝ :=
  firstExitLaw (generator a b c d) i

set_main_module Rhone.Statistics.AsymmetricPairDesign.Laplace
clear_aux_proof_cache

noncomputable def laplace (a b c d k : ℝ) (i : Fin 3) : ℝ :=
  ∫ t, Real.exp (-k * t) ∂pairLaw a b c d i

end Rhone.Statistics.AsymmetricPairDesign

set_main_module Rhone.Statistics.IslandPairSpatialDesign
clear_aux_proof_cache

namespace Rhone.Statistics.IslandPairSpatialDesign

open Coalescent.IslandPair

def transientCategory : Fin 2 → Category := ![some true, some false]

end Rhone.Statistics.IslandPairSpatialDesign

set_main_module Rhone.Unproved.Palomar.KnownStrataPairDesign.Challenge
clear_aux_proof_cache

namespace Rhone.Palomar.KnownStrataPairDesign

open MeasureTheory
open Coalescent.IslandPair Statistics.IslandPairSpatialDesign
open MarkovChain.Identifiability Statistics.Identifiability Statistics.PairObservationChannel

theorem pair_generator_eq_projected (n : ℕ) (c q : ℝ) (i j : Fin 2) :
    pairGenerator n c q i j =
      projectedGenerator (n + 2) ((n + 1) * q) c (transientCategory i)
        (transientCategory j) := by
  sorry

theorem exit_rate_eq_projected (n : ℕ) (c q : ℝ) (i : Fin 2) :
    exitRate (pairGenerator n c q) i =
      projectedGenerator (n + 2) ((n + 1) * q) c (transientCategory i) none := by
  sorry

theorem spatial_laplace_gap (n : ℕ) {c q k : ℝ} (hc : 0 < c) (hq : 0 < q) (hk : 0 ≤ k) :
    pairLaplace (Rhone.Statistics.SpatialPairDesign.pairLaw n c q 0) k -
        pairLaplace (Rhone.Statistics.SpatialPairDesign.pairLaw n c q 1) k =
      c * k / pairLaplaceDenominator n c q k := by
  sorry

theorem spatial_separated_iff {K : ℕ} {H : Type*} [Fintype H] (E : Channel K H) (n : ℕ)
    {c q k : ℝ} (hc : 0 < c) (hq : 0 < q) (hk : 0 < k) :
    (∃ x y, reportedMass E
        (pairLaplace (Rhone.Statistics.SpatialPairDesign.pairLaw n c q 0) k) x y ≠
      reportedMass E
        (pairLaplace (Rhone.Statistics.SpatialPairDesign.pairLaw n c q 1) k) x y) ↔
      Informative E := by
  sorry

theorem asymmetric_balance {a b c d k : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (hk : 0 ≤ k) :
    (k + a + b) * Rhone.Statistics.AsymmetricPairDesign.laplace a b c d k 1 =
      b * Rhone.Statistics.AsymmetricPairDesign.laplace a b c d k 0 +
        a * Rhone.Statistics.AsymmetricPairDesign.laplace a b c d k 2 := by
  sorry

theorem asymmetric_laplace_separation {a b c d k : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (hk : 0 < k) :
    Rhone.Statistics.AsymmetricPairDesign.laplace a b c d k 1 <
        Rhone.Statistics.AsymmetricPairDesign.laplace a b c d k 0 ∨
      Rhone.Statistics.AsymmetricPairDesign.laplace a b c d k 1 <
        Rhone.Statistics.AsymmetricPairDesign.laplace a b c d k 2 := by
  sorry

theorem asymmetric_no_common_law {K : ℕ} {H : Type*} [Fintype H] (E : Channel K H)
    (hK : 2 ≤ K) (hE : Informative E)
    {a b c d k : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hk : 0 < k) :
    ¬ ∃ Q : H × H → ℝ, ∀ i : Fin 3, ∀ x y,
      reportedMass E (Rhone.Statistics.AsymmetricPairDesign.laplace a b c d k i) x y =
        Q (x, y) := by
  sorry

end Rhone.Palomar.KnownStrataPairDesign
