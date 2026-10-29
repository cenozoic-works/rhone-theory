module

public import Mathlib.LinearAlgebra.Matrix.Stochastic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Probability.Kernel.IonescuTulcea.Traj
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Probability.ProductMeasure

set_option maxSynthPendingDepth 3

@[expose] public section

elab "clear_aux_proof_cache" : command => do
  Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
  let ext ← unsafe Lean.Elab.Command.liftCoreM
    (Lean.evalConst (Lean.EnvExtension (Lean.PersistentHashMap Nat Nat))
      (Lean.Name.mkNum `_private.Lean.Meta.Match.Match 0 ++ `Lean.Meta.Match.matcherExt))
  Lean.modifyEnv fun env => ext.setState env {}

clear_aux_proof_cache

namespace Rhone.MarkovChain

open Finset Matrix

structure FinChain (S : Type*) [Fintype S] where

  P : Matrix S S ℝ

  nonneg : ∀ x y, 0 ≤ P x y

  row_sum : ∀ x, ∑ y, P x y = 1

namespace FinChain

variable {S : Type*} [Fintype S] [DecidableEq S] (C : FinChain S)

def stepN (n : ℕ) : Matrix S S ℝ := C.P ^ n

end FinChain

end Rhone.MarkovChain

clear_aux_proof_cache

namespace Rhone.MarkovChain.FinChain

open Finset Filter Topology

variable {S : Type*} [Fintype S] [DecidableEq S] (C : FinChain S)

noncomputable def potential (A : Finset S) (c : S → ℝ) (x : S) : ℝ :=
  ∑' n, ∑ y ∈ Aᶜ, C.stepN n x y * c y

end Rhone.MarkovChain.FinChain

clear_aux_proof_cache

namespace Rhone.MarkovChain

open Finset

structure RateChain (S : Type*) [Fintype S] where

  Q : Matrix S S ℝ

  off_diag_nonneg : ∀ x y, x ≠ y → 0 ≤ Q x y

  row_sum : ∀ x, ∑ y, Q x y = 0

namespace RateChain

variable {S : Type*} [Fintype S] [DecidableEq S] (R : RateChain S)

omit [DecidableEq S] in

def rate (x : S) : ℝ := -R.Q x x

theorem rate_eq_sum (x : S) : R.rate x = ∑ y ∈ univ.erase x, R.Q x y := by
  have h := R.row_sum x
  rw [← Finset.add_sum_erase univ _ (mem_univ x)] at h
  rw [rate]
  linarith

omit [DecidableEq S] in

theorem rate_nonneg (x : S) : 0 ≤ R.rate x := by
  classical
  rw [rate_eq_sum]
  exact Finset.sum_nonneg fun y hy => R.off_diag_nonneg x y (Finset.ne_of_mem_erase hy).symm

noncomputable def jumpMatrix : Matrix S S ℝ := fun x y =>
  if R.rate x = 0 then (if x = y then 1 else 0) else (if x = y then 0 else R.Q x y / R.rate x)

theorem sum_jumpMatrix_mul {x : S} (hx : R.rate x ≠ 0) (u : S → ℝ) :
    ∑ y, R.jumpMatrix x y * u y = u x + (∑ y, R.Q x y * u y) / R.rate x := by
  have hterm : ∀ y, R.jumpMatrix x y * u y =
      (if x = y then u y else 0) + R.Q x y * u y / R.rate x := by
    intro y
    by_cases hxy : x = y
    · subst hxy
      have hq : R.Q x x = -R.rate x := by simp [rate]
      simp only [jumpMatrix, hx, ↓reduceIte, zero_mul, hq]
      field_simp
      ring
    · simp only [jumpMatrix, hx, hxy, ↓reduceIte]
      ring
  simp only [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq, ← Finset.sum_div]
  simp

noncomputable def jumpChain : FinChain S where
  P := R.jumpMatrix
  nonneg x y := by
    unfold jumpMatrix
    split_ifs with h1 h2 h2
    · exact zero_le_one
    · exact le_rfl
    · exact le_rfl
    · exact div_nonneg (R.off_diag_nonneg x y h2) (R.rate_nonneg x)
  row_sum x := by
    by_cases hx : R.rate x = 0
    · simp [jumpMatrix, hx]
    · have h := R.sum_jumpMatrix_mul hx (fun _ => 1)
      simp only [mul_one, R.row_sum x, zero_div, add_zero] at h
      exact h

noncomputable def expectedCost (A : Finset S) (c : S → ℝ) (x : S) : ℝ :=
  R.jumpChain.potential A (fun y => c y / R.rate y) x

noncomputable def expectedTime (A : Finset S) (x : S) : ℝ := R.expectedCost A (fun _ => 1) x

end RateChain

end Rhone.MarkovChain

clear_aux_proof_cache

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

noncomputable def pathLaw (x : S) : Measure (ℕ → S) := P.traj x

end DiscreteProcess

end Rhone.MarkovChain

clear_aux_proof_cache

namespace Rhone.MarkovChain.FinChain

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

variable {S : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  (C : FinChain S)

omit [DecidableEq S] [MeasurableSpace S] [DiscreteMeasurableSpace S] in

theorem sum_ofReal_P (x : S) : ∑ y, ENNReal.ofReal (C.P x y) = 1 := by
  rw [← ENNReal.ofReal_sum_of_nonneg fun y _ => C.nonneg x y, C.row_sum, ENNReal.ofReal_one]

noncomputable def stepPMF (x : S) : PMF S :=
  PMF.ofFintype (fun y => ENNReal.ofReal (C.P x y)) (C.sum_ofReal_P x)

noncomputable def kernel : Kernel S S where
  toFun x := (C.stepPMF x).toMeasure
  measurable' := Measurable.of_discrete

instance : IsMarkovKernel C.kernel :=
  ⟨fun x => by change IsProbabilityMeasure (C.stepPMF x).toMeasure; infer_instance⟩

noncomputable def toProcess : DiscreteProcess S := ⟨C.kernel⟩

noncomputable def pathLaw (x : S) : Measure (ℕ → S) := C.toProcess.pathLaw x

end Rhone.MarkovChain.FinChain

clear_aux_proof_cache

namespace Rhone.MarkovChain

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

instance isProbabilityMeasure_expMeasure_one : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure one_pos

noncomputable def clockLaw : Measure (ℕ → ℝ) := Measure.infinitePi fun _ : ℕ => expMeasure 1

namespace RateChain

variable {S : Type*} [Fintype S] [DecidableEq S] (R : RateChain S)

omit [DecidableEq S] in

noncomputable def holdTime (p : (ℕ → S) × (ℕ → ℝ)) (k : ℕ) : ℝ := p.2 k / R.rate (p.1 k)

noncomputable def costBefore (A : Finset S) (c : S → ℝ) (p : (ℕ → S) × (ℕ → ℝ)) : ℝ≥0∞ :=
  ∑' k, if p.1 k ∈ A then 0 else ENNReal.ofReal (c (p.1 k) * R.holdTime p k)

noncomputable def timeBefore (A : Finset S) (p : (ℕ → S) × (ℕ → ℝ)) : ℝ≥0∞ :=
  R.costBefore A (fun _ => 1) p

variable [MeasurableSpace S] [DiscreteMeasurableSpace S]

noncomputable def jumpHoldLaw (x : S) : Measure ((ℕ → S) × (ℕ → ℝ)) :=
  (R.jumpChain.pathLaw x).prod clockLaw

end RateChain

end Rhone.MarkovChain

clear_aux_proof_cache

namespace Rhone.Coalescent.IslandPair
open Finset

abbrev State (d : Nat) := Option (Fin d × Fin d)

noncomputable def destinationRate (d : Nat) (m : Real) : Real := m / (d - 1 : Nat)

noncomputable def eventRate (d : Nat) (m c : Real) : State d → State d → Real
  | none, _ => 0
  | some (a,b), none => if a = b then c else 0
  | some (a,b), some (x,y) =>
      (if b = y ∧ a ≠ x then destinationRate d m else 0) +
      (if a = x ∧ b ≠ y then destinationRate d m else 0)

noncomputable def generator (d : Nat) (m c : Real) (s t : State d) : Real :=
  eventRate d m c s t - if s = t then ∑ y, eventRate d m c s y else 0

theorem eventRate_nonneg (d : Nat) (m c : Real) (hm : 0 ≤ m) (hc : 0 ≤ c)
    (s t : State d) : 0 ≤ eventRate d m c s t := by
  have hk : 0 ≤ destinationRate d m := div_nonneg hm (Nat.cast_nonneg _)
  cases s with
  | none => exact le_rfl
  | some p =>
    rcases p with ⟨a,b⟩
    cases t with
    | none => simp only [eventRate]; split_ifs <;> first | exact hc | exact le_rfl
    | some q =>
      rcases q with ⟨x,y⟩
      simp only [eventRate]
      exact add_nonneg (by split_ifs <;> first | exact hk | exact le_rfl)
        (by split_ifs <;> first | exact hk | exact le_rfl)

theorem generator_row_sum (d : Nat) (m c : Real) (s : State d) :
    ∑ t, generator d m c s t = 0 := by
  simp [generator, sum_sub_distrib]

noncomputable def chain (d : Nat) (m c : Real) (hm : 0 ≤ m) (hc : 0 ≤ c) :
    Rhone.MarkovChain.RateChain (State d) where
  Q := generator d m c
  off_diag_nonneg s t hst := by
    simp only [generator, hst, ↓reduceIte, sub_zero]
    exact eventRate_nonneg d m c hm hc s t
  row_sum := generator_row_sum d m c

end Rhone.Coalescent.IslandPair

clear_aux_proof_cache

namespace Rhone.Coalescent.IslandPair
open Finset

noncomputable def sameTime (d : Nat) (c : Real) : Real := d / c

noncomputable def differentTime (d : Nat) (m c : Real) : Real :=
  sameTime d c + (d - 1 : Nat) / (2 * m)

noncomputable def meanTime (d : Nat) (m c : Real) : State d → Real
  | none => 0
  | some (a,b) => if a = b then sameTime d c else differentTime d m c

end Rhone.Coalescent.IslandPair

clear_aux_proof_cache

namespace Rhone.Coalescent.IslandPair
open Finset MeasureTheory

instance stateMeasurableSpace (d : Nat) : MeasurableSpace (State d) := ⊤

instance stateDiscreteMeasurableSpace (d : Nat) : DiscreteMeasurableSpace (State d) :=
  ⟨fun _ => trivial⟩

end Rhone.Coalescent.IslandPair

clear_aux_proof_cache

namespace Rhone.Coalescent.IslandPairFst
open Finset IslandPair

noncomputable def fstFromTimes (tWithin tTotal : ℝ) : ℝ := (tTotal - tWithin) / tTotal

noncomputable def randomDemesTime (d : ℕ) (m c : ℝ) (hm : 0 ≤ m) (hc : 0 ≤ c) : ℝ :=
  (1 / (d : ℝ) ^ 2) *
    ∑ a : Fin d, ∑ b : Fin d, (chain d m c hm hc).expectedTime {none} (some (a, b))

noncomputable def fstBetween (d : ℕ) (m c : ℝ) : ℝ :=
  ((d : ℝ) - 1) * c / (2 * m * d + ((d : ℝ) - 1) * c)

noncomputable def fstRandom (d : ℕ) (m c : ℝ) : ℝ :=
  ((d : ℝ) - 1) ^ 2 * c / (2 * m * (d : ℝ) ^ 2 + ((d : ℝ) - 1) ^ 2 * c)

end Rhone.Coalescent.IslandPairFst

clear_aux_proof_cache

namespace Rhone.Palomar.IslandPairCoalescence

open Finset MeasureTheory Coalescent.IslandPair

theorem expectedTime_same (d : Nat) (hd : 2 ≤ d) (m c : Real)
    (hm : 0 < m) (hc : 0 < c) (a : Fin d) :
    (chain d m c hm.le hc.le).expectedTime {none} (some (a,a)) = d / c := by
  sorry

theorem expectedTime_different (d : Nat) (hd : 2 ≤ d) (m c : Real)
    (hm : 0 < m) (hc : 0 < c) (a b : Fin d) (hab : a ≠ b) :
    (chain d m c hm.le hc.le).expectedTime {none} (some (a,b)) =
      d / c + (d - 1 : Nat) / (2 * m) := by
  sorry

theorem lintegral_timeBefore (d : Nat) (hd : 2 ≤ d) (m c : Real)
    (hm : 0 < m) (hc : 0 < c) (s : State d) :
    ∫⁻ p, (chain d m c hm.le hc.le).timeBefore {none} p
      ∂(chain d m c hm.le hc.le).jumpHoldLaw s = ENNReal.ofReal (meanTime d m c s) := by
  sorry

end Rhone.Palomar.IslandPairCoalescence

namespace Rhone.Palomar.IslandPairCoalescence

open Finset Filter Topology Coalescent.IslandPair Coalescent.IslandPairFst

theorem fstFromTimes_between (d : ℕ) (hd : 2 ≤ d) (m c : ℝ) (hm : 0 < m) (hc : 0 < c)
    (a b b' : Fin d) (hbb : b ≠ b') :
    fstFromTimes ((chain d m c hm.le hc.le).expectedTime {none} (some (a, a)))
      ((chain d m c hm.le hc.le).expectedTime {none} (some (b, b'))) = fstBetween d m c := by
  sorry

theorem fstFromTimes_random (d : ℕ) (hd : 2 ≤ d) (m c : ℝ) (hm : 0 < m) (hc : 0 < c)
    (a : Fin d) :
    fstFromTimes ((chain d m c hm.le hc.le).expectedTime {none} (some (a, a)))
      (randomDemesTime d m c hm.le hc.le) = fstRandom d m c := by
  sorry

theorem fstBetween_diploid (d : ℕ) (hd : 2 ≤ d) (m N : ℝ) (hm : 0 < m) (hN : 0 < N) :
    fstBetween d m (1 / (2 * N)) = 1 / (1 + 4 * N * m * ((d : ℝ) / ((d : ℝ) - 1))) := by
  sorry

theorem fstRandom_diploid (d : ℕ) (hd : 2 ≤ d) (m N : ℝ) (hm : 0 < m) (hN : 0 < N) :
    fstRandom d m (1 / (2 * N)) =
      1 / (1 + 4 * N * m * ((d : ℝ) ^ 2 / ((d : ℝ) - 1) ^ 2)) := by
  sorry

theorem fstBetween_strictAntiOn (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c) :
    StrictAntiOn (fun m : ℝ => fstBetween d m c) (Set.Ioi 0) := by
  sorry

theorem fstRandom_strictAntiOn (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c) :
    StrictAntiOn (fun m : ℝ => fstRandom d m c) (Set.Ioi 0) := by
  sorry

theorem tendsto_fstBetween_zero_right (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c) :
    Tendsto (fun m : ℝ => fstBetween d m c) (𝓝[>] 0) (𝓝 1) := by
  sorry

theorem tendsto_fstRandom_zero_right (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c) :
    Tendsto (fun m : ℝ => fstRandom d m c) (𝓝[>] 0) (𝓝 1) := by
  sorry

theorem tendsto_fstBetween_atTop (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (_hc : 0 < c) :
    Tendsto (fun m : ℝ => fstBetween d m c) atTop (𝓝 0) := by
  sorry

theorem tendsto_fstRandom_atTop (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (_hc : 0 < c) :
    Tendsto (fun m : ℝ => fstRandom d m c) atTop (𝓝 0) := by
  sorry

theorem tendsto_fstBetween_demes (m c : ℝ) (hm : 0 < m) (hc : 0 < c) :
    Tendsto (fun d : ℕ => fstBetween d m c) atTop (𝓝 (c / (2 * m + c))) := by
  sorry

theorem tendsto_fstRandom_demes (m c : ℝ) (hm : 0 < m) (hc : 0 < c) :
    Tendsto (fun d : ℕ => fstRandom d m c) atTop (𝓝 (c / (2 * m + c))) := by
  sorry

theorem tendsto_fstBetween_demes_diploid (m N : ℝ) (hm : 0 < m) (hN : 0 < N) :
    Tendsto (fun d : ℕ => fstBetween d m (1 / (2 * N))) atTop
      (𝓝 (1 / (1 + 4 * N * m))) := by
  sorry

theorem tendsto_fstRandom_demes_diploid (m N : ℝ) (hm : 0 < m) (hN : 0 < N) :
    Tendsto (fun d : ℕ => fstRandom d m (1 / (2 * N))) atTop
      (𝓝 (1 / (1 + 4 * N * m))) := by
  sorry

end Rhone.Palomar.IslandPairCoalescence
