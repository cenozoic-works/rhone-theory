module

public import Mathlib.LinearAlgebra.Matrix.Stochastic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Probability.Kernel.IonescuTulcea.Traj
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

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
set_main_module Rhone.MarkovChain.FinChain

namespace Rhone.MarkovChain

open Finset Matrix

structure FinChain (S : Type*) [Fintype S] where

  P : Matrix S S ℝ

  nonneg : ∀ x y, 0 ≤ P x y

  row_sum : ∀ x, ∑ y, P x y = 1

namespace FinChain

variable {S : Type*} [Fintype S] [DecidableEq S] (C : FinChain S)

def stepN (n : ℕ) : Matrix S S ℝ := C.P ^ n

def expect (f : S → ℝ) : S → ℝ := C.P *ᵥ f

end FinChain

end Rhone.MarkovChain

clear_aux_proof_cache
set_main_module Rhone.MarkovChain.Absorption

namespace Rhone.MarkovChain.FinChain

open Finset Filter Topology

variable {S : Type*} [Fintype S] [DecidableEq S] (C : FinChain S)

def Reaches (A : Finset S) : Prop := ∀ x, ∃ n, ∃ a ∈ A, 0 < C.stepN n x a

end Rhone.MarkovChain.FinChain

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

noncomputable def pathLaw (x : S) : Measure (ℕ → S) := P.traj x

end DiscreteProcess

end Rhone.MarkovChain

clear_aux_proof_cache
set_main_module Rhone.MarkovChain.Trajectory

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
set_main_module Rhone.MarkovChain.CountChain

namespace Rhone.MarkovChain

abbrev CountKernel (N : ℕ) : Type := Fin (N + 1) → Fin (N + 1) → ℝ

namespace CountKernel

variable {N : ℕ}

def IsStochastic (P : CountKernel N) : Prop :=
  (∀ i j, 0 ≤ P i j) ∧ ∀ i, ∑ j, P i j = 1

def expect (P : CountKernel N) (f : Fin (N + 1) → ℝ) (i : Fin (N + 1)) : ℝ :=
  ∑ j, P i j * f j

end CountKernel

end Rhone.MarkovChain

clear_aux_proof_cache
set_main_module Rhone.MarkovChain.CoreBridge

namespace Rhone.MarkovChain

open Finset

variable {N : ℕ}

namespace CountKernel

def toFinChain (P : CountKernel N) (hP : P.IsStochastic) : FinChain (Fin (N + 1)) where
  P := P
  nonneg := hP.1
  row_sum := hP.2

end CountKernel

def fixationBoundary (N : ℕ) : Finset (Fin (N + 1)) := {0, Fin.last N}

end Rhone.MarkovChain

clear_aux_proof_cache
set_main_module Rhone.MarkovChain.Cannings

namespace Rhone.MarkovChain

open Finset

structure CanningsModel (N : ℕ) (Ω : Type*) [Fintype Ω] where

  w : Ω → ℝ

  ν : Ω → Fin N → ℕ
  w_nonneg : ∀ ω, 0 ≤ w ω
  sum_w : ∑ ω, w ω = 1
  sum_ν : ∀ ω, ∑ k, ν ω k = N

  exchangeable : ∀ (σ : Equiv.Perm (Fin N)) (f : (Fin N → ℕ) → ℝ),
    ∑ ω, w ω * f (fun k => ν ω (σ k)) = ∑ ω, w ω * f (ν ω)

def moranOffspring (N : ℕ) (pd : Fin N × Fin N) (k : Fin N) : ℕ :=
  (if k = pd.2 then 0 else 1) + (if k = pd.1 then 1 else 0)

attribute [-instance] FloorSemiring.instCharZero RCLike.charZero_rclike
  StarOrderedRing.toExistsAddOfLE in

noncomputable def moranModel (N : ℕ) (hN : 0 < N) : CanningsModel N (Fin N × Fin N) where
  w _ := 1 / (N : ℝ) ^ 2
  ν := moranOffspring N
  w_nonneg _ := by positivity
  sum_w := by
    have : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast
    field_simp
  sum_ν pd := by
    have hp : ∑ k : Fin N, (if k = pd.1 then 1 else 0) = 1 := by simp
    have hd : ∑ k : Fin N, (if k = pd.2 then 0 else 1) = N - 1 := by
      have : ∀ k : Fin N, (if k = pd.2 then 0 else 1) = 1 - (if k = pd.2 then 1 else 0) := by
        intro k; split_ifs <;> simp
      simp only [this]
      rw [Finset.sum_tsub_distrib]
      · simp
      · intro k _; split_ifs <;> simp
    simp only [moranOffspring, Finset.sum_add_distrib, hp, hd]
    omega
  exchangeable σ f := by
    refine (Fintype.sum_equiv ((σ.symm).prodCongr (σ.symm)) _ _ ?_)
    intro pd
    have : (fun k => moranOffspring N pd (σ k)) =
        moranOffspring N ((σ.symm).prodCongr (σ.symm) pd) := by
      funext k
      simp only [moranOffspring, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd]
      have h1 : (σ k = pd.2) ↔ (k = σ.symm pd.2) := by
        rw [Equiv.eq_symm_apply]
      have h2 : (σ k = pd.1) ↔ (k = σ.symm pd.1) := by
        rw [Equiv.eq_symm_apply]
      simp only [h1, h2]
    rw [this]

end Rhone.MarkovChain

clear_aux_proof_cache
set_main_module Rhone.MarkovChain.CanningsCountChain

namespace Rhone.MarkovChain.CanningsModel

open Finset

variable {N : ℕ} {Ω : Type*} [Fintype Ω]

private theorem subset_count_le (M : CanningsModel N Ω) (S : Finset (Fin N)) (ω : Ω) :
    (∑ k ∈ S, M.ν ω k) ≤ N := by
  have h : (∑ k ∈ S, M.ν ω k) ≤ ∑ k : Fin N, M.ν ω k :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun _ _ _ => Nat.zero_le _)
  exact h.trans_eq (M.sum_ν ω)

noncomputable def countKernel (M : CanningsModel N Ω) : CountKernel N :=
  fun i j => ∑ ω : Ω,
    if (∑ k ∈ Finset.univ.filter (fun k : Fin N => k.val < i.val), M.ν ω k) = j.val
    then M.w ω else 0

private theorem countKernel_expect (M : CanningsModel N Ω) (f : Fin (N + 1) → ℝ)
    (i : Fin (N + 1)) :
    M.countKernel.expect f i = ∑ ω : Ω, M.w ω *
      f ⟨(∑ k ∈ Finset.univ.filter (fun k : Fin N => k.val < i.val), M.ν ω k),
        Nat.lt_succ_of_le (subset_count_le M _ ω)⟩ := by
  classical
  unfold CountKernel.expect countKernel
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  let j0 : Fin (N + 1) :=
    ⟨(∑ k ∈ Finset.univ.filter (fun k : Fin N => k.val < i.val), M.ν ω k),
      Nat.lt_succ_of_le (subset_count_le M _ ω)⟩
  change (∑ j : Fin (N + 1), (if j0.val = j.val then M.w ω else 0) * f j) =
    M.w ω * f j0
  simp only [← Fin.ext_iff]
  simp [ite_mul]

theorem countKernel_isStochastic (M : CanningsModel N Ω) : M.countKernel.IsStochastic := by
  constructor
  · intro i j
    apply Finset.sum_nonneg
    intro ω _
    split_ifs
    · exact M.w_nonneg ω
    · exact le_rfl
  · intro i
    have h := countKernel_expect M (fun _ => 1) i
    simpa only [CountKernel.expect, mul_one, M.sum_w] using h

noncomputable def countChain (M : CanningsModel N Ω) : Rhone.MarkovChain.FinChain (Fin (N + 1)) :=
  M.countKernel.toFinChain M.countKernel_isStochastic

end Rhone.MarkovChain.CanningsModel

clear_aux_proof_cache
set_main_module Rhone.MarkovChain.CanningsReachability

namespace Rhone.MarkovChain

open Finset MeasureTheory

variable {N : ℕ} {Ω : Type*} [Fintype Ω]

def CanningsModel.NonDegenerate (M : CanningsModel N Ω) : Prop :=
  ∃ ω, 0 < M.w ω ∧ ∃ k, M.ν ω k ≠ 1

noncomputable def CanningsModel.offspringProb (M : CanningsModel N Ω) (k : Fin N) (m : ℕ) : ℝ :=
  ∑ ω, if M.ν ω k = m then M.w ω else 0

noncomputable def CanningsModel.offspringSqDeviation (M : CanningsModel N Ω) (k : Fin N) : ℝ :=
  ∑ ω, M.w ω * ((M.ν ω k : ℝ) - 1) ^ 2

end Rhone.MarkovChain

clear_aux_proof_cache
set_main_module Palomar.NeutralFixation.Challenge

namespace Rhone.Palomar.NeutralFixation

open Finset MeasureTheory MarkovChain

theorem fixation_real_of_nonDegenerate {N : ℕ} {Ω : Type*} [Fintype Ω] (hN : 0 < N)
    (M : CanningsModel N Ω) (hM : CanningsModel.NonDegenerate M) (i : Fin (N + 1)) :
    (M.countChain.pathLaw i).real {ω | ∃ n, ω n = Fin.last N} = (i : ℝ) / N := by
  sorry

theorem fixation_real_eventually_of_nonDegenerate {N : ℕ} {Ω : Type*} [Fintype Ω] (hN : 0 < N)
    (M : CanningsModel N Ω) (hM : CanningsModel.NonDegenerate M) (i : Fin (N + 1)) :
    (M.countChain.pathLaw i).real {ω | ∃ n, ∀ m, n ≤ m → ω m = Fin.last N} = (i : ℝ) / N := by
  sorry

theorem loss_real_of_nonDegenerate {N : ℕ} {Ω : Type*} [Fintype Ω] (hN : 0 < N)
    (M : CanningsModel N Ω) (hM : CanningsModel.NonDegenerate M) (i : Fin (N + 1)) :
    (M.countChain.pathLaw i).real {ω | ∃ n, ω n = 0} = 1 - (i : ℝ) / N := by
  sorry

theorem fixation_real_of_not_nonDegenerate {N : ℕ} {Ω : Type*} [Fintype Ω]
    (M : CanningsModel N Ω) (hM : ¬ CanningsModel.NonDegenerate M) {i : Fin (N + 1)}
    (hi : i ≠ Fin.last N) :
    (M.countChain.pathLaw i).real {ω | ∃ n, ω n = Fin.last N} = 0 := by
  sorry

theorem cannings_fixation_ne_freq_without_reaches :
    ∃ M : CanningsModel 2 Unit,
      (M.countChain.pathLaw 1).real {ω | ∃ n, ω n = Fin.last 2} ≠ (1 : ℝ) / 2 := by
  sorry

theorem countChain_reaches_iff {N : ℕ} {Ω : Type*} [Fintype Ω] (M : CanningsModel N Ω)
    (hN : 2 ≤ N) :
    M.countChain.Reaches (fixationBoundary N) ↔ CanningsModel.NonDegenerate M := by
  sorry

theorem nonDegenerate_iff_offspringProb_zero_pos {N : ℕ} {Ω : Type*} [Fintype Ω]
    (M : CanningsModel N Ω) (k : Fin N) :
    CanningsModel.NonDegenerate M ↔ 0 < CanningsModel.offspringProb M k 0 := by
  sorry

theorem nonDegenerate_iff_offspringProb_one_lt_one {N : ℕ} {Ω : Type*} [Fintype Ω]
    (M : CanningsModel N Ω) (k : Fin N) :
    CanningsModel.NonDegenerate M ↔ CanningsModel.offspringProb M k 1 < 1 := by
  sorry

theorem nonDegenerate_iff_offspringVariance_pos {N : ℕ} {Ω : Type*} [Fintype Ω]
    (M : CanningsModel N Ω) (k : Fin N) :
    CanningsModel.NonDegenerate M ↔ 0 < CanningsModel.offspringSqDeviation M k := by
  sorry

theorem fixation_real_of_martingale {N : ℕ} (hN : 0 < N) (C : FinChain (Fin (N + 1)))
    (hm : ∀ i, C.expect (fun j => (j : ℝ)) i = i) (hR : C.Reaches (fixationBoundary N))
    (i : Fin (N + 1)) :
    (C.pathLaw i).real {ω | ∃ n, ω n = Fin.last N} = (i : ℝ) / N := by
  sorry

theorem moranModel_nonDegenerate {N : ℕ} (hN : 2 ≤ N) (h : 0 < N) :
    CanningsModel.NonDegenerate (moranModel N h) := by
  sorry

theorem moranModel_fixation_real {N : ℕ} (hN : 2 ≤ N) (h : 0 < N) (i : Fin (N + 1)) :
    ((moranModel N h).countChain.pathLaw i).real {ω | ∃ n, ω n = Fin.last N} = (i : ℝ) / N := by
  sorry

end Rhone.Palomar.NeutralFixation
