/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.TypedAncestralChain.Link

/-! # The type-carrying chain as a Markov kernel, and its trajectory measure -/

@[expose] public section

namespace Rhone.Coalescent.TypedAncestralChain

open Finset TwoLocusGenealogy LinearAlgebra.Recursion MeasureTheory ProbabilityTheory

variable {n KA KB : ℕ} {θA θB ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}
variable {σA : Fin n → Fin KA} {σB : Fin n → Fin KB}

structure TS (n KA KB : ℕ) : Type where
  st : TSt n KA KB
  deriving DecidableEq

namespace TS

def equivTSt : TS n KA KB ≃ TSt n KA KB where
  toFun := TS.st
  invFun := TS.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance : MeasurableSpace (TS n KA KB) := ⊤
instance : Fintype (TS n KA KB) := Fintype.ofEquiv _ (equivTSt (n := n) (KA := KA) (KB := KB)).symm
instance : Inhabited (TS n KA KB) := ⟨⟨((∅ : Finset (Lin n)), noneT n KA, noneT n KB)⟩⟩
instance : Nonempty (TS n KA KB) := ⟨default⟩
instance : DiscreteMeasurableSpace (TS n KA KB) := ⟨fun _ => trivial⟩
instance : MeasurableSingletonClass (TS n KA KB) := ⟨fun _ => trivial⟩

theorem st_inj {s t : TS n KA KB} : s.st = t.st ↔ s = t := by
  constructor
  · intro h; cases s; cases t; simpa using h
  · rintro rfl; rfl

end TS

noncomputable def dtotS (θA θB ρ : ℝ) (s : TS n KA KB) : ℝ := dtot θA θB ρ s.st.1

noncomputable def transS (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ)
    (s t : TS n KA KB) : ℝ := transT θA θB ρ πA πB s.st t.st

noncomputable def hitS (σA : Fin n → Fin KA) (σB : Fin n → Fin KB) (θA θB ρ : ℝ)
    (πA : Fin KA → ℝ) (πB : Fin KB → ℝ) (N : ℕ) (s : TS n KA KB) : ℝ :=
  hitNT σA σB θA θB ρ πA πB N s.st

theorem transS_nonneg (hθA : 0 ≤ θA) (hθB : 0 ≤ θB) (hρ : 0 ≤ ρ) (hπA : ∀ i, 0 ≤ πA i)
    (hπB : ∀ j, 0 ≤ πB j) (s t : TS n KA KB) : 0 ≤ transS θA θB ρ πA πB s t :=
  transT_nonneg hθA hθB hρ hπA hπB _ _

theorem sum_transS (hsA : ∑ i, πA i = 1) (hsB : ∑ j, πB j = 1) (s : TS n KA KB) :
    (∑ t : TS n KA KB, transS θA θB ρ πA πB s t) = 1 := by
  rw [Fintype.sum_equiv (TS.equivTSt (n := n) (KA := KA) (KB := KB))
    (fun t => transS θA θB ρ πA πB s t) (fun u => transT θA θB ρ πA πB s.st u)
    (fun _ => rfl)]
  exact sum_transT hsA hsB s.st

theorem transS_of_nonpos {s t : TS n KA KB} (h : ¬ 0 < dtotS θA θB ρ s) :
    transS θA θB ρ πA πB s t = if t = s then 1 else 0 := by
  rw [transS, transT_of_dtot_nonpos h]
  by_cases hts : t = s
  · rw [ite_eq_left (congrArg TS.st hts), ite_eq_left hts]
  · rw [ite_eq_right (fun hc => hts (TS.st_inj.1 hc)), ite_eq_right hts]

structure Adm (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ) : Prop where
  thA : 0 ≤ θA
  thB : 0 ≤ θB
  rho : 0 ≤ ρ
  piA : ∀ i, 0 ≤ πA i
  piB : ∀ j, 0 ≤ πB j
  sumA : ∑ i, πA i = 1
  sumB : ∑ j, πB j = 1

noncomputable def onePMFT (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ)
    (h : Adm θA θB ρ πA πB) (s : TS n KA KB) : PMF (TS n KA KB) :=
  PMF.ofFintype (fun t : TS n KA KB => ENNReal.ofReal (transS θA θB ρ πA πB s t)) (by
    have hnn : ∀ t ∈ (Finset.univ : Finset (TS n KA KB)), 0 ≤ transS θA θB ρ πA πB s t :=
      fun t _ => transS_nonneg h.thA h.thB h.rho h.piA h.piB s t
    rw [(ENNReal.ofReal_sum_of_nonneg hnn).symm, sum_transS h.sumA h.sumB s,
      ENNReal.ofReal_one])

noncomputable def argKernelT (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ)
    (h : Adm θA θB ρ πA πB) : Kernel (TS n KA KB) (TS n KA KB) where
  toFun s := (onePMFT θA θB ρ πA πB h s).toMeasure
  measurable' := Measurable.of_discrete

variable (h : Adm θA θB ρ πA πB)

theorem argKernelT_apply (s : TS n KA KB) :
    argKernelT θA θB ρ πA πB h s
      = (onePMFT θA θB ρ πA πB h s).toMeasure := rfl

instance isMarkovKernel_argKernelT :
    IsMarkovKernel (argKernelT (n := n) θA θB ρ πA πB h) :=
  ⟨fun s => by rw [argKernelT_apply]; infer_instance⟩

theorem argKernelT_singleton (s t : TS n KA KB) :
    argKernelT θA θB ρ πA πB h s {t}
      = ENNReal.ofReal (transS θA θB ρ πA πB s t) := by
  rw [argKernelT_apply, PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete]
  rfl

theorem onePMFT_of_nonpos {s : TS n KA KB} (hz : ¬ 0 < dtotS θA θB ρ s) :
    onePMFT θA θB ρ πA πB h s = PMF.pure s := by
  ext t
  have h1 : onePMFT θA θB ρ πA πB h s t
      = ENNReal.ofReal (transS θA θB ρ πA πB s t) := rfl
  rw [h1, transS_of_nonpos hz, PMF.pure_apply]
  split_ifs
  · exact ENNReal.ofReal_one
  · exact ENNReal.ofReal_zero

theorem argKernelT_of_nonpos {s : TS n KA KB} (hz : ¬ 0 < dtotS θA θB ρ s) :
    argKernelT θA θB ρ πA πB h s = Measure.dirac s := by
  rw [argKernelT_apply, onePMFT_of_nonpos h hz, PMF.toMeasure_pure]

noncomputable def argSeqT (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ)
    (h : Adm θA θB ρ πA πB) (m : ℕ) :
    Kernel ((_i : Finset.Iic m) → TS n KA KB) (TS n KA KB) :=
  (argKernelT θA θB ρ πA πB h).comap
    (fun x => x ⟨m, Finset.mem_Iic.2 le_rfl⟩) Measurable.of_discrete

instance isMarkovKernel_argSeqT (m : ℕ) :
    IsMarkovKernel (argSeqT (n := n) θA θB ρ πA πB h m) := by
  rw [argSeqT]
  infer_instance

noncomputable def argTrajT (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ)
    (h : Adm θA θB ρ πA πB) (s : TS n KA KB) :
    Measure ((_ : ℕ) → TS n KA KB) :=
  Kernel.traj (X := fun _ => TS n KA KB)
    (argSeqT θA θB ρ πA πB h) 0 (fun _ => s)

instance isProbabilityMeasure_argTrajT (s : TS n KA KB) :
    IsProbabilityMeasure
      (argTrajT (n := n) θA θB ρ πA πB h s) := by
  rw [argTrajT]
  infer_instance

end Rhone.Coalescent.TypedAncestralChain
