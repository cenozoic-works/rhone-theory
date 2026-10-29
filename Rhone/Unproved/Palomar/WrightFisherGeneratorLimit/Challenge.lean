module

public import Mathlib.LinearAlgebra.Matrix.Stochastic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.Polynomial

set_option maxSynthPendingDepth 3

@[expose] public section

elab "clear_aux_proof_cache" : command =>
  Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

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

def expect (f : S → ℝ) : S → ℝ := C.P *ᵥ f

end FinChain

end Rhone.MarkovChain

clear_aux_proof_cache
set_main_module Rhone.Diffusion.GeneratorLimit

namespace Rhone.Diffusion

open Filter Topology

variable {Sₙ : ℕ → Type*} [∀ n, Fintype (Sₙ n)] {S : Type*}

noncomputable def generatorError (C : ∀ n, MarkovChain.FinChain (Sₙ n)) (τ : ℕ → ℝ)
    (σ : ∀ n, Sₙ n → S)
    (A : (S → ℝ) → S → ℝ) (f : S → ℝ) (n : ℕ) (x : Sₙ n) : ℝ :=
  τ n * ((C n).expect (f ∘ σ n) x - f (σ n x)) - A f (σ n x)

structure GeneratorLimit (C : ∀ n, MarkovChain.FinChain (Sₙ n)) (τ : ℕ → ℝ) (σ : ∀ n, Sₙ n → S)
    (A : (S → ℝ) → S → ℝ) (D : Set (S → ℝ)) : Prop where

  generator : ∀ f ∈ D, Tendsto (fun n => ⨆ x, |generatorError C τ σ A f n x|) atTop (𝓝 0)

end Rhone.Diffusion

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
set_main_module Rhone.MarkovChain.WrightFisher

namespace Rhone.MarkovChain

open Finset

def binomRow (n : ℕ) (p : ℝ) (j : ℕ) : ℝ := (n.choose j : ℝ) * p ^ j * (1 - p) ^ (n - j)

theorem binomRow_nonneg {n : ℕ} {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (j : ℕ) :
    0 ≤ binomRow n p j := by
  have : 0 ≤ 1 - p := by linarith
  unfold binomRow
  positivity

theorem sum_binomRow (n : ℕ) (p : ℝ) : ∑ j ∈ range (n + 1), binomRow n p j = 1 := by
  have := (add_pow p (1 - p) n).symm
  simpa [binomRow, mul_comm, mul_left_comm, mul_assoc] using this

noncomputable def wfRow (N i j : ℕ) : ℝ := binomRow N ((i : ℝ) / N) j

noncomputable def wf (N : ℕ) : CountKernel N := fun i j => wfRow N i j

theorem wf_apply (N : ℕ) (i j : Fin (N + 1)) : wf N i j = wfRow N i j := rfl

attribute [-instance] FloorSemiring.instCharZero RCLike.charZero_rclike in
attribute [-simp] CharP.cast_eq_zero in
private theorem freq_mem{N i : ℕ} (hi : i ≤ N) : 0 ≤ (i : ℝ) / N ∧ (i : ℝ) / N ≤ 1 := by
  refine ⟨by positivity, ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · rw [div_le_one (by exact_mod_cast hN)]; exact_mod_cast hi

theorem sum_fin_eq_range {N : ℕ} (f : ℕ → ℝ) :
    ∑ j : Fin (N + 1), f j = ∑ j ∈ range (N + 1), f j :=
  Fin.sum_univ_eq_sum_range f (N + 1)

theorem wf_isStochastic (N : ℕ) : (wf N).IsStochastic := by
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · have := freq_mem (Nat.lt_succ_iff.mp i.2)
    exact binomRow_nonneg this.1 this.2 _
  · simp only [wf_apply, wfRow]
    rw [sum_fin_eq_range (fun j => binomRow N ((i : ℝ) / N) j), sum_binomRow]

end Rhone.MarkovChain

clear_aux_proof_cache
set_main_module Rhone.MarkovChain.CoreBridge

namespace Rhone.MarkovChain

open Finset Diffusion

variable {N : ℕ}

namespace CountKernel

def toFinChain (P : CountKernel N) (hP : P.IsStochastic) : FinChain (Fin (N + 1)) where
  P := P
  nonneg := hP.1
  row_sum := hP.2

end CountKernel

noncomputable def wfChain (N : ℕ) : FinChain (Fin (N + 1)) :=
  (wf N).toFinChain (wf_isStochastic N)

end Rhone.MarkovChain

clear_aux_proof_cache
set_main_module Rhone.MarkovChain.WrightFisherDiploid

namespace Rhone.MarkovChain

noncomputable def wfDiploid (N : ℕ) : CountKernel (2 * N) := wf (2 * N)

end Rhone.MarkovChain

clear_aux_proof_cache
set_main_module Rhone.Diffusion.Generator

namespace Rhone.Diffusion

open Polynomial Finset

noncomputable def wfGenerator (f : ℝ → ℝ) (x : ℝ) : ℝ := x * (1 - x) / 2 * deriv (deriv f) x

end Rhone.Diffusion

clear_aux_proof_cache
set_main_module Rhone.Dynamics.MutationSelection

namespace Rhone.Dynamics

variable {F : Type*} [Field F]

def hapMutSelStep (s μ q : F) : F := μ + (1 - μ) * (q * (1 - s) / (1 - s * q))

end Rhone.Dynamics

clear_aux_proof_cache
set_main_module Palomar.WrightFisherGeneratorLimit.Challenge

namespace Rhone.Palomar.WrightFisherGeneratorLimit

open Finset Filter Topology Diffusion MarkovChain

theorem wf_eq_binomial (N : ℕ) (i j : Fin (N + 1)) :
    wf N i j =
      (N.choose j : ℝ) * ((i : ℝ) / N) ^ (j : ℕ) * (1 - (i : ℝ) / N) ^ (N - (j : ℕ)) := by
  sorry

theorem wf_nonneg_and_row_sum (N : ℕ) :
    (∀ i j, 0 ≤ wf N i j) ∧ ∀ i, ∑ j, wf N i j = 1 := by
  sorry

theorem wfChain_expect_eq (N : ℕ) (f : Fin (N + 1) → ℝ) (i : Fin (N + 1)) :
    (wfChain N).expect f i = ∑ j, wf N i j * f j := by
  sorry

theorem wfDiploid_eq_wf (N : ℕ) : wfDiploid N = wf (2 * N) := by
  sorry

theorem wfChain_generatorError_eq (f : ℝ → ℝ) (N : ℕ) (i : Fin (N + 1)) :
    generatorError (Sₙ := fun N => Fin (N + 1)) (fun N => wfChain N) (fun N => (N : ℝ))
        (fun N i => ((i : ℕ) : ℝ) / N) wfGenerator f N i =
      (N : ℝ) * ((wf N).expect (fun j => f ((j : ℝ) / N)) i - f ((i : ℝ) / N))
        - (i : ℝ) / N * (1 - (i : ℝ) / N) / 2 * deriv (deriv f) ((i : ℝ) / N) := by
  sorry

theorem hapMutSelStep_eq (s μ x : ℝ) :
    Rhone.Dynamics.hapMutSelStep s μ x = μ + (1 - μ) * (x * (1 - s) / (1 - s * x)) := by
  sorry

theorem wf_expect_freq_sub {N : ℕ} (hN : 1 ≤ N) (i : Fin (N + 1)) :
    (wf N).expect (fun j => (j : ℝ) / N - (i : ℝ) / N) i = 0 := by
  sorry

theorem wf_expect_freq_sub_sq {N : ℕ} (hN : 1 ≤ N) (i : Fin (N + 1)) :
    (wf N).expect (fun j => ((j : ℝ) / N - (i : ℝ) / N) ^ 2) i =
      (i : ℝ) / N * (1 - (i : ℝ) / N) / N := by
  sorry

theorem wf_expect_freq_sub_cube {N : ℕ} (hN : 1 ≤ N) (i : Fin (N + 1)) :
    (wf N).expect (fun j => ((j : ℝ) / N - (i : ℝ) / N) ^ 3) i =
      (i : ℝ) / N * (1 - (i : ℝ) / N) * (1 - 2 * ((i : ℝ) / N)) / (N : ℝ) ^ 2 := by
  sorry

theorem wf_expect_freq_sub_pow_four {N : ℕ} (hN : 1 ≤ N) (i : Fin (N + 1)) :
    (wf N).expect (fun j => ((j : ℝ) / N - (i : ℝ) / N) ^ 4) i =
      (i : ℝ) / N * (1 - (i : ℝ) / N)
        * (1 + 3 * ((N : ℝ) - 2) * ((i : ℝ) / N) * (1 - (i : ℝ) / N)) / (N : ℝ) ^ 3 := by
  sorry

theorem wf_expect_freq_sub_pow_four_le {N : ℕ} (hN : 1 ≤ N) (i : Fin (N + 1)) :
    (wf N).expect (fun j => ((j : ℝ) / N - (i : ℝ) / N) ^ 4) i ≤ 3 / (16 * (N : ℝ) ^ 2) := by
  sorry

theorem wf_expect_abs_freq_sub_cube_le {N : ℕ} (hN : 1 ≤ N) (i : Fin (N + 1)) :
    (wf N).expect (fun j => |(j : ℝ) / N - (i : ℝ) / N| ^ 3) i ≤
      7 / (32 * (N * √(N : ℝ))) := by
  sorry

theorem wf_generator_error_le {f f' f'' : ℝ → ℝ} {L : ℝ}
    (hf : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt f (f' x) (Set.Icc 0 1) x)
    (hf' : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt f' (f'' x) (Set.Icc 0 1) x)
    (hL : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, |f'' x - f'' y| ≤ L * |x - y|)
    {N : ℕ} (hN : 1 ≤ N) (i : Fin (N + 1)) :
    |(N : ℝ) * ((wf N).expect (fun j => f ((j : ℝ) / N)) i - f ((i : ℝ) / N))
        - (i : ℝ) / N * (1 - (i : ℝ) / N) / 2 * f'' ((i : ℝ) / N)|
      ≤ 7 * L / (192 * √(N : ℝ)) := by
  sorry

theorem wfDiploid_generator_error_le {f f' f'' : ℝ → ℝ} {L : ℝ}
    (hf : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt f (f' x) (Set.Icc 0 1) x)
    (hf' : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt f' (f'' x) (Set.Icc 0 1) x)
    (hL : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, |f'' x - f'' y| ≤ L * |x - y|)
    {N : ℕ} (hN : 1 ≤ N) (i : Fin (2 * N + 1)) :
    |((2 * N : ℕ) : ℝ) * ((wfDiploid N).expect (fun j => f ((j : ℝ) / (2 * N : ℕ))) i
          - f ((i : ℝ) / (2 * N : ℕ)))
        - (i : ℝ) / (2 * N : ℕ) * (1 - (i : ℝ) / (2 * N : ℕ)) / 2
          * f'' ((i : ℝ) / (2 * N : ℕ))|
      ≤ 7 * L / (192 * √((2 * N : ℕ) : ℝ)) := by
  sorry

theorem wfChain_generatorError_le {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f) {M : ℝ}
    (hM : ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (deriv (deriv f)) x| ≤ M)
    {N : ℕ} (hN : 1 ≤ N) (i : Fin (N + 1)) :
    |generatorError (Sₙ := fun N => Fin (N + 1)) (fun N => wfChain N) (fun N => (N : ℝ))
        (fun N i => ((i : ℕ) : ℝ) / N) wfGenerator f N i| ≤ 7 * M / (192 * √(N : ℝ)) := by
  sorry

theorem wf_generatorLimit :
    GeneratorLimit (Sₙ := fun N => Fin (N + 1)) (fun N => wfChain N) (fun N => (N : ℝ))
      (fun N i => ((i : ℕ) : ℝ) / N) wfGenerator {f | ContDiff ℝ 3 f} := by
  sorry

theorem wf_generator_eventually_le {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ i : Fin (N + 1),
      |(N : ℝ) * ((wf N).expect (fun j => f ((j : ℝ) / N)) i - f ((i : ℝ) / N))
        - (i : ℝ) / N * (1 - (i : ℝ) / N) / 2 * deriv (deriv f) ((i : ℝ) / N)| ≤ ε := by
  sorry

theorem sum_binomRow_freq_sub {N : ℕ} (hN : 1 ≤ N) (q x : ℝ) :
    ∑ j ∈ range (N + 1), binomRow N q j * ((j : ℝ) / N - x) = q - x := by
  sorry

theorem sum_binomRow_freq_sub_sq {N : ℕ} (hN : 1 ≤ N) (q x : ℝ) :
    ∑ j ∈ range (N + 1), binomRow N q j * ((j : ℝ) / N - x) ^ 2 =
      q * (1 - q) / N + (q - x) ^ 2 := by
  sorry

theorem hapMutSel_drift_error_le {σ ν x : ℝ} (hσ : 0 ≤ σ) (hν : 0 ≤ ν)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) {N : ℕ} (hN : 2 * σ ≤ N) (hN1 : 1 ≤ N) :
    |(N : ℝ) * (∑ j ∈ range (N + 1),
          binomRow N (ν / N + (1 - ν / N) * (x * (1 - σ / N) / (1 - σ / N * x))) j
            * ((j : ℝ) / N - x))
        - (1 - x) * (ν - σ * x)| ≤ 2 * σ * (ν + σ) / N := by
  sorry

theorem hapMutSel_drift_tendsto {σ ν x : ℝ} (hσ : 0 ≤ σ) (hν : 0 ≤ ν)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    Tendsto (fun N : ℕ => (N : ℝ) * (∑ j ∈ range (N + 1),
        binomRow N (ν / N + (1 - ν / N) * (x * (1 - σ / N) / (1 - σ / N * x))) j
          * ((j : ℝ) / N - x)))
      atTop (𝓝 ((1 - x) * (ν - σ * x))) := by
  sorry

end Rhone.Palomar.WrightFisherGeneratorLimit
