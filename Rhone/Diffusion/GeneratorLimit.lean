/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.FinChain
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # Convergence of generators -/

@[expose] public section

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

namespace GeneratorLimit

variable {C : ∀ n, MarkovChain.FinChain (Sₙ n)} {τ : ℕ → ℝ} {σ : ∀ n, Sₙ n → S}
  {A : (S → ℝ) → S → ℝ} {D : Set (S → ℝ)}

theorem of_bound
    (h : ∀ f ∈ D, ∃ b : ℕ → ℝ, Tendsto b atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, ∀ x, |generatorError C τ σ A f n x| ≤ b n) :
    GeneratorLimit C τ σ A D := by
  refine ⟨fun f hf => ?_⟩
  obtain ⟨b, hb, hle⟩ := h f hf
  have hb' : Tendsto (fun n => |b n|) atTop (𝓝 0) := by
    have := hb.abs
    rwa [abs_zero] at this
  refine squeeze_zero' (Eventually.of_forall fun n => Real.iSup_nonneg fun x => abs_nonneg _)
    ?_ hb'
  filter_upwards [hle] with n hn
  exact Real.iSup_le (fun x => (hn x).trans (le_abs_self _)) (abs_nonneg _)

theorem eventually_le (h : GeneratorLimit C τ σ A D) {f : S → ℝ} (hf : f ∈ D) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ n in atTop, ∀ x, |generatorError C τ σ A f n x| ≤ ε := by
  filter_upwards [(h.generator f hf).eventually (gt_mem_nhds hε)] with n hn x
  exact (le_ciSup (Set.finite_range fun x => |generatorError C τ σ A f n x|).bddAbove x).trans
    hn.le

theorem mono (h : GeneratorLimit C τ σ A D) {D' : Set (S → ℝ)} (hD : D' ⊆ D) :
    GeneratorLimit C τ σ A D' :=
  ⟨fun f hf => h.generator f (hD hf)⟩

end GeneratorLimit

end Rhone.Diffusion
