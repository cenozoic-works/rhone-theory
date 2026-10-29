/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.ChainIncrements
public import Rhone.Diffusion.PathModulus
public import Rhone.Probability.ContinuousPathMoments

/-! # Measurability of rescaled chain paths and the fourth moment of one step -/

@[expose] public section

namespace Rhone

open MeasureTheory Filter Set Analysis MarkovChain Probability
open scoped NNReal

variable {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S]

theorem Diffusion.measurable_interpolatePrefix_piLE (g : S → ℝ) (k : ℕ) (u : ℝ) :
    Measurable[Filtration.piLE (X := fun _ : ℕ => S) k]
      fun ω : ℕ → S => Diffusion.interpolatePrefix (fun m => g (ω m)) k u := by
  have hm : ∀ l ≤ k, Measurable[Filtration.piLE (X := fun _ : ℕ => S) k]
      fun ω : ℕ → S => g (ω l) := fun l hl =>
    (Measurable.of_discrete (f := g)).comp ((DiscreteProcess.measurable_eval_piLE (S := S) l).mono
      ((Filtration.piLE (X := fun _ : ℕ => S)).mono hl) le_rfl)
  unfold Diffusion.interpolatePrefix
  refine (hm 0 (Nat.zero_le _)).add (Finset.measurable_sum _ fun l hl => ?_)
  have hl' := Finset.mem_range.1 hl
  exact ((hm (l + 1) hl').sub (hm l hl'.le)).mul_const _

theorem Diffusion.measurable_interpolate_piLE (g : S → ℝ) {k : ℕ} {u : ℝ} (hu : u ≤ k) :
    Measurable[Filtration.piLE (X := fun _ : ℕ => S) k]
      fun ω : ℕ → S => Diffusion.interpolate (fun m => g (ω m)) u := by
  have e : (fun ω : ℕ → S => Diffusion.interpolate (fun m => g (ω m)) u) =
      fun ω => Diffusion.interpolatePrefix (fun m => g (ω m)) k u :=
    funext fun ω => Diffusion.interpolate_eq_interpolatePrefix _ hu
  rw [e]
  exact Diffusion.measurable_interpolatePrefix_piLE g k u

theorem Diffusion.measurable_interpolate (g : S → ℝ) (u : ℝ) :
    Measurable fun ω : ℕ → S => Diffusion.interpolate (fun m => g (ω m)) u :=
  (Diffusion.measurable_interpolate_piLE g (Nat.le_ceil u)).mono (Filtration.piLE.le _) le_rfl

theorem Diffusion.measurable_rescaledPath (g : S → ℝ) (τ : ℝ) :
    Measurable fun ω : ℕ → S => Diffusion.rescaledPath τ fun m => g (ω m) := by
  have h : Measurable fun ω : ℕ → S => fun t : ℝ≥0 => (Diffusion.rescaledPath τ fun m => g (ω m))
      t :=
    measurable_pi_iff.2 fun t => Diffusion.measurable_interpolate g _
  intro s hs
  have hs' : MeasurableSet[MeasurableSpace.comap (fun (w : C(ℝ≥0, ℝ)) (t : ℝ≥0) => w t)
      MeasurableSpace.pi] s := by
    rw [← measurableSpace_eq_comap_coeFn]
    exact hs
  obtain ⟨B, hB, rfl⟩ := hs'
  exact h hB

namespace MarkovChain.FinChain

variable [Fintype S] (C : FinChain S)

theorem integral_step_pow_four_le (g : S → ℝ) {q : ℝ}
    (hq : ∀ z, C.expect (fun w => (g w - g z) ^ 4) z ≤ q) (x : S) (l : ℕ) :
    ∫ ω, (g (ω (l + 1)) - g (ω l)) ^ 4 ∂C.pathLaw x ≤ q := by
  have h1 := C.integral_mul_eval_succ_two x l (fun a b => (g b - g a) ^ 4)
    (h := fun _ => (1 : ℝ)) stronglyMeasurable_const (B := 1) (fun _ => by simp)
  simp only [one_mul] at h1
  rw [h1]
  have hi : Integrable (fun ω : ℕ → S => C.expect (fun w => (g w - g (ω l)) ^ 4) (ω l))
      (C.pathLaw x) := C.integrable_eval (fun z => C.expect (fun w => (g w - g z) ^ 4) z) l x
  calc ∫ ω, C.expect (fun w => (g w - g (ω l)) ^ 4) (ω l) ∂C.pathLaw x
      ≤ ∫ _ω, q ∂C.pathLaw x := integral_mono hi (integrable_const q) fun ω => hq (ω l)
    _ = q := by simp

theorem integrable_step_pow_four (g : S → ℝ) (x : S) (l : ℕ) :
    Integrable (fun ω : ℕ → S => (g (ω (l + 1)) - g (ω l)) ^ 4) (C.pathLaw x) :=
  C.integrable_three x (fun a b _ => (g b - g a) ^ 4) l (l + 1) 0

end MarkovChain.FinChain

end Rhone
