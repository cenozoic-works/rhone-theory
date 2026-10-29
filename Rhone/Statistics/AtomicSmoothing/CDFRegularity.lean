/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.AtomicSmoothing.MixtureLaw
public import Mathlib.Analysis.Normed.MulAction

/-! # Global regularity of the explicit finite-mixture CDFs -/

@[expose] public section

noncomputable section
open Set
open scoped BigOperators
namespace Rhone.Statistics.AtomicSmoothing

lemma exists_lipschitz_scaled {f : ℝ → ℝ} (a : ℝ)
    (hf : ∃ K, LipschitzWith K f) : ∃ K, LipschitzWith K (fun x => a * f x) := by
  obtain ⟨K, hK⟩ := hf
  refine ⟨‖a‖₊ * K, ?_⟩
  convert! (lipschitzWith_smul a).comp hK using 1

lemma exists_lipschitz_sum {α : Type*} (s : Finset α) (f : α → ℝ → ℝ)
    (hf : ∀ i ∈ s, ∃ K, LipschitzWith K (f i)) :
    ∃ K, LipschitzWith K (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨0, ?_⟩
      simp only [Finset.sum_empty]
      exact LipschitzWith.const (0 : ℝ)
  | @insert a s ha ih =>
      obtain ⟨Ka, hKa⟩ := hf a (Finset.mem_insert_self _ _)
      obtain ⟨Ks, hKs⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      exact ⟨Ka + Ks, by simpa only [Finset.sum_insert ha] using hKa.add hKs⟩

lemma componentCDF_lipschitz (a τ : ℝ) : ∃ K, LipschitzWith K (componentCDF a τ) := by
  have harg : ∃ K, LipschitzWith K (fun x : ℝ => (x - (a - τ)) / (2 * τ)) := by
    have he : ∃ K, LipschitzWith K (fun x : ℝ => (2 * τ)⁻¹ * (x - (a - τ))) :=
      exists_lipschitz_scaled _ ⟨1, by
        simpa using LipschitzWith.id.sub (LipschitzWith.const (a - τ))⟩
    simpa only [div_eq_mul_inv, mul_comm] using he
  obtain ⟨Ka, hKa⟩ := harg
  have hb : ∃ K, LipschitzWith K (fun x : ℝ => clip ((x - (a - τ)) / (2 * τ))) :=
    ⟨1 * Ka, clip_lipschitz.comp hKa⟩
  obtain ⟨K1, h1⟩ := exists_lipschitz_scaled (1 - τ) hb
  obtain ⟨K2, h2⟩ := exists_lipschitz_scaled τ ⟨1, clip_lipschitz⟩
  exact ⟨K1 + K2, h1.add h2⟩

lemma mixtureCDF_lipschitz {α : Type*} [Fintype α] (loc w : α → ℝ) (τ : ℝ) :
    ∃ K, LipschitzWith K (mixtureCDF loc w τ) := by
  exact exists_lipschitz_sum Finset.univ (fun a x => w a * componentCDF (loc a) τ x)
    (fun a _ => exists_lipschitz_scaled (w a) (componentCDF_lipschitz (loc a) τ))

lemma mixtureCDF_continuous {α : Type*} [Fintype α] (loc w : α → ℝ) (τ : ℝ) :
    Continuous (mixtureCDF loc w τ) := (mixtureCDF_lipschitz loc w τ).choose_spec.continuous

end Rhone.Statistics.AtomicSmoothing
