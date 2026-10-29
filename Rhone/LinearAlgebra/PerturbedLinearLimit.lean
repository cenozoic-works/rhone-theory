/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Algebra.GroupWithZero

/-! # Limits of solutions of perturbed finite linear systems -/

@[expose] public section

namespace Rhone.LinearAlgebra.PerturbedLinearLimit

open Filter Topology Matrix

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] {l : Filter α}

theorem tendsto_inv_of_tendsto {A : α → Matrix ι ι ℝ} {Q : Matrix ι ι ℝ}
    (hA : Tendsto A l (𝓝 Q)) (hQ : Q.det ≠ 0) : Tendsto (fun x => (A x)⁻¹) l (𝓝 Q⁻¹) := by
  have hdet : Tendsto (fun x => (A x).det) l (𝓝 Q.det) :=
    ((continuous_id.matrix_det).tendsto Q).comp hA
  have hadj : Tendsto (fun x => (A x).adjugate) l (𝓝 Q.adjugate) :=
    ((continuous_id.matrix_adjugate).tendsto Q).comp hA
  simp only [Matrix.inv_def, Ring.inverse_eq_inv']
  exact (hdet.inv₀ hQ).smul hadj

omit [DecidableEq ι] in
theorem tendsto_mulVec_of_tendsto {B : α → Matrix ι ι ℝ} {P : Matrix ι ι ℝ} {q : ι → ℝ}
    {v : α → ι → ℝ} (hB : Tendsto B l (𝓝 P)) (hv : Tendsto v l (𝓝 q)) :
    Tendsto (fun x => B x *ᵥ v x) l (𝓝 (P *ᵥ q)) := by
  have hcont : Continuous fun p : Matrix ι ι ℝ × (ι → ℝ) => p.1 *ᵥ p.2 :=
    continuous_fst.matrix_mulVec continuous_snd
  exact (hcont.tendsto (P, q)).comp (hB.prodMk_nhds hv)

theorem tendsto_of_mulVec_eq {A : α → Matrix ι ι ℝ} {Q : Matrix ι ι ℝ} {q : ι → ℝ}
    {v h : α → ι → ℝ} (hQ : Q.det ≠ 0) (hA : Tendsto A l (𝓝 Q)) (hv : Tendsto v l (𝓝 q))
    (hsol : ∀ᶠ x in l, A x *ᵥ h x = v x) :
    Tendsto h l (𝓝 (Q⁻¹ *ᵥ q)) := by
  have hmul : Tendsto (fun x => (A x)⁻¹ *ᵥ v x) l (𝓝 (Q⁻¹ *ᵥ q)) :=
    tendsto_mulVec_of_tendsto (B := fun x => (A x)⁻¹) (tendsto_inv_of_tendsto hA hQ) hv
  have hdetc : Continuous fun B : Matrix ι ι ℝ => B.det := continuous_id.matrix_det
  have hdet : ∀ᶠ x in l, (A x).det ≠ 0 :=
    ((hdetc.tendsto Q).comp hA).eventually_ne hQ
  have hev : ∀ᶠ x in l, (A x)⁻¹ *ᵥ v x = h x := by
    filter_upwards [hsol, hdet] with x hx hd
    have hu : IsUnit (A x).det := isUnit_iff_ne_zero.mpr hd
    rw [← hx, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  exact hmul.congr' hev

omit [Fintype ι] [DecidableEq ι] in
theorem tendsto_const_add {β : Type*} [TopologicalSpace β] [AddZeroClass β] [ContinuousAdd β]
    {q : β} {e : α → β} (he : Tendsto e l (𝓝 0)) : Tendsto (fun x => q + e x) l (𝓝 q) := by
  have h1 := (tendsto_const_nhds (x := q) (f := l)).add he
  rwa [add_zero] at h1

theorem tendsto_of_fixed_perturbed {Q : Matrix ι ι ℝ} {r : ι → ℝ} {E : α → Matrix ι ι ℝ}
    {e h : α → ι → ℝ} {ε : α → ℝ} (hQ : Q.det ≠ 0) (hE : Tendsto E l (𝓝 0))
    (he : Tendsto e l (𝓝 0)) (hε : ∀ᶠ x in l, ε x ≠ 0)
    (hfix : ∀ᶠ x in l, h x = (1 + ε x • (Q + E x)) *ᵥ h x + ε x • (r + e x)) :
    ∃ h₀ : ι → ℝ, Tendsto h l (𝓝 h₀) ∧ Q *ᵥ h₀ + r = 0 ∧
      ∀ g : ι → ℝ, Q *ᵥ g + r = 0 → g = h₀ := by
  have hneg : Tendsto (fun x => -e x) l (𝓝 0) := by
    have h1 := he.neg
    rwa [neg_zero] at h1
  have hsol : ∀ᶠ x in l, (Q + E x) *ᵥ h x = -r + -e x := by
    filter_upwards [hfix, hε] with x hx hx0
    have hexp : (1 + ε x • (Q + E x)) *ᵥ h x = h x + ε x • ((Q + E x) *ᵥ h x) := by
      rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
    rw [hexp, add_assoc, ← smul_add] at hx
    have h1 : ε x • ((Q + E x) *ᵥ h x + (r + e x)) = 0 := by
      have h2 := congrArg (fun w => w - h x) hx
      simpa using h2.symm
    have h3 := (smul_eq_zero.mp h1).resolve_left hx0
    rw [eq_neg_of_add_eq_zero_left h3, neg_add]
  have hu : IsUnit Q.det := isUnit_iff_ne_zero.mpr hQ
  refine ⟨Q⁻¹ *ᵥ (-r), tendsto_of_mulVec_eq hQ (tendsto_const_add hE)
    (tendsto_const_add hneg) hsol, ?_, fun g hg => ?_⟩
  · rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec, neg_add_cancel]
  · have hg' : Q *ᵥ g = -r := eq_neg_of_add_eq_zero_left hg
    rw [← hg', Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]

end Rhone.LinearAlgebra.PerturbedLinearLimit
