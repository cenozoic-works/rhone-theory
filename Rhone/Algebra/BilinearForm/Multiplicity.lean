/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.ClosedForms.Rho0

/-! # The multiplicity of a `ρ = 0` pole -/

@[expose] public section

namespace Rhone.Algebra.BilinearForm

open Finset LinearAlgebra.Recursion Config ClosedForms

variable {KA KB : ℕ}

theorem proportional_symm {i₁ j₁ k₁ i₂ j₂ k₂ : ℕ}
    (h : Proportional i₁ j₁ k₁ i₂ j₂ k₂) : Proportional i₂ j₂ k₂ i₁ j₁ k₁ := by
  obtain ⟨c, hc, hk, hi, hj⟩ := h
  have hc0 : c ≠ 0 := hc.ne'
  refine ⟨c⁻¹, inv_pos.mpr hc, ?_, ?_, ?_⟩
  · rw [hk]; field_simp
  · rw [hi]; field_simp
  · rw [hj]; field_simp

theorem proportional_trans {i₁ j₁ k₁ i₂ j₂ k₂ i₃ j₃ k₃ : ℕ}
    (h₁ : Proportional i₁ j₁ k₁ i₂ j₂ k₂) (h₂ : Proportional i₂ j₂ k₂ i₃ j₃ k₃) :
    Proportional i₁ j₁ k₁ i₃ j₃ k₃ := by
  obtain ⟨c, hc, hk, hi, hj⟩ := h₁
  obtain ⟨d, hd, hk', hi', hj'⟩ := h₂
  exact ⟨c * d, mul_pos hc hd, by rw [hk, hk']; ring, by rw [hi, hi']; ring,
    by rw [hj, hj']; ring⟩

theorem meas_le_of_below {ζ η : Config KA KB} (h : Below ζ η) : meas ζ ≤ meas η := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [meas]
  omega

theorem eq_of_proportional_of_le' {i₁ j₁ k₁ i₂ j₂ k₂ : ℕ} (h2j : 2 ≤ j₂) (h2k : 2 ≤ k₂)
    (h2k1 : 2 ≤ k₁) (hprop : Proportional i₁ j₁ k₁ i₂ j₂ k₂) (hj : j₁ = j₂) :
    i₁ = i₂ ∧ k₁ = k₂ := by
  obtain ⟨c, hc, hk, hii, hjj⟩ := hprop
  have hj2 : (0 : ℚ) < (j₂ : ℚ) := by exact_mod_cast Nat.lt_of_lt_of_le two_pos h2j
  have hc1 : c = 1 := by
    rw [hj] at hjj
    rcases mul_left_eq_self₀.mp hjj.symm with h | h
    · exact h
    · exact absurd h hj2.ne'
  subst hc1
  rw [one_mul] at hk hii
  exact ⟨by exact_mod_cast hii, mul_pred_injective h2k1 h2k (by exact_mod_cast hk)⟩

theorem nA_lt_of_proportional {η ζ : Config KA KB} (hbelow : Below ζ η)
    (hlt : meas ζ < meas η) (hηA : 2 ≤ η.nA) (hηn : 2 ≤ η.n) (hζn : 2 ≤ ζ.n)
    (hprop : Proportional ζ.nA ζ.nB ζ.n η.nA η.nB η.n) : ζ.nA < η.nA := by
  rcases lt_or_eq_of_le hbelow.2.1 with h | h
  · exact h
  · exfalso
    obtain ⟨hj, hk⟩ := eq_of_proportional_of_le hηA hηn hζn hprop h
    simp only [meas] at hlt
    omega

theorem nB_lt_of_proportional {η ζ : Config KA KB} (hbelow : Below ζ η)
    (hlt : meas ζ < meas η) (hηB : 2 ≤ η.nB) (hηn : 2 ≤ η.n) (hζn : 2 ≤ ζ.n)
    (hprop : Proportional ζ.nA ζ.nB ζ.n η.nA η.nB η.n) : ζ.nB < η.nB := by
  rcases lt_or_eq_of_le hbelow.2.2 with h | h
  · exact h
  · exfalso
    obtain ⟨hi, hk⟩ := eq_of_proportional_of_le' hηB hηn hζn hprop h
    simp only [meas] at hlt
    omega

variable {F : Type*} [CommRing F]

theorem rhs_mem_of_step {A : Subring F} {θA θB : F} {πA : Fin KA → F} {πB : Fin KB → F}
    (hθA : θA ∈ A) (hθB : θB ∈ A) (hπA : ∀ i, πA i ∈ A) (hπB : ∀ j, πB j ∈ A)
    (g : Config KA KB → F) (η : Config KA KB)
    (hg : ∀ ζ : Config KA KB, Step ζ η → g ζ ∈ A) :
    rhs θA θB 0 πA πB g η ∈ A := by
  have term : ∀ (cf : ℕ) (ζ : Config KA KB), (cf ≠ 0 → Step ζ η) →
      ((cf : ℕ) : F) * g ζ ∈ A := by
    intro cf ζ hstep
    rcases Nat.eq_zero_or_pos cf with h0 | h0
    · rw [h0]; simp
    · exact A.mul_mem (natCast_mem A cf) (hg ζ (hstep (by omega)))
  have hcoalA : ∀ i : Fin KA, ((η.coalA i : ℕ) : F) * g (η.dropA i) ∈ A := fun i =>
    term _ _ fun hcf => step_dropA η fun h0 => hcf (η.coalA_eq_zero_of h0)
  have hcoalB : ∀ j : Fin KB, ((η.coalB j : ℕ) : F) * g (η.dropB j) ∈ A := fun j =>
    term _ _ fun hcf => step_dropB η fun h0 => hcf (η.coalB_eq_zero_of h0)
  have hcoalC : ∀ (i : Fin KA) (j : Fin KB),
      ((η.coalC i j : ℕ) : F) * g (η.dropC i j) ∈ A := fun i j =>
    term _ _ fun hcf => step_dropC η fun h0 => hcf (η.coalC_eq_zero_of h0)
  have hcoalAB : ∀ (i : Fin KA) (j : Fin KB),
      ((η.coalAB i j : ℕ) : F) * g (η.mergeAB i j) ∈ A := by
    intro i j
    refine term _ _ fun hcf => step_mergeAB η ?_ ?_
    · exact fun h0 => hcf (η.coalAB_eq_zero_left j h0)
    · exact fun h0 => hcf (η.coalAB_eq_zero_right i h0)
  have hdropA : ∀ i : Fin KA, ((η.a i : ℕ) : F) * g (η.dropA i) ∈ A := fun i =>
    term _ _ fun hcf => step_dropA η hcf
  have hdropB : ∀ j : Fin KB, ((η.b j : ℕ) : F) * g (η.dropB j) ∈ A := fun j =>
    term _ _ fun hcf => step_dropB η hcf
  have hkillA : ∀ (i : Fin KA) (j : Fin KB),
      ((η.c i j : ℕ) : F) * g (η.killA i j) ∈ A := fun i j =>
    term _ _ fun hcf => step_killA η hcf
  have hkillB : ∀ (i : Fin KA) (j : Fin KB),
      ((η.c i j : ℕ) : F) * g (η.killB i j) ∈ A := fun i j =>
    term _ _ fun hcf => step_killB η hcf
  simp only [rhs]
  refine A.add_mem (A.add_mem (A.add_mem (A.add_mem (A.add_mem (A.add_mem ?_ ?_) ?_) ?_)
    (A.mul_mem hθA ?_)) (A.mul_mem hθB ?_)) ?_
  · exact A.sum_mem fun i _ => hcoalA i
  · exact A.sum_mem fun j _ => hcoalB j
  · exact A.sum_mem fun i _ => A.sum_mem fun j _ => hcoalC i j
  · exact A.sum_mem fun i _ => A.sum_mem fun j _ => hcoalAB i j
  · exact A.sum_mem fun i _ =>
      A.mul_mem (hπA i) (A.add_mem (hdropA i) (A.sum_mem fun j _ => hkillA i j))
  · exact A.sum_mem fun j _ =>
      A.mul_mem (hπB j) (A.add_mem (hdropB j) (A.sum_mem fun i _ => hkillB i j))
  · rw [zero_mul]; exact A.zero_mem

theorem q_mem_pow_of_rho_zero {A : Subring F} {θA θB : F} {πA : Fin KA → F} {πB : Fin KB → F}
    {q : Config KA KB → F} (hq : IsSolution θA θB 0 πA πB q)
    (hθA : θA ∈ A) (hθB : θB ∈ A) (hπA : ∀ i, πA i ∈ A) (hπB : ∀ j, πB j ∈ A)
    (ξ : Config KA KB) {ℓ : F} (hℓ : ℓ ∈ A) (P : Config KA KB → Prop)
    (r : Config KA KB → ℕ)
    (hmono : ∀ ζ η : Config KA KB, Below ζ η → r ζ ≤ r η)
    (hdeep : ∀ η : Config KA KB, 2 ≤ min η.nA η.nB → 2 ≤ r η)
    (hchain : ∀ η ζ : Config KA KB, Below ζ η → meas ζ < meas η →
      2 ≤ min η.nA η.nB → 2 ≤ min ζ.nA ζ.nB → P η → P ζ → r ζ < r η)
    (hstop : ∀ η : Config KA KB, Below η ξ → min η.nA η.nB ≤ 1 → q η ∈ A)
    (hinv : ∀ η : Config KA KB, Below η ξ → 2 ≤ min η.nA η.nB → ¬ P η →
      ∃ y ∈ A, diag θA θB 0 η * y = 1)
    (hdvd : ∀ η : Config KA KB, Below η ξ → 2 ≤ min η.nA η.nB → P η →
      ∃ y ∈ A, diag θA θB 0 η * y = ℓ) :
    ℓ ^ (r ξ - 1) * q ξ ∈ A := by
  have main : ∀ M : ℕ, ∀ η : Config KA KB, meas η = M → Below η ξ → ∀ b : ℕ,
      (∀ ζ : Config KA KB, Below ζ η → 2 ≤ min ζ.nA ζ.nB → P ζ → r ζ ≤ b + 1) →
      ℓ ^ b * q η ∈ A := by
    intro M
    induction M using Nat.strong_induction_on with
    | _ M IH =>
      intro η hmeas hbelow b hb
      by_cases hmin : min η.nA η.nB ≤ 1
      · exact A.mul_mem (A.pow_mem hℓ b) (hstop η hbelow hmin)
      have h2min : 2 ≤ min η.nA η.nB := by omega
      have hnA : 2 ≤ η.nA := le_trans h2min (min_le_left _ _)
      have hn : 2 ≤ η.n := le_trans hnA η.nA_le_n
      have hrec := hq.recursion η hn
      by_cases hP : P η
      · obtain ⟨y, hyA, hy⟩ := hdvd η hbelow h2min hP
        have hbη := hb η (Below.rfl η) h2min hP
        have hrη := hdeep η h2min
        have hb1 : 1 ≤ b := by omega
        have hsub : ∀ ζ : Config KA KB, Step ζ η → ℓ ^ (b - 1) * q ζ ∈ A := by
          intro ζ hstep
          have hlt := hstep.2
          refine IH (meas ζ) (by omega) ζ rfl (hstep.1.trans hbelow) (b - 1) ?_
          intro ζ' hζ' h2 hPζ'
          have hbel : Below ζ' η := hζ'.trans hstep.1
          have hlt' : meas ζ' < meas η := lt_of_le_of_lt (meas_le_of_below hζ') hlt
          have := hchain η ζ' hbel hlt' h2min h2 hP hPζ'
          omega
        have hRhs := rhs_mem_of_step hθA hθB hπA hπB
          (fun ζ => ℓ ^ (b - 1) * q ζ) η hsub
        rw [rhs_smul] at hRhs
        have hbb : b - 1 + 1 = b := by omega
        have hpow : ℓ ^ b = ℓ ^ (b - 1) * ℓ := by rw [← pow_succ, hbb]
        have hval : ℓ ^ b * q η = y * (ℓ ^ (b - 1) * rhs θA θB 0 πA πB q η) := by
          calc ℓ ^ b * q η = ℓ ^ (b - 1) * (ℓ * q η) := by rw [hpow]; ring
            _ = ℓ ^ (b - 1) * (diag θA θB 0 η * y * q η) := by rw [hy]
            _ = y * (ℓ ^ (b - 1) * (diag θA θB 0 η * q η)) := by ring
            _ = y * (ℓ ^ (b - 1) * rhs θA θB 0 πA πB q η) := by rw [hrec]
        rw [hval]
        exact A.mul_mem hyA hRhs
      · obtain ⟨y, hyA, hy⟩ := hinv η hbelow h2min hP
        have hsub : ∀ ζ : Config KA KB, Step ζ η → ℓ ^ b * q ζ ∈ A := by
          intro ζ hstep
          have hlt := hstep.2
          refine IH (meas ζ) (by omega) ζ rfl (hstep.1.trans hbelow) b ?_
          intro ζ' hζ' h2 hPζ'
          exact hb ζ' (hζ'.trans hstep.1) h2 hPζ'
        have hRhs := rhs_mem_of_step hθA hθB hπA hπB (fun ζ => ℓ ^ b * q ζ) η hsub
        rw [rhs_smul] at hRhs
        have hval : ℓ ^ b * q η = y * (ℓ ^ b * rhs θA θB 0 πA πB q η) := by
          calc ℓ ^ b * q η = diag θA θB 0 η * y * (ℓ ^ b * q η) := by rw [hy]; ring
            _ = y * (ℓ ^ b * (diag θA θB 0 η * q η)) := by ring
            _ = y * (ℓ ^ b * rhs θA θB 0 πA πB q η) := by rw [hrec]
        rw [hval]
        exact A.mul_mem hyA hRhs
  refine main (meas ξ) ξ rfl (Below.rfl ξ) (r ξ - 1) ?_
  intro ζ hζ h2 _
  have h1 := hmono ζ ξ hζ
  have h2r := hdeep ζ h2
  omega

def PropTo (i₀ j₀ k₀ : ℕ) (η : Config KA KB) : Prop :=
  Proportional η.nA η.nB η.n i₀ j₀ k₀

theorem chain_propTo_min (i₀ j₀ k₀ : ℕ) : ∀ η ζ : Config KA KB, Below ζ η → meas ζ < meas η →
    2 ≤ min η.nA η.nB → 2 ≤ min ζ.nA ζ.nB → PropTo i₀ j₀ k₀ η → PropTo i₀ j₀ k₀ ζ →
    min ζ.nA ζ.nB < min η.nA η.nB := by
  intro η ζ hbel hlt h2η h2ζ hPη hPζ
  have hηA : 2 ≤ η.nA := le_trans h2η (min_le_left _ _)
  have hηB : 2 ≤ η.nB := le_trans h2η (min_le_right _ _)
  have hζA : 2 ≤ ζ.nA := le_trans h2ζ (min_le_left _ _)
  have hprop := proportional_trans hPζ (proportional_symm hPη)
  have hA := nA_lt_of_proportional hbel hlt hηA (le_trans hηA η.nA_le_n)
    (le_trans hζA ζ.nA_le_n) hprop
  have hB := nB_lt_of_proportional hbel hlt hηB (le_trans hηA η.nA_le_n)
    (le_trans hζA ζ.nA_le_n) hprop
  omega

theorem q_mem_pow_propTo {A : Subring F} {θA θB : F} {πA : Fin KA → F} {πB : Fin KB → F}
    {q : Config KA KB → F} (hq : IsSolution θA θB 0 πA πB q)
    (hθA : θA ∈ A) (hθB : θB ∈ A) (hπA : ∀ i, πA i ∈ A) (hπB : ∀ j, πB j ∈ A)
    (ξ : Config KA KB) {ℓ : F} (hℓ : ℓ ∈ A) (i₀ j₀ k₀ : ℕ)
    (hstop : ∀ η : Config KA KB, Below η ξ → min η.nA η.nB ≤ 1 → q η ∈ A)
    (hinv : ∀ η : Config KA KB, Below η ξ → 2 ≤ min η.nA η.nB → ¬ PropTo i₀ j₀ k₀ η →
      ∃ y ∈ A, diag θA θB 0 η * y = 1)
    (hdvd : ∀ η : Config KA KB, Below η ξ → 2 ≤ min η.nA η.nB → PropTo i₀ j₀ k₀ η →
      ∃ y ∈ A, diag θA θB 0 η * y = ℓ) :
    ℓ ^ (min ξ.nA ξ.nB - 1) * q ξ ∈ A :=
  q_mem_pow_of_rho_zero hq hθA hθB hπA hπB ξ hℓ (PropTo i₀ j₀ k₀)
    (fun η => min η.nA η.nB) (fun _ _ h => by have := h.2.1; have := h.2.2; omega)
    (fun _ h => h) (chain_propTo_min i₀ j₀ k₀) hstop hinv hdvd

end Rhone.Algebra.BilinearForm
