/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.EsfPair.Weight

/-! # `P(ξ_A, ξ_B)` and the ESF-pair decomposition -/

@[expose] public section

namespace Rhone.Coalescent.EsfPair

open Finset Filter Topology TwoLocusGenealogy TypedAncestralChain

variable {n KA KB : ℕ} {θA θB ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}
variable {σA : Fin n → Fin KA} {σB : Fin n → Fin KB} {ζA ζB : Blocks n}

theorem hitNP_le_absN (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (N : ℕ) {s : PSt n}
    (hs : WFP s) : hitNP ζA ζB θA θB ρ N s ≤ absN θA θB ρ N s.1 := by
  rw [← sum_hitNP_eq_absN hθA hθB hρ N hs]
  exact Finset.single_le_sum
    (f := fun x : Blocks n × Blocks n => hitNP x.1 x.2 θA θB ρ N s)
    (fun x _ => hitNP_nonneg hθA.le hθB.le hρ N s) (Finset.mem_univ (ζA, ζB))

theorem hitNP_le_one (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (N : ℕ) {s : PSt n}
    (hs : WFP s) : hitNP ζA ζB θA θB ρ N s ≤ 1 := by
  refine (hitNP_le_absN hθA hθB hρ N hs).trans ?_
  rw [absN_eq_hitN]
  exact hitN_le_one hθA hθB hρ (fun _ => zero_le_one) (by simp) (fun _ => zero_le_one) (by simp)
    N hs.wf

noncomputable def PPst (θA θB ρ : ℝ) (ζA ζB : Blocks n) (s : PSt n) : ℝ :=
  ⨆ N, hitNP ζA ζB θA θB ρ N s

def initP (n : ℕ) : PSt n := (fullState n, ∅, ∅)

noncomputable def esfKernel (θA θB ρ : ℝ) (ζA ζB : Blocks n) : ℝ :=
  PPst θA θB ρ ζA ζB (initP n)

theorem wfp_initP : WFP (initP n) := by
  refine ⟨fullState_wf, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [initP]

theorem tendsto_hitNP (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) {s : PSt n} (hs : WFP s) :
    Tendsto (fun N => hitNP ζA ζB θA θB ρ N s) atTop (𝓝 (PPst θA θB ρ ζA ζB s)) := by
  refine tendsto_atTop_ciSup (monotone_nat_of_le_succ fun N => hitNP_mono hθA hθB hρ N hs.wf) ?_
  exact ⟨1, fun y hy => by
    obtain ⟨N, rfl⟩ := hy
    exact hitNP_le_one hθA hθB hρ N hs⟩

theorem PPst_nonneg (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) {s : PSt n} (hs : WFP s) :
    0 ≤ PPst θA θB ρ ζA ζB s :=
  ge_of_tendsto' (tendsto_hitNP hθA hθB hρ hs)
    fun N => hitNP_nonneg (ζA := ζA) (ζB := ζB) hθA.le hθB.le hρ N s

theorem esfKernel_nonneg (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (ζA ζB : Blocks n) :
    0 ≤ esfKernel (n := n) θA θB ρ ζA ζB :=
  PPst_nonneg hθA hθB hρ wfp_initP

theorem PPst_weighted (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (hπA : ∀ i, 0 ≤ πA i)
    (hsA : ∑ i, πA i = 1) (hπB : ∀ j, 0 ≤ πB j) (hsB : ∑ j, πB j = 1) {s : PSt n}
    (hs : WFP s) :
    (∑ x : Blocks n × Blocks n,
        (wA σA πA x.1 * wB σB πB x.2) * PPst θA θB ρ x.1 x.2 s)
      = wA σA πA s.2.1 * wB σB πB s.2.2 * hitProb σA σB θA θB ρ πA πB s.1 := by
  have hL : Tendsto (fun N => ∑ x : Blocks n × Blocks n,
      (wA σA πA x.1 * wB σB πB x.2) * hitNP x.1 x.2 θA θB ρ N s) atTop
      (𝓝 (∑ x : Blocks n × Blocks n, (wA σA πA x.1 * wB σB πB x.2) * PPst θA θB ρ x.1 x.2 s)) :=
    tendsto_finsetSum _ fun x _ =>
      ((tendsto_hitNP hθA hθB hρ hs).const_mul (wA σA πA x.1 * wB σB πB x.2))
  have hhit : Tendsto (fun N => hitN σA σB θA θB ρ πA πB N s.1) atTop
      (𝓝 (hitProb σA σB θA θB ρ πA πB s.1)) := by
    refine tendsto_atTop_ciSup
      (monotone_nat_of_le_succ fun N => hitN_mono hθA hθB hρ hπA hπB N hs.wf) ?_
    exact ⟨1, fun y hy => by
      obtain ⟨N, rfl⟩ := hy
      exact hitN_le_one hθA hθB hρ hπA hsA hπB hsB N hs.wf⟩
  have hR : Tendsto (fun N => wA σA πA s.2.1 * wB σB πB s.2.2
      * hitN σA σB θA θB ρ πA πB N s.1) atTop
      (𝓝 (wA σA πA s.2.1 * wB σB πB s.2.2 * hitProb σA σB θA θB ρ πA πB s.1)) :=
    hhit.const_mul _
  exact tendsto_nhds_unique hL
    (by simpa only [hitNP_weighted hθA hθB hρ _ hs] using hR)

theorem cfg_initP : cfg σA σB (initP n).1 = cSample σA σB := cfg_fullState

theorem sum_esfKernel_eq_one (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) :
    (∑ x : Blocks n × Blocks n, esfKernel θA θB ρ x.1 x.2) = 1 := by
  have hL : Tendsto (fun N => ∑ x : Blocks n × Blocks n,
      hitNP x.1 x.2 θA θB ρ N (initP n)) atTop
      (𝓝 (∑ x : Blocks n × Blocks n, esfKernel θA θB ρ x.1 x.2)) :=
    tendsto_finsetSum _ fun x _ => tendsto_hitNP hθA hθB hρ wfp_initP
  have habs : Tendsto (fun N => absN θA θB ρ N (initP n).1) atTop (𝓝 1) := by
    have hmono : Monotone fun N => absN θA θB ρ N (initP n).1 := by
      refine monotone_nat_of_le_succ fun N => ?_
      rw [absN_eq_hitN, absN_eq_hitN]
      exact hitN_mono hθA hθB hρ (fun _ => zero_le_one) (fun _ => zero_le_one) N fullState_wf
    have hbdd : BddAbove (Set.range fun N => absN θA θB ρ N (initP n).1) := by
      refine ⟨1, fun y hy => ?_⟩
      obtain ⟨N, rfl⟩ := hy
      change absN θA θB ρ N (initP n).1 ≤ 1
      rw [absN_eq_hitN]
      exact hitN_le_one hθA hθB hρ (fun _ => zero_le_one) (by simp) (fun _ => zero_le_one)
        (by simp) N fullState_wf
    have := tendsto_atTop_ciSup hmono hbdd
    rwa [absProb_eq_one hθA hθB hρ (L := (initP n).1) fullState_wf] at this
  refine tendsto_nhds_unique hL ?_
  simpa only [sum_hitNP_eq_absN hθA hθB hρ _ wfp_initP] using habs

theorem esf_pair_decomposition (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hπA : ∀ i, 0 ≤ πA i) (hsA : ∑ i, πA i = 1) (hπB : ∀ j, 0 ≤ πB j) (hsB : ∑ j, πB j = 1)
    (σA : Fin n → Fin KA) (σB : Fin n → Fin KB) :
    LinearAlgebra.Recursion.q (πA := πA) (πB := πB) hθA hθB hρ (cSample σA σB)
      = ∑ ζA : Blocks n, ∑ ζB : Blocks n,
          esfKernel θA θB ρ ζA ζB * wA σA πA ζA * wB σB πB ζB := by
  have h := PPst_weighted (σA := σA) (σB := σB) hθA hθB hρ hπA hsA hπB hsB (s := initP n)
    wfp_initP
  have hinit : (initP n).1 = fullState n := rfl
  rw [hinit] at h
  have h2 : wA σA πA (initP n).2.1 = 1 := wA_empty
  have h3 : wB σB πB (initP n).2.2 = 1 := wB_empty
  rw [h2, h3, one_mul, one_mul, hitProb_fullState hθA hθB hρ hπA hsA hπB hsB] at h
  rw [← h, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun ζA _ => Finset.sum_congr rfl fun ζB _ => by
    rw [esfKernel]
    ring

theorem exists_esf_kernel {θA θB ρ : ℝ} (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (n : ℕ) :
    ∃ P : Blocks n → Blocks n → ℝ,
      (∀ ζA ζB, 0 ≤ P ζA ζB) ∧ (∑ x : Blocks n × Blocks n, P x.1 x.2) = 1 ∧
      ∀ (KA KB : ℕ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ) (_ : ∀ i, 0 ≤ πA i)
        (_ : ∑ i, πA i = 1) (_ : ∀ j, 0 ≤ πB j) (_ : ∑ j, πB j = 1)
        (σA : Fin n → Fin KA) (σB : Fin n → Fin KB),
        LinearAlgebra.Recursion.q (πA := πA) (πB := πB) hθA hθB hρ (cSample σA σB)
          = ∑ ζA : Blocks n, ∑ ζB : Blocks n, P ζA ζB * wA σA πA ζA * wB σB πB ζB :=
  ⟨esfKernel θA θB ρ, esfKernel_nonneg hθA hθB hρ, sum_esfKernel_eq_one hθA hθB hρ,
    fun _ _ _ _ hπA hsA hπB hsB σA σB =>
      esf_pair_decomposition hθA hθB hρ hπA hsA hπB hsB σA σB⟩

end Rhone.Coalescent.EsfPair
