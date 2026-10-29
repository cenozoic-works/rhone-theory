/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.TwoLocusGenealogy.Hit
public import Rhone.Probability.Denominator.Swap

/-! # The infinite-horizon hitting probability, and the identification theorem -/

@[expose] public section

namespace Rhone.Coalescent.TwoLocusGenealogy

open Finset LinearAlgebra.Recursion Filter Topology

variable {KA KB : ℕ} {θA θB ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}

noncomputable def qProb (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ)
    (ξ : Config KA KB) : ℝ := ⨆ N, fitN θA θB ρ πA πB N ξ

section Sup

variable (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (hπA : ∀ i, 0 ≤ πA i)
  (hsA : ∑ i, πA i = 1) (hπB : ∀ j, 0 ≤ πB j) (hsB : ∑ j, πB j = 1)

include hθA hθB hρ hπA hsA hπB hsB

theorem fitN_bddAbove (ξ : Config KA KB) :
    BddAbove (Set.range fun N => fitN θA θB ρ πA πB N ξ) :=
  ⟨1, by rintro x ⟨N, rfl⟩; exact fitN_le_one hθA hθB hρ hπA hsA hπB hsB N ξ⟩

theorem tendsto_fitN (ξ : Config KA KB) :
    Tendsto (fun N => fitN θA θB ρ πA πB N ξ) atTop (𝓝 (qProb θA θB ρ πA πB ξ)) :=
  tendsto_atTop_ciSup (fitN_mono' hθA hθB hρ hπA hπB ξ)
    (fitN_bddAbove hθA hθB hρ hπA hsA hπB hsB ξ)

theorem qProb_nonneg (ξ : Config KA KB) : 0 ≤ qProb θA θB ρ πA πB ξ :=
  le_ciSup_of_le (fitN_bddAbove hθA hθB hρ hπA hsA hπB hsB ξ) 0
    (fitN_nonneg hθA hθB hρ hπA hπB 0 ξ)

theorem qProb_le_one (ξ : Config KA KB) : qProb θA θB ρ πA πB ξ ≤ 1 :=
  ciSup_le fun N => fitN_le_one hθA hθB hρ hπA hsA hπB hsB N ξ

end Sup

theorem qProb_zero : qProb θA θB ρ πA πB (0 : Config KA KB) = 1 := by
  have h : ∀ N, fitN θA θB ρ πA πB N (0 : Config KA KB) = 1 :=
    fun N => fitN_of_n_eq_zero N Config.n_zero
  simp only [qProb, h, ciSup_const]

theorem tendsto_rhs {qN : ℕ → Config KA KB → ℝ} {q : Config KA KB → ℝ}
    (h : ∀ η, Tendsto (fun N => qN N η) atTop (𝓝 (q η))) (ξ : Config KA KB) :
    Tendsto (fun N => rhs θA θB ρ πA πB (qN N) ξ) atTop (𝓝 (rhs θA θB ρ πA πB q ξ)) := by
  simp only [rhs]
  refine Tendsto.add (Tendsto.add (Tendsto.add (Tendsto.add (Tendsto.add (Tendsto.add ?_ ?_)
    ?_) ?_) ?_) ?_) ?_
  · exact tendsto_finsetSum _ fun i _ => (h _).const_mul _
  · exact tendsto_finsetSum _ fun j _ => (h _).const_mul _
  · exact tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => (h _).const_mul _
  · exact tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => (h _).const_mul _
  · exact Tendsto.const_mul _ (tendsto_finsetSum _ fun i _ =>
      Tendsto.const_mul _ (((h _).const_mul _).add
        (tendsto_finsetSum _ fun j _ => (h _).const_mul _)))
  · exact Tendsto.const_mul _ (tendsto_finsetSum _ fun j _ =>
      Tendsto.const_mul _ (((h _).const_mul _).add
        (tendsto_finsetSum _ fun i _ => (h _).const_mul _)))
  · exact Tendsto.const_mul _ (tendsto_finsetSum _ fun i _ =>
      tendsto_finsetSum _ fun j _ => (h _).const_mul _)

theorem qProb_recursion (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (hπA : ∀ i, 0 ≤ πA i)
    (hsA : ∑ i, πA i = 1) (hπB : ∀ j, 0 ≤ πB j) (hsB : ∑ j, πB j = 1) {ξ : Config KA KB}
    (hn : ξ.n ≠ 0) :
    LinearAlgebra.Recursion.diag θA θB ρ ξ * qProb θA θB ρ πA πB ξ
      = rhs θA θB ρ πA πB (qProb θA θB ρ πA πB) ξ := by
  have hd : (0 : ℝ) < LinearAlgebra.Recursion.diag θA θB ρ ξ := diag_pos hθA hθB hρ (by omega)
  have h1 : Tendsto (fun N => fitN θA θB ρ πA πB (N + 1) ξ) atTop
      (𝓝 (qProb θA θB ρ πA πB ξ)) :=
    (tendsto_fitN hθA hθB hρ hπA hsA hπB hsB ξ).comp (tendsto_add_atTop_nat 1)
  have h2 : (fun N => fitN θA θB ρ πA πB (N + 1) ξ)
      = fun N => rhs θA θB ρ πA πB (fitN θA θB ρ πA πB N) ξ / LinearAlgebra.Recursion.diag θA θB ρ
          ξ :=
    funext fun N => fitN_succ_of_ne N hn
  rw [h2] at h1
  have h3 := tendsto_nhds_unique h1
    ((tendsto_rhs (fun η => tendsto_fitN hθA hθB hρ hπA hsA hπB hsB η) ξ).div_const
      (LinearAlgebra.Recursion.diag θA θB ρ ξ))
  rw [h3]
  field_simp

theorem eA_a_apply (i i' : Fin KA) :
    (Config.eA i : Config KA KB).a i' = if i' = i then 1 else 0 := by
  by_cases h : i' = i
  · subst h; simp [Config.eA, incf_self]
  · simp [Config.eA, incf_of_ne _ h, h]

theorem eB_b_apply (j j' : Fin KB) :
    (Config.eB j : Config KA KB).b j' = if j' = j then 1 else 0 := by
  by_cases h : j' = j
  · subst h; simp [Config.eB, incf_self]
  · simp [Config.eB, incf_of_ne _ h, h]

theorem eC_c_apply (i i' : Fin KA) (j j' : Fin KB) :
    (Config.eC i j : Config KA KB).c i' j' = if i' = i then (if j' = j then 1 else 0) else 0 := by
  change Config.incC (fun _ _ => 0) i j i' j' = _
  rw [incC_eq_add]
  simp [eM_apply]

@[simp] theorem eA_b_apply (i : Fin KA) (j : Fin KB) :
    (Config.eA i : Config KA KB).b j = 0 := rfl

@[simp] theorem eA_c_apply (i i' : Fin KA) (j : Fin KB) :
    (Config.eA i : Config KA KB).c i' j = 0 := rfl

@[simp] theorem eB_a_apply (i : Fin KA) (j : Fin KB) :
    (Config.eB j : Config KA KB).a i = 0 := rfl

@[simp] theorem eB_c_apply (i : Fin KA) (j j' : Fin KB) :
    (Config.eB j : Config KA KB).c i j' = 0 := rfl

@[simp] theorem eC_a_apply (i i' : Fin KA) (j : Fin KB) :
    (Config.eC i j : Config KA KB).a i' = 0 := rfl

@[simp] theorem eC_b_apply (i : Fin KA) (j j' : Fin KB) :
    (Config.eC i j : Config KA KB).b j' = 0 := rfl

@[simp] theorem nA_eA (i : Fin KA) : (Config.eA i : Config KA KB).nA = 1 := by
  simp [Config.nA, Config.sumA, Config.t, Config.eA, sum_incf]

@[simp] theorem nB_eA (i : Fin KA) : (Config.eA i : Config KA KB).nB = 0 := by
  simp [Config.nB, Config.sumB, Config.t, Config.eA]

@[simp] theorem nA_eB (j : Fin KB) : (Config.eB j : Config KA KB).nA = 0 := by
  simp [Config.nA, Config.sumA, Config.t, Config.eB]

@[simp] theorem nB_eB (j : Fin KB) : (Config.eB j : Config KA KB).nB = 1 := by
  simp [Config.nB, Config.sumB, Config.t, Config.eB, sum_incf]

@[simp] theorem t_eC (i : Fin KA) (j : Fin KB) : (Config.eC i j : Config KA KB).t = 1 := by
  simp [Config.t, Config.eC, Config.sum_incC]

@[simp] theorem nA_eC (i : Fin KA) (j : Fin KB) : (Config.eC i j : Config KA KB).nA = 1 := by
  simp [Config.nA, Config.sumA]

@[simp] theorem nB_eC (i : Fin KA) (j : Fin KB) : (Config.eC i j : Config KA KB).nB = 1 := by
  simp [Config.nB, Config.sumB]

def pAB (i : Fin KA) (j : Fin KB) : Config KA KB :=
  ⟨incf (fun _ => 0) i, incf (fun _ => 0) j, fun _ _ => 0⟩

theorem pAB_a_apply (i i' : Fin KA) (j : Fin KB) :
    (pAB i j : Config KA KB).a i' = if i' = i then 1 else 0 := by
  by_cases h : i' = i
  · subst h; simp [pAB, incf_self]
  · simp [pAB, incf_of_ne _ h, h]

theorem pAB_b_apply (i : Fin KA) (j j' : Fin KB) :
    (pAB i j : Config KA KB).b j' = if j' = j then 1 else 0 := by
  by_cases h : j' = j
  · subst h; simp [pAB, incf_self]
  · simp [pAB, incf_of_ne _ h, h]

@[simp] theorem pAB_c_apply (i i' : Fin KA) (j j' : Fin KB) :
    (pAB i j : Config KA KB).c i' j' = 0 := rfl

@[simp] theorem t_pAB (i : Fin KA) (j : Fin KB) : (pAB i j : Config KA KB).t = 0 := by
  simp [Config.t, pAB]

@[simp] theorem nA_pAB (i : Fin KA) (j : Fin KB) : (pAB i j : Config KA KB).nA = 1 := by
  simp [Config.nA, Config.sumA, Config.t, pAB, sum_incf]

@[simp] theorem nB_pAB (i : Fin KA) (j : Fin KB) : (pAB i j : Config KA KB).nB = 1 := by
  simp [Config.nB, Config.sumB, Config.t, pAB, sum_incf]

@[simp] theorem n_pAB (i : Fin KA) (j : Fin KB) : (pAB i j : Config KA KB).n = 2 := by
  simp [Config.n, Config.sumA, Config.sumB, Config.t, pAB, sum_incf]

theorem split_eC (i : Fin KA) (j : Fin KB) :
    (Config.eC i j : Config KA KB).split i j = pAB i j := by
  refine Config.ext rfl rfl ?_
  change Config.decC (Config.incC (fun _ _ => 0) i j) i j = fun _ _ => 0
  rw [incC_eq_add]
  exact decC_eM_add _ i j

theorem mergeAB_pAB (i : Fin KA) (j : Fin KB) :
    (pAB i j : Config KA KB).mergeAB i j = Config.eC i j := by
  refine Config.ext ?_ ?_ rfl
  · change decf (incf (fun _ => 0) i) i = fun _ => 0
    rw [incf_eq_add]
    exact decf_eV_add _ i
  · change decf (incf (fun _ => 0) j) j = fun _ => 0
    rw [incf_eq_add]
    exact decf_eV_add _ j

theorem eq_eA_of {η : Config KA KB} (h1 : η.nA = 1) (h2 : η.nB = 0) : ∃ i, η = Config.eA i := by
  have hn : η.n = 1 := by
    have h3 := η.n_add_t
    have h4 : η.t ≤ η.nB := η.t_le_nB
    omega
  rcases η.exists_e_of_n_eq_one hn with ⟨i, rfl⟩ | ⟨j, rfl⟩ | ⟨i, j, rfl⟩
  · exact ⟨i, rfl⟩
  · simp at h1
  · simp at h2

theorem eq_eB_of {η : Config KA KB} (h1 : η.nA = 0) (h2 : η.nB = 1) : ∃ j, η = Config.eB j := by
  have hn : η.n = 1 := by
    have h3 := η.n_add_t
    have h4 : η.t ≤ η.nA := η.t_le_nA
    omega
  rcases η.exists_e_of_n_eq_one hn with ⟨i, rfl⟩ | ⟨j, rfl⟩ | ⟨i, j, rfl⟩
  · simp at h1
  · exact ⟨j, rfl⟩
  · simp at h1

theorem homogeneous_eq_zero' (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    {d : Config KA KB → ℝ} (hd0 : d 0 = 0)
    (hrec : ∀ ξ : Config KA KB, ξ.n ≠ 0 →
      LinearAlgebra.Recursion.diag θA θB ρ ξ * d ξ = rhs θA θB ρ πA πB d ξ) :
    ∀ ξ : Config KA KB, d ξ = 0 := by
  have hlev0 : ∀ η : Config KA KB, η.nA = 0 → η.nB = 0 → d η = 0 := by
    intro η h1 h2
    rw [η.eq_zero_of_n_eq_zero (η.n_eq_zero_iff.2 ⟨h1, h2⟩), hd0]
  have hA : ∀ i : Fin KA, d (Config.eA i : Config KA KB) = 0 := by
    intro i
    have hb : ∀ η : Config KA KB, η.nA ≤ (Config.eA i : Config KA KB).nA →
        η.nB ≤ (Config.eA i : Config KA KB).nB →
        (η.nA < (Config.eA i : Config KA KB).nA ∨ η.nB < (Config.eA i : Config KA KB).nB) →
        d η = 0 := by
      intro η ha hbb hs
      rw [nA_eA] at ha hs
      rw [nB_eA] at hbb hs
      exact hlev0 η (by omega) (by omega)
    have hr := hrec (Config.eA i) (by simp)
    rw [rhs_of_vanishing_below θA θB ρ πA πB _ hb] at hr
    have hz : (∑ i', ∑ j', (((Config.eA i : Config KA KB).coalAB i' j' : ℕ) : ℝ)
          * d ((Config.eA i : Config KA KB).mergeAB i' j'))
        + ρ * ∑ i', ∑ j', (((Config.eA i : Config KA KB).c i' j' : ℕ) : ℝ)
          * d ((Config.eA i : Config KA KB).split i' j') = 0 := by
      simp [Config.coalAB]
    rw [hz] at hr
    exact (mul_eq_zero.1 hr).resolve_left (diag_pos hθA hθB hρ (by simp)).ne'
  have hB : ∀ j : Fin KB, d (Config.eB j : Config KA KB) = 0 := by
    intro j
    have hb : ∀ η : Config KA KB, η.nA ≤ (Config.eB j : Config KA KB).nA →
        η.nB ≤ (Config.eB j : Config KA KB).nB →
        (η.nA < (Config.eB j : Config KA KB).nA ∨ η.nB < (Config.eB j : Config KA KB).nB) →
        d η = 0 := by
      intro η ha hbb hs
      rw [nA_eB] at ha hs
      rw [nB_eB] at hbb hs
      exact hlev0 η (by omega) (by omega)
    have hr := hrec (Config.eB j) (by simp)
    rw [rhs_of_vanishing_below θA θB ρ πA πB _ hb] at hr
    have hz : (∑ i', ∑ j', (((Config.eB j : Config KA KB).coalAB i' j' : ℕ) : ℝ)
          * d ((Config.eB j : Config KA KB).mergeAB i' j'))
        + ρ * ∑ i', ∑ j', (((Config.eB j : Config KA KB).c i' j' : ℕ) : ℝ)
          * d ((Config.eB j : Config KA KB).split i' j') = 0 := by
      simp [Config.coalAB]
    rw [hz] at hr
    exact (mul_eq_zero.1 hr).resolve_left (diag_pos hθA hθB hρ (by simp)).ne'
  have hblock : ∀ η : Config KA KB, η.nA ≤ 1 → η.nB ≤ 1 → (η.nA < 1 ∨ η.nB < 1) → d η = 0 := by
    intro η ha hbb hs
    rcases Nat.lt_or_ge η.nA 1 with h | h
    · rcases Nat.lt_or_ge η.nB 1 with h' | h'
      · exact hlev0 η (by omega) (by omega)
      · obtain ⟨j, rfl⟩ := eq_eB_of (η := η) (by omega) (by omega)
        exact hB j
    · have hA1 : η.nA = 1 := by omega
      have hB0 : η.nB = 0 := by omega
      obtain ⟨i, rfl⟩ := eq_eA_of (η := η) hA1 hB0
      exact hA i
  have hC : ∀ (i : Fin KA) (j : Fin KB), d (Config.eC i j : Config KA KB) = 0 := by
    intro i j
    have hbC : ∀ η : Config KA KB, η.nA ≤ (Config.eC i j : Config KA KB).nA →
        η.nB ≤ (Config.eC i j : Config KA KB).nB →
        (η.nA < (Config.eC i j : Config KA KB).nA ∨ η.nB < (Config.eC i j : Config KA KB).nB) →
        d η = 0 := by
      intro η ha hbb hs
      rw [nA_eC] at ha hs
      rw [nB_eC] at hbb hs
      exact hblock η ha hbb hs
    have hbP : ∀ η : Config KA KB, η.nA ≤ (pAB i j : Config KA KB).nA →
        η.nB ≤ (pAB i j : Config KA KB).nB →
        (η.nA < (pAB i j : Config KA KB).nA ∨ η.nB < (pAB i j : Config KA KB).nB) →
        d η = 0 := by
      intro η ha hbb hs
      rw [nA_pAB] at ha hs
      rw [nB_pAB] at hbb hs
      exact hblock η ha hbb hs
    have hrC := hrec (Config.eC i j) (by simp)
    rw [rhs_of_vanishing_below θA θB ρ πA πB _ hbC] at hrC
    have hrP := hrec (pAB i j) (by simp)
    rw [rhs_of_vanishing_below θA θB ρ πA πB _ hbP] at hrP
    have hzC : (∑ i', ∑ j', (((Config.eC i j : Config KA KB).coalAB i' j' : ℕ) : ℝ)
          * d ((Config.eC i j : Config KA KB).mergeAB i' j'))
        + ρ * ∑ i', ∑ j', (((Config.eC i j : Config KA KB).c i' j' : ℕ) : ℝ)
          * d ((Config.eC i j : Config KA KB).split i' j') = ρ * d (pAB i j) := by
      simp [Config.coalAB, eC_c_apply, split_eC]
    have hzP : (∑ i', ∑ j', (((pAB i j : Config KA KB).coalAB i' j' : ℕ) : ℝ)
          * d ((pAB i j : Config KA KB).mergeAB i' j'))
        + ρ * ∑ i', ∑ j', (((pAB i j : Config KA KB).c i' j' : ℕ) : ℝ)
          * d ((pAB i j : Config KA KB).split i' j') = 2 * d (Config.eC i j) := by
      simp [Config.coalAB, pAB_a_apply, pAB_b_apply, mergeAB_pAB]
    rw [hzC] at hrC
    rw [hzP] at hrP
    have hdC : LinearAlgebra.Recursion.diag θA θB ρ (Config.eC i j : Config KA KB) = θA + θB + ρ :=
        by
      simp [LinearAlgebra.Recursion.diag]
    have hdP : LinearAlgebra.Recursion.diag θA θB ρ (pAB i j : Config KA KB) = 2 + θA + θB := by
      simp [LinearAlgebra.Recursion.diag]
    rw [hdC] at hrC
    rw [hdP] at hrP
    have hfac : (θA + θB) * (θA + θB + 2 + ρ) * d (Config.eC i j : Config KA KB) = 0 := by
      linear_combination (2 + θA + θB) * hrC + ρ * hrP
    have hne : (θA + θB) * (θA + θB + 2 + ρ) ≠ 0 := by positivity
    exact (mul_eq_zero.1 hfac).resolve_left hne
  have hbd : ∀ ξ : Config KA KB, ξ.n ≤ 1 → d ξ = 0 := by
    intro ξ hn
    rcases Nat.lt_or_ge ξ.n 1 with h | h
    · rw [ξ.eq_zero_of_n_eq_zero (by omega), hd0]
    · rcases ξ.exists_e_of_n_eq_one (by omega) with ⟨i, rfl⟩ | ⟨j, rfl⟩ | ⟨i, j, rfl⟩
      · exact hA i
      · exact hB j
      · exact hC i j
  exact LinearAlgebra.Recursion.homogeneous_eq_zero (πA := πA) (πB := πB) hθA hθB hρ hbd
    fun η hn => hrec η (by omega)

theorem qProb_eq_q (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (hπA : ∀ i, 0 ≤ πA i)
    (hsA : ∑ i, πA i = 1) (hπB : ∀ j, 0 ≤ πB j) (hsB : ∑ j, πB j = 1) :
    qProb θA θB ρ πA πB = LinearAlgebra.Recursion.q (πA := πA) (πB := πB) hθA hθB hρ := by
  have hqsol : IsSolution θA θB ρ πA πB
      (LinearAlgebra.Recursion.q (πA := πA) (πB := πB) hθA hθB hρ) := q_isSolution hθA hθB hρ
  have hqall : ∀ ξ : Config KA KB, LinearAlgebra.Recursion.diag θA θB ρ ξ
      * LinearAlgebra.Recursion.q (πA := πA) (πB := πB) hθA hθB hρ ξ
      = rhs θA θB ρ πA πB (LinearAlgebra.Recursion.q (πA := πA) (πB := πB) hθA hθB hρ) ξ :=
    Probability.Denominator.recursion_all hθA hθB hρ hqsol
  have hrec : ∀ ξ : Config KA KB, ξ.n ≠ 0 → LinearAlgebra.Recursion.diag θA θB ρ ξ
      * (qProb θA θB ρ πA πB ξ - LinearAlgebra.Recursion.q (πA := πA) (πB := πB) hθA hθB hρ ξ)
      = rhs θA θB ρ πA πB
          (fun η => qProb θA θB ρ πA πB η
            - LinearAlgebra.Recursion.q (πA := πA) (πB := πB) hθA hθB hρ η) ξ := by
    intro ξ hn
    rw [rhs_sub, mul_sub, qProb_recursion hθA hθB hρ hπA hsA hπB hsB hn, hqall ξ]
  have hd0 : qProb θA θB ρ πA πB (0 : Config KA KB)
      - LinearAlgebra.Recursion.q (πA := πA) (πB := πB) hθA hθB hρ 0 = 0 := by
    rw [qProb_zero, hqsol.empty, sub_self]
  have := homogeneous_eq_zero' (πA := πA) (πB := πB) hθA hθB hρ hd0 hrec
  funext ξ
  have h := this ξ
  linarith

theorem q_nonneg (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (hπA : ∀ i, 0 ≤ πA i)
    (hsA : ∑ i, πA i = 1) (hπB : ∀ j, 0 ≤ πB j) (hsB : ∑ j, πB j = 1) (ξ : Config KA KB) :
    0 ≤ LinearAlgebra.Recursion.q (πA := πA) (πB := πB) hθA hθB hρ ξ := by
  rw [← qProb_eq_q hθA hθB hρ hπA hsA hπB hsB]
  exact qProb_nonneg hθA hθB hρ hπA hsA hπB hsB ξ

theorem q_le_one (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (hπA : ∀ i, 0 ≤ πA i)
    (hsA : ∑ i, πA i = 1) (hπB : ∀ j, 0 ≤ πB j) (hsB : ∑ j, πB j = 1) (ξ : Config KA KB) :
    LinearAlgebra.Recursion.q (πA := πA) (πB := πB) hθA hθB hρ ξ ≤ 1 := by
  rw [← qProb_eq_q hθA hθB hρ hπA hsA hπB hsB]
  exact qProb_le_one hθA hθB hρ hπA hsA hπB hsB ξ

theorem qProb_isSolution (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (hπA : ∀ i, 0 ≤ πA i)
    (hsA : ∑ i, πA i = 1) (hπB : ∀ j, 0 ≤ πB j) (hsB : ∑ j, πB j = 1) :
    IsSolution θA θB ρ πA πB (qProb θA θB ρ πA πB) := by
  rw [qProb_eq_q hθA hθB hρ hπA hsA hπB hsB]
  exact q_isSolution hθA hθB hρ

end Rhone.Coalescent.TwoLocusGenealogy
