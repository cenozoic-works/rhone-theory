/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.TwoLocusGenealogy.Prob

/-! # The one-step law is a probability distribution, and absorption is almost sure -/

@[expose] public section

namespace Rhone.Coalescent.TwoLocusGenealogy

open Finset LinearAlgebra.Recursion

variable {n KA KB : ℕ}
variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}
variable {σA : Fin n → Fin KA} {σB : Fin n → Fin KB}

theorem matchA_nonneg (hπA : ∀ i, 0 ≤ πA i) (S : Finset (Fin n)) :
    0 ≤ matchA σA πA S :=
  Finset.sum_nonneg fun i _ => by split_ifs; exacts [hπA i, le_rfl]

theorem matchB_nonneg (hπB : ∀ j, 0 ≤ πB j) (T : Finset (Fin n)) :
    0 ≤ matchB σB πB T :=
  Finset.sum_nonneg fun j _ => by split_ifs; exacts [hπB j, le_rfl]

theorem matchA_le_one (hπA : ∀ i, 0 ≤ πA i) (hsA : ∑ i, πA i = 1) (S : Finset (Fin n)) :
    matchA σA πA S ≤ 1 := by
  rw [← hsA]
  exact Finset.sum_le_sum fun i _ => by split_ifs; exacts [le_rfl, hπA i]

theorem matchB_le_one (hπB : ∀ j, 0 ≤ πB j) (hsB : ∑ j, πB j = 1) (T : Finset (Fin n)) :
    matchB σB πB T ≤ 1 := by
  rw [← hsB]
  exact Finset.sum_le_sum fun j _ => by split_ifs; exacts [le_rfl, hπB j]

theorem step_nonneg (hθA : 0 ≤ θA) (hθB : 0 ≤ θB) (hρ : 0 ≤ ρ) (hπA : ∀ i, 0 ≤ πA i)
    (hπB : ∀ j, 0 ≤ πB j) {g : Finset (Lin n) → F} (hg : ∀ M, 0 ≤ g M)
    (L : Finset (Lin n)) : 0 ≤ step σA σB θA θB ρ πA πB g L := by
  refine add_nonneg (add_nonneg (add_nonneg ?_ ?_) ?_) ?_
  · exact Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => hg _
  · exact mul_nonneg hθA (Finset.sum_nonneg fun p _ =>
      mul_nonneg (matchA_nonneg hπA _) (hg _))
  · exact mul_nonneg hθB (Finset.sum_nonneg fun p _ =>
      mul_nonneg (matchB_nonneg hπB _) (hg _))
  · exact mul_nonneg hρ (Finset.sum_nonneg fun p _ => hg _)

def stepU (θA θB ρ : F) (g : Finset (Lin n) → F) (L : Finset (Lin n)) : F :=
  (∑ p ∈ L, ∑ q ∈ L.erase p, g (coalL L p q))
    + θA * (∑ p ∈ carA L, g (mutAL L p))
    + θB * (∑ p ∈ carB L, g (mutBL L p))
    + ρ * (∑ p ∈ carC L, g (recL L p))

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem stepU_one (L : Finset (Lin n)) : stepU θA θB ρ (fun _ => (1 : F)) L = dtot θA θB ρ L := by
  have h1 : (∑ p ∈ L, ∑ q ∈ L.erase p, (1 : F)) = ((L.card * (L.card - 1) : ℕ) : F) := by
    have hin : ∀ p ∈ L, (∑ _q ∈ L.erase p, (1 : F)) = ((L.card - 1 : ℕ) : F) := by
      intro p hp
      rw [Finset.sum_const, Finset.card_erase_of_mem hp, nsmul_eq_mul, mul_one]
    rw [Finset.sum_congr rfl hin, Finset.sum_const, nsmul_eq_mul]
    push_cast
    ring
  have h2 : (∑ _p ∈ carA L, (1 : F)) = ((na L : ℕ) : F) := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one, na]
  have h3 : (∑ _p ∈ carB L, (1 : F)) = ((nb L : ℕ) : F) := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one, nb]
  have h4 : (∑ _p ∈ carC L, (1 : F)) = ((tt L : ℕ) : F) := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one, tt]
  rw [stepU, h1, h2, h3, h4, dtot]

theorem step_one_le_dtot (hθA : 0 ≤ θA) (hθB : 0 ≤ θB) (hπA : ∀ i, 0 ≤ πA i)
    (hsA : ∑ i, πA i = 1) (hπB : ∀ j, 0 ≤ πB j) (hsB : ∑ j, πB j = 1) (L : Finset (Lin n)) :
    step σA σB θA θB ρ πA πB (fun _ => (1 : F)) L ≤ dtot θA θB ρ L := by
  rw [← stepU_one (θA := θA) (θB := θB) (ρ := ρ) L, step, stepU]
  have hA : θA * (∑ p ∈ carA L, matchA σA πA p.1 * (1 : F))
      ≤ θA * (∑ _p ∈ carA L, (1 : F)) := by
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun p _ => ?_) hθA
    rw [mul_one]
    exact matchA_le_one hπA hsA _
  have hB : θB * (∑ p ∈ carB L, matchB σB πB p.2 * (1 : F))
      ≤ θB * (∑ _p ∈ carB L, (1 : F)) := by
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun p _ => ?_) hθB
    rw [mul_one]
    exact matchB_le_one hπB hsB _
  linarith

def absN (θA θB ρ : F) : ℕ → Finset (Lin n) → F
  | 0, L => if L = ∅ then 1 else 0
  | N + 1, L =>
      if L = ∅ then 1 else stepU θA θB ρ (absN θA θB ρ N) L / dtot θA θB ρ L

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem matchA_one_allele (S : Finset (Fin n)) :
    matchA (fun _ => (0 : Fin 1)) (fun _ => (1 : F)) S = 1 := by
  rw [matchA, Fin.sum_univ_one, ite_eq_left fun _ _ => rfl]

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem matchB_one_allele (T : Finset (Fin n)) :
    matchB (fun _ => (0 : Fin 1)) (fun _ => (1 : F)) T = 1 := by
  rw [matchB, Fin.sum_univ_one, ite_eq_left fun _ _ => rfl]

theorem clean_one_allele (L : Finset (Lin n)) :
    Clean (fun _ => (0 : Fin 1)) (fun _ => (0 : Fin 1)) L :=
  fun _ _ => ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem absN_eq_hitN (N : ℕ) (L : Finset (Lin n)) :
    absN θA θB ρ N L = hitN (fun _ => (0 : Fin 1)) (fun _ => (0 : Fin 1)) θA θB ρ
      (fun _ => (1 : F)) (fun _ => (1 : F)) N L := by
  induction N generalizing L with
  | zero => rfl
  | succ N ih =>
    by_cases h : L = ∅
    · subst h; simp [absN]
    · rw [absN, ite_eq_right h, hitN_succ_of_ne N h]
      have hstep : stepU θA θB ρ (absN θA θB ρ N) L
          = step (fun _ => (0 : Fin 1)) (fun _ => (0 : Fin 1)) θA θB ρ
              (fun _ => (1 : F)) (fun _ => (1 : F))
              (hitN (fun _ => (0 : Fin 1)) (fun _ => (0 : Fin 1)) θA θB ρ
                (fun _ => (1 : F)) (fun _ => (1 : F)) N) L := by
        rw [step, stepU]
        simp only [matchA_one_allele, matchB_one_allele, one_mul, ih]
      rw [hstep]

theorem absProb_eq_one {θA θB ρ : ℝ} (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    {L : Finset (Lin n)} (hw : WF L) : (⨆ N, absN θA θB ρ N L) = 1 := by
  have hπ : ∀ _i : Fin 1, (0 : ℝ) ≤ 1 := fun _ => zero_le_one
  have hs : (∑ _i : Fin 1, (1 : ℝ)) = 1 := by simp
  have h : (fun N => absN θA θB ρ N L)
      = fun N => hitN (fun _ => (0 : Fin 1)) (fun _ => (0 : Fin 1)) θA θB ρ
        (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) N L := funext fun N => absN_eq_hitN N L
  rw [h]
  have hp := hitProb_eq_q (σA := fun _ => (0 : Fin 1)) (σB := fun _ => (0 : Fin 1))
    hθA hθB hρ hπ hs hπ hs hw (clean_one_allele L)
  rw [hitProb] at hp
  rw [hp, LinearAlgebra.Recursion.q_eq_one hθA hθB hρ]

end Rhone.Coalescent.TwoLocusGenealogy
