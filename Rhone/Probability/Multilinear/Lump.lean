/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.Multilinear.Phi
public import Rhone.Probability.Multilinear.CentredHierarchy
public import Rhone.LinearAlgebra.Tridiag.Defs

/-! # `Φ^{i,j}_t`, and the within-block part of DL‑1 -/

@[expose] public section

namespace Rhone.Probability.Multilinear

open Finset LinearAlgebra.Recursion Denominator

def canM (i j t : ℕ) : Finset (Fin i × Fin j) :=
  (univ : Finset (Fin i × Fin j)).filter fun p => (p.1 : ℕ) = (p.2 : ℕ) ∧ (p.1 : ℕ) < t

theorem mem_canM {i j t : ℕ} {p : Fin i × Fin j} :
    p ∈ canM i j t ↔ (p.1 : ℕ) = (p.2 : ℕ) ∧ (p.1 : ℕ) < t := by
  simp [canM]

theorem isMatching_canM (i j t : ℕ) : IsMatching (canM i j t) where
  fst p hp p' hp' h := by
    rw [mem_canM] at hp hp'
    have h1 : (p.1 : ℕ) = (p'.1 : ℕ) := congrArg Fin.val h
    exact Prod.ext h (Fin.ext (by omega))
  snd p hp p' hp' h := by
    rw [mem_canM] at hp hp'
    have h2 : (p.2 : ℕ) = (p'.2 : ℕ) := congrArg Fin.val h
    exact Prod.ext (Fin.ext (by omega)) h

theorem card_canM {i j t : ℕ} (hti : t ≤ i) (htj : t ≤ j) : (canM i j t).card = t := by
  have h : (canM i j t).card = (Finset.range t).card := by
    refine Finset.card_bij' (fun p _ => (p.1 : ℕ))
      (fun k hk => (⟨k, lt_of_lt_of_le (Finset.mem_range.mp hk) hti⟩,
        ⟨k, lt_of_lt_of_le (Finset.mem_range.mp hk) htj⟩)) ?_ ?_ ?_ ?_
    · intro p hp
      rw [mem_canM] at hp
      exact Finset.mem_range.mpr hp.2
    · intro k hk
      rw [mem_canM]
      exact ⟨rfl, Finset.mem_range.mp hk⟩
    · intro p hp
      rw [mem_canM] at hp
      exact Prod.ext (Fin.ext rfl) (Fin.ext hp.1)
    · intro k _
      rfl
  rw [h, Finset.card_range]

variable {F : Type*} [Field F] {SA SB : Type*}
variable [Fintype SA] [DecidableEq SA] [Fintype SB] [DecidableEq SB]

noncomputable def Phi (q : Config 2 2 → F) (πA πB : Fin 2 → F) (i j t : ℕ) : F :=
  Q q (canM i j t) (fun _ => fvec πA) (fun _ => fvec πB)

theorem Phi_eq (q : Config 2 2 → F) (πA πB : Fin 2 → F) {M : Finset (SA × SB)}
    (hM : IsMatching M) {i j t : ℕ} (hA : Fintype.card SA = i) (hB : Fintype.card SB = j)
    (ht : M.card = t) (hti : t ≤ i) (htj : t ≤ j) :
    Q q M (fun _ => fvec πA) (fun _ => fvec πB) = Phi q πA πB i j t :=
  Q_const_congr q hM (isMatching_canM i j t) (by simp [hA]) (by simp [hB])
    (by rw [ht, card_canM hti htj]) _ _

section WithinBlock

variable (q : Config 2 2 → F) (πA πB : Fin 2 → F) {M : Finset (SA × SB)} (hM : IsMatching M)
include hM

theorem isMatching_insert {k : SA} {l : SB} (hk : k ∈ freeA M) (hl : l ∈ freeB M) :
    IsMatching (insert (k, l) M) where
  fst p hp p' hp' h := by
    rcases Finset.mem_insert.mp hp with rfl | hp
    · rcases Finset.mem_insert.mp hp' with rfl | hp'
      · rfl
      · exact absurd (h ▸ rfl : p'.1 = k) (fst_ne_of_mem_freeA hk hp')
    · rcases Finset.mem_insert.mp hp' with rfl | hp'
      · exact absurd h (fst_ne_of_mem_freeA hk hp)
      · exact hM.fst _ hp _ hp' h
  snd p hp p' hp' h := by
    rcases Finset.mem_insert.mp hp with rfl | hp
    · rcases Finset.mem_insert.mp hp' with rfl | hp'
      · rfl
      · exact absurd (h ▸ rfl : p'.2 = l) (snd_ne_of_mem_freeB hl hp')
    · rcases Finset.mem_insert.mp hp' with rfl | hp'
      · exact absurd h (snd_ne_of_mem_freeB hl hp)
      · exact hM.snd _ hp _ hp' h

omit [Fintype SA] [Fintype SB] in
theorem isMatching_erase (p : SA × SB) : IsMatching (M.erase p) where
  fst _ hr _ hr' h := hM.fst _ (Finset.mem_erase.mp hr).2 _ (Finset.mem_erase.mp hr').2 h
  snd _ hr _ hr' h := hM.snd _ (Finset.mem_erase.mp hr).2 _ (Finset.mem_erase.mp hr').2 h

theorem sum_insert_lumped :
    (∑ k ∈ freeA M, ∑ l ∈ freeB M,
        Q q (insert (k, l) M) (fun _ => fvec πA) (fun _ => fvec πB))
      = (((freeA M).card * (freeB M).card : ℕ) : F)
        * Phi q πA πB (Fintype.card SA) (Fintype.card SB) (M.card + 1) := by
  have hstep : ∀ k ∈ freeA M, ∀ l ∈ freeB M,
      Q q (insert (k, l) M) (fun _ => fvec πA) (fun _ => fvec πB)
        = Phi q πA πB (Fintype.card SA) (Fintype.card SB) (M.card + 1) := by
    intro k hk l hl
    have hcard : (insert (k, l) M).card = M.card + 1 :=
      Finset.card_insert_of_notMem (mem_freeA.mp hk l)
    have hle : M.card + 1 ≤ Fintype.card SA := by
      have h1 := card_freeA hM
      have h2 : 1 ≤ (freeA M).card := Finset.card_pos.mpr ⟨k, hk⟩
      omega
    have hle' : M.card + 1 ≤ Fintype.card SB := by
      have h1 := card_freeB hM
      have h2 : 1 ≤ (freeB M).card := Finset.card_pos.mpr ⟨l, hl⟩
      omega
    exact Phi_eq q πA πB (isMatching_insert hM hk hl) rfl rfl hcard hle hle'
  rw [Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun l hl => hstep k hk l hl]
  simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_mul]
  ring

theorem sum_erase_lumped :
    (∑ p ∈ M, Q q (M.erase p) (fun _ => fvec πA) (fun _ => fvec πB))
      = ((M.card : ℕ) : F)
        * Phi q πA πB (Fintype.card SA) (Fintype.card SB) (M.card - 1) := by
  have hstep : ∀ p ∈ M, Q q (M.erase p) (fun _ => fvec πA) (fun _ => fvec πB)
      = Phi q πA πB (Fintype.card SA) (Fintype.card SB) (M.card - 1) := by
    intro p hp
    have hcard : (M.erase p).card = M.card - 1 := Finset.card_erase_of_mem hp
    have hle : M.card - 1 ≤ Fintype.card SA := by
      have h1 := card_freeA hM; omega
    have hle' : M.card - 1 ≤ Fintype.card SB := by
      have h1 := card_freeB hM; omega
    exact Phi_eq q πA πB (isMatching_erase hM p) rfl rfl hcard hle hle'
  rw [Finset.sum_congr rfl fun p hp => hstep p hp]
  simp only [Finset.sum_const, nsmul_eq_mul]

end WithinBlock

section Lumped

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA πB : Fin 2 → F}

noncomputable def matchingRecursionSource (q : Config 2 2 → F) (πA πB : Fin 2 → F)
    (M : Finset (SA × SB)) : F :=
  (∑ k ∈ freeA M, ∑ m ∈ (freeA M).erase k,
      (kap πA * Q q M (killAt (fvec πA) (insert k {m})) (fun _ => fvec πB)
        + gam πA * Q q M (killAt (fvec πA) {m}) (fun _ => fvec πB)))
    + 2 * (∑ k ∈ freeA M, ∑ p ∈ M,
      (kap πA * Q q M (killAt (fvec πA) (insert p.1 {k})) (fun _ => fvec πB)
        + gam πA * Q q M (killAt (fvec πA) {k}) (fun _ => fvec πB)))
    + (∑ l ∈ freeB M, ∑ n ∈ (freeB M).erase l,
      (kap πB * Q q M (fun _ => fvec πA) (killAt (fvec πB) (insert l {n}))
        + gam πB * Q q M (fun _ => fvec πA) (killAt (fvec πB) {n})))
    + 2 * (∑ l ∈ freeB M, ∑ p ∈ M,
      (kap πB * Q q M (fun _ => fvec πA) (killAt (fvec πB) (insert p.2 {l}))
        + gam πB * Q q M (fun _ => fvec πA) (killAt (fvec πB) {l})))
    + (∑ p ∈ M, ∑ r ∈ M.erase p,
      (kap πA * kap πB * Q q M (killAt (fvec πA) (insert p.1 {r.1}))
            (killAt (fvec πB) (insert p.2 {r.2}))
        + kap πA * gam πB * Q q M (killAt (fvec πA) (insert p.1 {r.1}))
            (killAt (fvec πB) {r.2})
        + gam πA * kap πB * Q q M (killAt (fvec πA) {r.1})
            (killAt (fvec πB) (insert p.2 {r.2}))
        + gam πA * gam πB * Q q M (killAt (fvec πA) {r.1}) (killAt (fvec πB) {r.2})))

theorem dgQ_mul_Phi_eq_matchingRecursionSource (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    {q : Config 2 2 → F} (hq : IsSolution θA θB ρ πA πB q) (M : Finset (SA × SB))
    (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1) (hM : IsMatching M) :
    dgQ θA θB ρ (Fintype.card SA) (Fintype.card SB) M.card
        * Phi q πA πB (Fintype.card SA) (Fintype.card SB) M.card
      = matchingRecursionSource q πA πB M
        + 2 * (((Fintype.card SA - M.card) * (Fintype.card SB - M.card) : ℕ) : F)
            * Phi q πA πB (Fintype.card SA) (Fintype.card SB) (M.card + 1)
        + ρ * ((M.card : ℕ) : F)
            * Phi q πA πB (Fintype.card SA) (Fintype.card SB) (M.card - 1) := by
  have hfA : (freeA M).card = Fintype.card SA - M.card := by
    have := card_freeA hM; omega
  have hfB : (freeB M).card = Fintype.card SB - M.card := by
    have := card_freeB hM; omega
  have hleA : M.card ≤ Fintype.card SA := by have := card_freeA hM; omega
  have hleB : M.card ≤ Fintype.card SB := by have := card_freeB hM; omega
  rw [← Phi_eq q πA πB hM rfl rfl rfl hleA hleB, dgQ_mul_Q_fvec hθA hθB hρ hq M hπA hπB hM,
    sum_insert_lumped q πA πB hM, sum_erase_lumped q πA πB hM, hfA, hfB, matchingRecursionSource]
  ring

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem dgQ_eq_dcoef (i j t : ℕ) : dgQ θA θB ρ i j t = LinearAlgebra.Tridiag.dcoef F i j θA θB ρ
    t := rfl

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem two_mul_eq_neg_bcoef (i j t : ℕ) :
    2 * (((i - t) * (j - t) : ℕ) : F) = -LinearAlgebra.Tridiag.bcoef F i j t := by
  simp [LinearAlgebra.Tridiag.bcoef]

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem rho_mul_eq_neg_ccoef (t : ℕ) :
    ρ * ((t + 1 : ℕ) : F) = -LinearAlgebra.Tridiag.ccoef F ρ t := by
  simp [LinearAlgebra.Tridiag.ccoef]

end Lumped

end Rhone.Probability.Multilinear
