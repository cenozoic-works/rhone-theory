/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.Denominator.Split
public import Rhone.Algebra.Denominator.Transfer
public import Rhone.Algebra.Denominator.Order
public import Rhone.LinearAlgebra.GaloisDegreeSeven.Positive

/-! # Sharpness of the denominator transfers from `Φ` to `q` -/

@[expose] public section

namespace Rhone.Probability.Denominator

open Finset LinearAlgebra.Recursion LinearAlgebra.Multilinear Multilinear LinearAlgebra.SlotDeletion
    SlotDeletion

section Positivity

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] {θA θB ρ : F}

theorem poch_pos {θ : F} (hθ : 0 < θ) (n : ℕ) : 0 < poch θ n :=
  Finset.prod_pos fun k _ => by
    have : (0 : F) ≤ (k : F) := Nat.cast_nonneg k
    linarith

theorem Erect_pos (hA : 0 ≤ θA) (hB : 0 ≤ θB) (hρ : 0 ≤ ρ) (i j : ℕ) :
    0 < Erect θA θB ρ i j :=
  Finset.prod_pos fun _ hp => Finset.prod_pos fun _ hs =>
    LinearAlgebra.GaloisDegreeSeven.E_pos (Finset.mem_Ico.mp hp).1 (Finset.mem_Ico.mp hs).1 hA hB hρ

theorem Dfull_pos (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (i j : ℕ) :
    0 < Dfull θA θB ρ i j := by
  rw [Dfull]
  exact mul_pos (mul_pos (poch_pos hθA i) (poch_pos hθB j))
    (Erect_pos hθA.le hθB.le hρ i j)

theorem Dcut_pos (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) {i : ℕ} (hi : 2 ≤ i) (j : ℕ) :
    0 < Dcut θA θB ρ i j := by
  rw [Dcut]
  refine mul_pos (mul_pos (poch_pos hθA i) (poch_pos hθB j))
    (mul_pos (Erect_pos hθA.le hθB.le hρ _ _) ?_)
  exact Finset.prod_pos fun _ hs =>
    LinearAlgebra.GaloisDegreeSeven.E_pos hi (Finset.mem_Ico.mp hs).1 hθA.le hθB.le hρ

end Positivity

section Membership

variable {F : Type*} [Field F] {θA θB ρ : F} (A : Subring F)

theorem Dfull_mem (haA : θA ∈ A) (haB : θB ∈ A) (haρ : ρ ∈ A) (i j : ℕ) :
    Dfull θA θB ρ i j ∈ A := by
  have h : A.subtype (Dfull (⟨θA, haA⟩ : A) ⟨θB, haB⟩ ⟨ρ, haρ⟩ i j) = Dfull θA θB ρ i j :=
    Dfull_map A.subtype (⟨θA, haA⟩ : A) ⟨θB, haB⟩ ⟨ρ, haρ⟩ i j
  rw [← h]
  exact (Dfull (⟨θA, haA⟩ : A) ⟨θB, haB⟩ ⟨ρ, haρ⟩ i j).2

theorem Dcut_mem (haA : θA ∈ A) (haB : θB ∈ A) (haρ : ρ ∈ A) (i j : ℕ) :
    Dcut θA θB ρ i j ∈ A := by
  have h : A.subtype (Dcut (⟨θA, haA⟩ : A) ⟨θB, haB⟩ ⟨ρ, haρ⟩ i j) = Dcut θA θB ρ i j :=
    Dcut_map A.subtype (⟨θA, haA⟩ : A) ⟨θB, haB⟩ ⟨ρ, haρ⟩ i j
  rw [← h]
  exact (Dcut (⟨θA, haA⟩ : A) ⟨θB, haB⟩ ⟨ρ, haρ⟩ i j).2

theorem E_mem (haA : θA ∈ A) (haB : θB ∈ A) (haρ : ρ ∈ A) (i j : ℕ) :
    LinearAlgebra.Tridiag.E F i j θA θB ρ ∈ A := by
  have h : A.subtype (LinearAlgebra.Tridiag.E A i j (⟨θA, haA⟩ : A) ⟨θB, haB⟩ ⟨ρ, haρ⟩)
      = LinearAlgebra.Tridiag.E F i j θA θB ρ :=
    LinearAlgebra.Tridiag.E_map A.subtype i j (⟨θA, haA⟩ : A) ⟨θB, haB⟩ ⟨ρ, haρ⟩
  rw [← h]
  exact (LinearAlgebra.Tridiag.E A i j (⟨θA, haA⟩ : A) ⟨θB, haB⟩ ⟨ρ, haρ⟩).2

end Membership

universe u

section Labelled

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA πB : Fin 2 → F} {q : Config 2 2 → F}
variable {SA SB : Type u} [Fintype SA] [DecidableEq SA] [Fintype SB] [DecidableEq SB]

theorem dvdIn_E_of_clears_labelled (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hq : IsSolution θA θB ρ πA πB q) (A : Subring F)
    (haA : θA ∈ A) (haB : θB ∈ A) (haρ : ρ ∈ A)
    (hπAm : ∀ i, πA i ∈ A) (hπBm : ∀ j, πB j ∈ A)
    (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1)
    (M : Finset (SA × SB)) (hM : IsMatching M) (α : SA → Fin 2) (β : SB → Fin 2)
    (hiA : 2 ≤ Fintype.card SA) (hiB : 2 ≤ Fintype.card SB)
    (hH : Algebra.Denominator.IsRedDenom A (Phi q πA πB (Fintype.card SA) (Fintype.card SB) M.card)
      (Dfull θA θB ρ (Fintype.card SA) (Fintype.card SB)))
    {d : F} (hd : Algebra.Denominator.Clears A (q (xi M α β)) d) :
    Algebra.Denominator.DvdIn A
        (LinearAlgebra.Tridiag.E F (Fintype.card SA) (Fintype.card SB) θA θB ρ) d :=
  Algebra.Denominator.dvdIn_of_split_clears
      (q_xi_eq_topCoeff_mul_Phi_add_psi hθA hθB hρ hq hπA hπB M hM α β)
    (topCoeff_mul_self α β) (topCoeff_mem A α β)
    ⟨Dcut_mem A haA haB haρ _ _,
      Dcut_mul_psi_mem hθA hθB hρ hq A haA haB haρ hπAm hπBm hπA hπB M α β hiA⟩
    (Dcut_pos hθA hθB hρ hiA _).ne' (Dcut_mul_E θA θB ρ hiA hiB).symm hH hd

end Labelled

section Cfg

variable {F : Type*} [Field F] {πA πB : Fin 2 → F} {q : Config 2 2 → F}

theorem card_matchOf (ξ : Config 2 2) : (matchOf ξ).card = ξ.t :=
  (t_xi (matchOf ξ) (alphaOf ξ) (betaOf ξ)).symm.trans (congrArg Config.t (xi_matchOf))

noncomputable def topCoeffCfg (F : Type*) [Field F] (ξ : Config 2 2) : F :=
  topCoeff F (alphaOf ξ) (betaOf ξ)

noncomputable def psiCfg (q : Config 2 2 → F) (πA πB : Fin 2 → F) (ξ : Config 2 2) : F :=
  psi q πA πB (matchOf ξ) (alphaOf ξ) (betaOf ξ)

theorem topCoeffCfg_mul_self (ξ : Config 2 2) :
    topCoeffCfg F ξ * topCoeffCfg F ξ = 1 :=
  topCoeff_mul_self _ _

theorem topCoeffCfg_mem (A : Subring F) (ξ : Config 2 2) : topCoeffCfg F ξ ∈ A :=
  topCoeff_mem A _ _

end Cfg

section Config

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA πB : Fin 2 → F} {q : Config 2 2 → F}

theorem q_eq_topCoeffCfg_mul_Phi_add_psiCfg (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hq : IsSolution θA θB ρ πA πB q) (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1)
    (ξ : Config 2 2) :
    q ξ = topCoeffCfg F ξ * Phi q πA πB ξ.nA ξ.nB ξ.t + psiCfg q πA πB ξ := by
  have h := q_xi_eq_topCoeff_mul_Phi_add_psi hθA hθB hρ hq hπA hπB (matchOf ξ) isMatching_matchOf
    (alphaOf ξ) (betaOf ξ)
  rwa [xi_matchOf, card_SlotA, card_SlotB, card_matchOf] at h

theorem Dcut_mul_psiCfg_mem (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hq : IsSolution θA θB ρ πA πB q) (A : Subring F)
    (haA : θA ∈ A) (haB : θB ∈ A) (haρ : ρ ∈ A)
    (hπAm : ∀ i, πA i ∈ A) (hπBm : ∀ j, πB j ∈ A)
    (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1)
    (ξ : Config 2 2) (hiA : 2 ≤ ξ.nA) :
    Dcut θA θB ρ ξ.nA ξ.nB * psiCfg q πA πB ξ ∈ A := by
  have h := Dcut_mul_psi_mem hθA hθB hρ hq A haA haB haρ hπAm hπBm hπA hπB
    (matchOf ξ) (alphaOf ξ) (betaOf ξ) (by rw [card_SlotA]; exact hiA)
  rwa [card_SlotA, card_SlotB] at h

theorem dvdIn_E_of_clears (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hq : IsSolution θA θB ρ πA πB q) (A : Subring F)
    (haA : θA ∈ A) (haB : θB ∈ A) (haρ : ρ ∈ A)
    (hπAm : ∀ i, πA i ∈ A) (hπBm : ∀ j, πB j ∈ A)
    (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1)
    (ξ : Config 2 2) (hiA : 2 ≤ ξ.nA) (hiB : 2 ≤ ξ.nB)
    (hH : Algebra.Denominator.IsRedDenom A (Phi q πA πB ξ.nA ξ.nB ξ.t) (Dfull θA θB ρ ξ.nA ξ.nB))
    {d : F} (hd : Algebra.Denominator.Clears A (q ξ) d) :
    Algebra.Denominator.DvdIn A (LinearAlgebra.Tridiag.E F ξ.nA ξ.nB θA θB ρ) d :=
  Algebra.Denominator.dvdIn_of_split_clears
      (q_eq_topCoeffCfg_mul_Phi_add_psiCfg hθA hθB hρ hq hπA hπB ξ)
    (topCoeffCfg_mul_self ξ) (topCoeffCfg_mem A ξ)
    ⟨Dcut_mem A haA haB haρ _ _,
      Dcut_mul_psiCfg_mem hθA hθB hρ hq A haA haB haρ hπAm hπBm hπA hπB ξ hiA⟩
    (Dcut_pos hθA hθB hρ hiA _).ne' (Dcut_mul_E θA θB ρ hiA hiB).symm hH hd

theorem dvdIn_E_of_isRedDenom (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hq : IsSolution θA θB ρ πA πB q) (A : Subring F)
    (haA : θA ∈ A) (haB : θB ∈ A) (haρ : ρ ∈ A)
    (hπAm : ∀ i, πA i ∈ A) (hπBm : ∀ j, πB j ∈ A)
    (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1)
    (ξ : Config 2 2) (hiA : 2 ≤ ξ.nA) (hiB : 2 ≤ ξ.nB)
    (hH : Algebra.Denominator.IsRedDenom A (Phi q πA πB ξ.nA ξ.nB ξ.t) (Dfull θA θB ρ ξ.nA ξ.nB))
    {δ : F} (hδ : Algebra.Denominator.IsRedDenom A (q ξ) δ) :
    Algebra.Denominator.DvdIn A (LinearAlgebra.Tridiag.E F ξ.nA ξ.nB θA θB ρ) δ :=
  (Algebra.Denominator.dvdIn_of_isRedDenom_iff hδ).mp fun _ hd =>
    dvdIn_E_of_clears hθA hθB hρ hq A haA haB haρ hπAm hπBm hπA hπB ξ hiA hiB hH hd

theorem not_dvdIn_Dfull_mul_q_of_not_dvdIn_Dfull_mul_Phi (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hq : IsSolution θA θB ρ πA πB q) (A : Subring F)
    (haA : θA ∈ A) (haB : θB ∈ A) (haρ : ρ ∈ A)
    (hπAm : ∀ i, πA i ∈ A) (hπBm : ∀ j, πB j ∈ A)
    (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1)
    (ξ : Config 2 2) (hiA : 2 ≤ ξ.nA) (hiB : 2 ≤ ξ.nB) {e : F}
    (hEdvd : Algebra.Denominator.DvdIn A e (LinearAlgebra.Tridiag.E F ξ.nA ξ.nB θA θB ρ))
    (hH : ¬ Algebra.Denominator.DvdIn A e (Dfull θA θB ρ ξ.nA ξ.nB * Phi q πA πB ξ.nA ξ.nB ξ.t)) :
    ¬ Algebra.Denominator.DvdIn A e (Dfull θA θB ρ ξ.nA ξ.nB * q ξ) := by
  intro hdvd
  refine hH ?_
  have hid := Algebra.Denominator.num_identity
      (q_eq_topCoeffCfg_mul_Phi_add_psiCfg hθA hθB hρ hq hπA hπB ξ)
    (Dcut_mul_E θA θB ρ hiA hiB).symm
  have h2 : Algebra.Denominator.DvdIn A e (LinearAlgebra.Tridiag.E F ξ.nA ξ.nB θA θB ρ
      * (Dcut θA θB ρ ξ.nA ξ.nB * psiCfg q πA πB ξ)) :=
    hEdvd.mul_right (Dcut_mul_psiCfg_mem hθA hθB hρ hq A haA haB haρ hπAm hπBm hπA hπB ξ hiA)
  have h3 : Algebra.Denominator.DvdIn A e (topCoeffCfg F ξ
      * (Dfull θA θB ρ ξ.nA ξ.nB * Phi q πA πB ξ.nA ξ.nB ξ.t)) := by
    have hrw : topCoeffCfg F ξ * (Dfull θA θB ρ ξ.nA ξ.nB * Phi q πA πB ξ.nA ξ.nB ξ.t)
        = Dfull θA θB ρ ξ.nA ξ.nB * q ξ
          - LinearAlgebra.Tridiag.E F ξ.nA ξ.nB θA θB ρ
            * (Dcut θA θB ρ ξ.nA ξ.nB * psiCfg q πA πB ξ) := by
      rw [hid]
      ring
    rw [hrw]
    exact hdvd.sub h2
  have h4 := h3.mul_left (topCoeffCfg_mem A ξ)
  have hrw2 : topCoeffCfg F ξ * (topCoeffCfg F ξ
      * (Dfull θA θB ρ ξ.nA ξ.nB * Phi q πA πB ξ.nA ξ.nB ξ.t))
      = Dfull θA θB ρ ξ.nA ξ.nB * Phi q πA πB ξ.nA ξ.nB ξ.t := by
    have hcc := topCoeffCfg_mul_self (F := F) ξ
    linear_combination (Dfull θA θB ρ ξ.nA ξ.nB * Phi q πA πB ξ.nA ξ.nB ξ.t) * hcc
  rwa [hrw2] at h4

theorem num_identity_cfg (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hq : IsSolution θA θB ρ πA πB q) (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1)
    {A : Subring F} (ξ : Config 2 2) (hiA : 2 ≤ ξ.nA) (hiB : 2 ≤ ξ.nB)
    (NPhi NPsi Nq EE cc : A)
    (hNPhi : (NPhi : F) = Dfull θA θB ρ ξ.nA ξ.nB * Phi q πA πB ξ.nA ξ.nB ξ.t)
    (hNPsi : (NPsi : F) = Dcut θA θB ρ ξ.nA ξ.nB * psiCfg q πA πB ξ)
    (hNq : (Nq : F) = Dfull θA θB ρ ξ.nA ξ.nB * q ξ)
    (hEE : (EE : F) = LinearAlgebra.Tridiag.E F ξ.nA ξ.nB θA θB ρ)
    (hcc : (cc : F) = topCoeffCfg F ξ) :
    Nq = cc * NPhi + EE * NPsi := by
  apply Subtype.ext
  push_cast
  rw [hNq, hNPhi, hNPsi, hEE, hcc]
  exact Algebra.Denominator.num_identity
      (q_eq_topCoeffCfg_mul_Phi_add_psiCfg hθA hθB hρ hq hπA hπB ξ)
    (Dcut_mul_E θA θB ρ hiA hiB).symm

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem isUnit_topCoeffCfg_coe {A : Subring F} (ξ : Config 2 2) (cc : A)
    (hcc : (cc : F) = topCoeffCfg F ξ) : IsUnit cc := by
  have h : cc * cc = 1 := by
    apply Subtype.ext
    push_cast
    rw [hcc]
    exact topCoeffCfg_mul_self ξ
  exact ⟨⟨cc, cc, h, h⟩, rfl⟩

theorem emultiplicity_Dfull_le_of_clears (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hq : IsSolution θA θB ρ πA πB q) (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1)
    {A : Subring F} (ξ : Config 2 2) (hiA : 2 ≤ ξ.nA) (hiB : 2 ≤ ξ.nB)
    (NPhi NPsi Nq EE cc DD dd Nd : A)
    (hNPhi : (NPhi : F) = Dfull θA θB ρ ξ.nA ξ.nB * Phi q πA πB ξ.nA ξ.nB ξ.t)
    (hNPsi : (NPsi : F) = Dcut θA θB ρ ξ.nA ξ.nB * psiCfg q πA πB ξ)
    (hNq : (Nq : F) = Dfull θA θB ρ ξ.nA ξ.nB * q ξ)
    (hEE : (EE : F) = LinearAlgebra.Tridiag.E F ξ.nA ξ.nB θA θB ρ)
    (hcc : (cc : F) = topCoeffCfg F ξ)
    (hDD : (DD : F) = Dfull θA θB ρ ξ.nA ξ.nB)
    (hNd : (Nd : F) = (dd : F) * q ξ)
    {e : A} (hp : Prime e) (hEdvd : e ∣ EE) (hH : ¬ e ∣ NPhi) :
    emultiplicity e DD ≤ emultiplicity e dd := by
  have hid := num_identity_cfg hθA hθB hρ hq hπA hπB ξ hiA hiB NPhi NPsi Nq EE cc
    hNPhi hNPsi hNq hEE hcc
  have hzero : emultiplicity e Nq = 0 :=
    Algebra.Denominator.emultiplicity_num_eq_zero hp hid (isUnit_topCoeffCfg_coe ξ cc hcc)
      (emultiplicity_eq_zero.2 hH) (emultiplicity_pos_of_dvd hEdvd)
  have hprod : DD * Nd = dd * Nq := by
    apply Subtype.ext
    push_cast
    rw [hDD, hNd, hNq]
    ring
  exact Algebra.Denominator.emultiplicity_le_of_num_eq_zero hp hprod hzero

end Config

end Rhone.Probability.Denominator
