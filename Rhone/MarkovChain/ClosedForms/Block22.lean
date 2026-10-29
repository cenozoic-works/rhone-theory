/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.ClosedForms.Marginal
public import Rhone.LinearAlgebra.Recursion.Unique
public import Rhone.LinearAlgebra.Tridiag.Defs

/-! # Block `(2,2)` in closed form, for arbitrary `K_A, K_B` -/

@[expose] public section

namespace Rhone.MarkovChain.ClosedForms

open Finset Matrix LinearAlgebra.Recursion Config

section Ring

variable {R : Type*} [CommRing R]

def Eblock (θA θB ρ : R) : R :=
  (θA + θB + 2) * ρ ^ 2 + (θA + θB + 2) * (3 * (θA + θB) + 13) * ρ
    + 2 * (θA + θB + 1) * (θA + θB + 3) * (θA + θB + 6)

def wvec (θA θB ρ : R) : Fin 3 → R :=
  ![16, 4 * (θA + θB + 6),
    4 * (θA + θB + 3) * (θA + θB + 6) + 2 * ρ * (θA + θB + 2)]

def T22 (θA θB ρ : R) : Matrix (Fin 3) (Fin 3) R :=
  !![12 + θA * 2 + θB * 2, -8, 0;
     -ρ, 6 + θA * 2 + θB * 2 + ρ, -2;
     0, -(ρ * 2), 2 + θA * 2 + θB * 2 + ρ * 2]

theorem T22_eq_tridiag (θA θB ρ : R) : LinearAlgebra.Tridiag.T R 2 2 θA θB ρ = T22 θA θB ρ :=
  LinearAlgebra.Tridiag.T_two_two_generic θA θB ρ

theorem T22_det (θA θB ρ : R) : (T22 θA θB ρ).det = 4 * Eblock θA θB ρ := by
  rw [T22, Matrix.det_fin_three]
  simp only [Eblock, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.of_apply]
  ring

theorem T22_mulVec_wvec (θA θB ρ : R) :
    T22 θA θB ρ *ᵥ wvec θA θB ρ = ![0, 0, 4 * Eblock θA θB ρ] := by
  funext t
  fin_cases t <;>
    simp [T22, Matrix.mulVec, dotProduct, Fin.sum_univ_three, wvec, Eblock] <;> ring

end Ring

variable {KA KB : ℕ} {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F}

def lev (S : (Fin KA → ℕ) → (Fin KB → ℕ) → F) (f : ℕ → F) (ξ : Config KA KB) : F :=
  if ξ.nA = 2 ∧ ξ.nB = 2 then S ξ.mA ξ.mB * f ξ.t else 0

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem lev_of_not {S : (Fin KA → ℕ) → (Fin KB → ℕ) → F} {f : ℕ → F} {ξ : Config KA KB}
    (h : ¬(ξ.nA = 2 ∧ ξ.nB = 2)) : lev S f ξ = 0 := ite_eq_right h

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem lev_of_block {S : (Fin KA → ℕ) → (Fin KB → ℕ) → F} {f : ℕ → F} {ξ : Config KA KB}
    (hA : ξ.nA = 2) (hB : ξ.nB = 2) : lev S f ξ = S ξ.mA ξ.mB * f ξ.t := ite_eq_left ⟨hA, hB⟩

theorem lumpable (S : (Fin KA → ℕ) → (Fin KB → ℕ) → F) (f : ℕ → F) {ξ : Config KA KB}
    (hA : ξ.nA = 2) (hB : ξ.nB = 2) :
    (∑ i, ∑ j, ((ξ.coalAB i j : ℕ) : F) * lev S f (ξ.mergeAB i j))
        + ρ * ∑ i, ∑ j, ((ξ.c i j : ℕ) : F) * lev S f (ξ.split i j)
      = ((2 * (ξ.sumA * ξ.sumB) : ℕ) : F) * (S ξ.mA ξ.mB * f (ξ.t + 1))
        + ρ * (((ξ.t : ℕ) : F) * (S ξ.mA ξ.mB * f (ξ.t - 1))) := by
  have h1 : ∀ (i : Fin KA) (j : Fin KB),
      ((ξ.coalAB i j : ℕ) : F) * lev S f (ξ.mergeAB i j)
        = ((ξ.coalAB i j : ℕ) : F) * (S ξ.mA ξ.mB * f (ξ.t + 1)) := by
    intro i j
    by_cases ha : ξ.a i = 0
    · rw [ξ.coalAB_eq_zero_left j ha]; simp
    by_cases hb : ξ.b j = 0
    · rw [ξ.coalAB_eq_zero_right i hb]; simp
    obtain ⟨e1, e2⟩ := ξ.mergeAB_same ha hb
    rw [lev_of_block (by rw [e1, hA]) (by rw [e2, hB]), Config.mA_mergeAB ξ j ha,
      Config.mB_mergeAB ξ i hb, t_mergeAB]
  have h2 : ∀ (i : Fin KA) (j : Fin KB),
      ((ξ.c i j : ℕ) : F) * lev S f (ξ.split i j)
        = ((ξ.c i j : ℕ) : F) * (S ξ.mA ξ.mB * f (ξ.t - 1)) := by
    intro i j
    by_cases hc : ξ.c i j = 0
    · rw [hc]; simp
    obtain ⟨e1, e2⟩ := ξ.split_same hc
    have ht : (ξ.split i j).t = ξ.t - 1 := by have := ξ.t_split i j hc; omega
    rw [lev_of_block (by rw [e1, hA]) (by rw [e2, hB]), Config.mA_split ξ hc,
      Config.mB_split ξ hc, ht]
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
      Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => h1 i j,
    Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
      Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => h2 i j]
  congr 1
  · rw [← ξ.sum_coalAB]
    push_cast
    simp [Finset.sum_mul]
  · congr 1
    rw [← ξ.sum_c]
    push_cast
    simp [Finset.sum_mul]

def wn (θA θB ρ : F) : ℕ → F
  | 0 => 16
  | 1 => 4 * (θA + θB + 6)
  | 2 => 4 * (θA + θB + 3) * (θA + θB + 6) + 2 * ρ * (θA + θB + 2)
  | _ + 3 => 0

def gf (θA θB ρ : F) (t : ℕ) : F := wn θA θB ρ t / (2 * Eblock θA θB ρ)

theorem Eblock_pos (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) : 0 < Eblock θA θB ρ := by
  have h1 : (0 : F) < θA + θB + 2 := by linarith
  have a1 : (0 : F) < 2 * (θA + θB + 1) := by linarith
  have a2 : (0 : F) < θA + θB + 3 := by linarith
  have a3 : (0 : F) < θA + θB + 6 := by linarith
  have h3 : (0 : F) < 3 * (θA + θB) + 13 := by linarith
  have h4 : (0 : F) < 2 * (θA + θB + 1) * (θA + θB + 3) * (θA + θB + 6) :=
    mul_pos (mul_pos a1 a2) a3
  have h5 : (0 : F) ≤ (θA + θB + 2) * ρ ^ 2 := mul_nonneg h1.le (sq_nonneg ρ)
  have h6 : (0 : F) ≤ (θA + θB + 2) * (3 * (θA + θB) + 13) * ρ :=
    mul_nonneg (mul_nonneg h1.le h3.le) hρ
  simp only [Eblock]
  linarith

theorem gf_row (hE : Eblock θA θB ρ ≠ 0) {t : ℕ} (ht : t ≤ 2) :
    ((((4 - t) * (3 - t) : ℕ) : F) + θA * 2 + θB * 2 + ρ * (t : ℕ)) * gf θA θB ρ t
      = ((2 * (2 - t) * (2 - t) : ℕ) : F) * gf θA θB ρ (t + 1)
        + ρ * ((t : ℕ) : F) * gf θA θB ρ (t - 1) + (if t = 2 then 2 else 0) := by
  interval_cases t
  · norm_num [gf, wn]
    field_simp
    ring
  · norm_num [gf, wn]
    field_simp
    ring
  · norm_num [gf, wn]
    field_simp
    simp only [Eblock]
    ring

theorem block22_closed_form (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    {πA : Fin KA → F} {πB : Fin KB → F} {q qhat : Config KA KB → F}
    (hq : IsSolution θA θB ρ πA πB q) (S : (Fin KA → ℕ) → (Fin KB → ℕ) → F)
    (hthm1 : ∀ η : Config KA KB, η.nA ≤ 2 → η.nB ≤ 2 → ¬(η.nA = 2 ∧ η.nB = 2) → q η = qhat η)
    (hsrc : ∀ ξ : Config KA KB, ξ.nA = 2 → ξ.nB = 2 →
      diag θA θB ρ ξ * qhat ξ
        = rhs θA θB ρ πA πB qhat ξ - 2 * (if ξ.t = 2 then S ξ.mA ξ.mB else 0))
    {ξ : Config KA KB} (hA : ξ.nA = 2) (hB : ξ.nB = 2) :
    q ξ = qhat ξ + S ξ.mA ξ.mB * gf θA θB ρ ξ.t := by
  have hE : Eblock θA θB ρ ≠ 0 := (Eblock_pos hθA hθB hρ).ne'
  set hfun : Config KA KB → F :=
    fun η => if η.nA ≤ 2 ∧ η.nB ≤ 2 then q η - qhat η - lev S (gf θA θB ρ) η else 0 with hfd
  have hval : ∀ η : Config KA KB, η.nA ≤ 2 → η.nB ≤ 2 →
      hfun η = q η - qhat η - lev S (gf θA θB ρ) η := by
    intro η h1 h2
    rw [hfd]
    exact ite_eq_left ⟨h1, h2⟩
  have hout : ∀ η : Config KA KB, ¬(η.nA ≤ 2 ∧ η.nB ≤ 2) → hfun η = 0 := by
    intro η h
    rw [hfd]
    exact ite_eq_right h
  have hzero : ∀ η : Config KA KB, ¬(η.nA = 2 ∧ η.nB = 2) → hfun η = 0 := by
    intro η hne
    by_cases hle : η.nA ≤ 2 ∧ η.nB ≤ 2
    · rw [hval η hle.1 hle.2, lev_of_not hne, hthm1 η hle.1 hle.2 hne]
      ring
    · exact hout η hle
  have key : ∀ η : Config KA KB, η.nA + η.nB ≤ 4 → hfun η = 0 := by
    refine within_block_eq_zero hθA hθB hρ (fun _ => le_rfl) ?_ ?_
    · intro η hn _
      refine hzero η ?_
      rintro ⟨h1, _⟩
      have := η.nA_le_n
      omega
    · intro η hn _ _
      by_cases hblk : η.nA = 2 ∧ η.nB = 2
      · obtain ⟨hηA, hηB⟩ := hblk
        have hvan := rhs_of_vanishing_below θA θB ρ πA πB (h := fun η' => q η' - qhat η')
          η (fun η' h1 h2 h3 => sub_eq_zero_of_eq
            (hthm1 η' (by omega) (by omega) (by omega)))
        rw [rhs_sub] at hvan
        have hlump := lumpable (ρ := ρ) S (gf θA θB ρ) hηA hηB
        have hn4 : η.n = 4 - η.t := by have := η.n_add_t; omega
        have ht2 : η.t ≤ 2 := by have := η.t_le_nA; omega
        have hsA : η.sumA = 2 - η.t := by simp only [nA] at hηA; omega
        have hsB : η.sumB = 2 - η.t := by simp only [nB] at hηB; omega
        have hdiag : diag θA θB ρ η
            = (((4 - η.t) * (3 - η.t) : ℕ) : F) + θA * 2 + θB * 2 + ρ * (η.t : ℕ) := by
          simp only [Rhone.LinearAlgebra.Recursion.diag, hηA, hηB, hn4]
          norm_num
          omega
        have hrowη := gf_row (θA := θA) (θB := θB) (ρ := ρ) hE ht2
        have hlev : diag θA θB ρ η * lev S (gf θA θB ρ) η
            = ((∑ i, ∑ j, ((η.coalAB i j : ℕ) : F) * lev S (gf θA θB ρ) (η.mergeAB i j))
                + ρ * ∑ i, ∑ j, ((η.c i j : ℕ) : F) * lev S (gf θA θB ρ) (η.split i j))
              + 2 * (if η.t = 2 then S η.mA η.mB else 0) := by
          rw [hlump, lev_of_block hηA hηB, hdiag, hsA, hsB]
          have hcast : ((2 * ((2 - η.t) * (2 - η.t)) : ℕ) : F)
              = ((2 * (2 - η.t) * (2 - η.t) : ℕ) : F) := by
            congr 1
            ring
          rw [hcast]
          rcases eq_or_ne η.t 2 with h | h
          · rw [h] at hrowη ⊢
            rw [ite_eq_left rfl] at hrowη ⊢
            linear_combination S η.mA η.mB * hrowη
          · rw [ite_eq_right h] at hrowη ⊢
            linear_combination S η.mA η.mB * hrowη
        have htA : ∀ (i : Fin KA) (j : Fin KB),
            ((η.coalAB i j : ℕ) : F) * hfun (η.mergeAB i j)
              = ((η.coalAB i j : ℕ) : F)
                * (q (η.mergeAB i j) - qhat (η.mergeAB i j)
                  - lev S (gf θA θB ρ) (η.mergeAB i j)) := by
          intro i j
          by_cases ha : η.a i = 0
          · rw [η.coalAB_eq_zero_left j ha]; simp
          by_cases hb : η.b j = 0
          · rw [η.coalAB_eq_zero_right i hb]; simp
          obtain ⟨e1, e2⟩ := η.mergeAB_same ha hb
          rw [hval _ (by omega) (by omega)]
        have htB : ∀ (i : Fin KA) (j : Fin KB),
            ((η.c i j : ℕ) : F) * hfun (η.split i j)
              = ((η.c i j : ℕ) : F)
                * (q (η.split i j) - qhat (η.split i j) - lev S (gf θA θB ρ) (η.split i j)) := by
          intro i j
          by_cases hc : η.c i j = 0
          · rw [hc]; simp
          obtain ⟨e1, e2⟩ := η.split_same hc
          rw [hval _ (by omega) (by omega)]
        rw [hval η (by omega) (by omega),
          Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
            Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => htA i j,
          Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
            Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => htB i j]
        have hexp : ∀ (g : Config KA KB → F),
            (∑ i, ∑ j, ((η.coalAB i j : ℕ) : F) * (g (η.mergeAB i j)))
              + ρ * ∑ i, ∑ j, ((η.c i j : ℕ) : F) * (g (η.split i j))
              = (∑ i, ∑ j, ((η.coalAB i j : ℕ) : F) * g (η.mergeAB i j))
                + ρ * ∑ i, ∑ j, ((η.c i j : ℕ) : F) * g (η.split i j) := fun _ => rfl
        have hsplit3 :
            (∑ i, ∑ j, ((η.coalAB i j : ℕ) : F)
                * (q (η.mergeAB i j) - qhat (η.mergeAB i j)
                  - lev S (gf θA θB ρ) (η.mergeAB i j)))
              + ρ * ∑ i, ∑ j, ((η.c i j : ℕ) : F)
                * (q (η.split i j) - qhat (η.split i j) - lev S (gf θA θB ρ) (η.split i j))
              = ((∑ i, ∑ j, ((η.coalAB i j : ℕ) : F)
                    * (q (η.mergeAB i j) - qhat (η.mergeAB i j)))
                  + ρ * ∑ i, ∑ j, ((η.c i j : ℕ) : F)
                    * (q (η.split i j) - qhat (η.split i j)))
                - ((∑ i, ∑ j, ((η.coalAB i j : ℕ) : F)
                    * lev S (gf θA θB ρ) (η.mergeAB i j))
                  + ρ * ∑ i, ∑ j, ((η.c i j : ℕ) : F)
                    * lev S (gf θA θB ρ) (η.split i j)) := by
          simp only [mul_sub, Finset.sum_sub_distrib, mul_sub]
          ring
        rw [hsplit3, ← hvan]
        have hrq := hq.recursion η hn
        have hsq := hsrc η hηA hηB
        rw [mul_sub, mul_sub, hrq, hsq, hlev]
        ring
      · rw [hzero η hblk]
        have hs1 : (∑ i, ∑ j, ((η.coalAB i j : ℕ) : F) * hfun (η.mergeAB i j)) = 0 := by
          refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
          by_cases ha : η.a i = 0
          · rw [η.coalAB_eq_zero_left j ha]; simp
          by_cases hb : η.b j = 0
          · rw [η.coalAB_eq_zero_right i hb]; simp
          obtain ⟨e1, e2⟩ := η.mergeAB_same ha hb
          rw [hzero _ (by rw [e1, e2]; exact hblk), mul_zero]
        have hs2 : (∑ i, ∑ j, ((η.c i j : ℕ) : F) * hfun (η.split i j)) = 0 := by
          refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
          by_cases hc : η.c i j = 0
          · rw [hc]; simp
          obtain ⟨e1, e2⟩ := η.split_same hc
          rw [hzero _ (by rw [e1, e2]; exact hblk), mul_zero]
        rw [hs1, hs2, mul_zero, mul_zero, add_zero]
  have hfin := key ξ (by omega)
  rw [hval ξ (by omega) (by omega), lev_of_block hA hB] at hfin
  linarith [hfin]

end Rhone.MarkovChain.ClosedForms
