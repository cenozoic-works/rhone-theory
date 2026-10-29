/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.Propagation.Propagate

/-! # The residue hierarchy `ψ̂` over a commutative ring -/

@[expose] public section

namespace Rhone.Probability.Assembly

open Matrix LinearAlgebra.Tridiag

variable {R : Type*} [CommRing R]

def srcR (κA γA κB γB : R) (f : ℕ → ℕ → ℕ → R) (i j t : ℕ) : R :=
  κA * ((((i - t) * (i - t - 1) : ℕ) : R) * f (i - 2) j t
      + 2 * (((i - t) * t : ℕ) : R) * f (i - 2) j (t - 1))
    + γA * (((i - t) * (i + t - 1) : ℕ) : R) * f (i - 1) j t
    + κB * ((((j - t) * (j - t - 1) : ℕ) : R) * f i (j - 2) t
      + 2 * (((j - t) * t : ℕ) : R) * f i (j - 2) (t - 1))
    + γB * (((j - t) * (j + t - 1) : ℕ) : R) * f i (j - 1) t
    + ((t * (t - 1) : ℕ) : R) * (κA * κB * f (i - 2) (j - 2) (t - 2)
      + κA * γB * f (i - 2) (j - 1) (t - 2)
      + γA * κB * f (i - 1) (j - 2) (t - 2)
      + γA * γB * f (i - 1) (j - 1) (t - 1))

def srcRVal (κA γA κB γB : R) (g20 g10 g02 g01 g22 g21 g12 g11 : ℕ → R) (i j t : ℕ) : R :=
  κA * ((((i - t) * (i - t - 1) : ℕ) : R) * g20 t
      + 2 * (((i - t) * t : ℕ) : R) * g20 (t - 1))
    + γA * (((i - t) * (i + t - 1) : ℕ) : R) * g10 t
    + κB * ((((j - t) * (j - t - 1) : ℕ) : R) * g02 t
      + 2 * (((j - t) * t : ℕ) : R) * g02 (t - 1))
    + γB * (((j - t) * (j + t - 1) : ℕ) : R) * g01 t
    + ((t * (t - 1) : ℕ) : R) * (κA * κB * g22 (t - 2)
      + κA * γB * g21 (t - 2)
      + γA * κB * g12 (t - 2)
      + γA * γB * g11 (t - 1))

theorem srcR_eq_srcRVal (κA γA κB γB : R) (f : ℕ → ℕ → ℕ → R) (i j t : ℕ) :
    srcR κA γA κB γB f i j t
      = srcRVal κA γA κB γB (fun u => f (i - 2) j u) (fun u => f (i - 1) j u)
          (fun u => f i (j - 2) u) (fun u => f i (j - 1) u) (fun u => f (i - 2) (j - 2) u)
          (fun u => f (i - 2) (j - 1) u) (fun u => f (i - 1) (j - 2) u)
          (fun u => f (i - 1) (j - 1) u) i j t := rfl

theorem srcR_eq_src {K : Type*} [Field K] (κA γA κB γB : K) (f : ℕ → ℕ → ℕ → K) (i j t : ℕ) :
    srcR κA γA κB γB f i j t = Rhone.Probability.Propagation.src κA γA κB γB f i j t := rfl

theorem srcRVal_eq_srcVal {K : Type*} [Field K] (κA γA κB γB : K) (g20 g10 g02 g01 g22 g21 g12
    g11 : ℕ → K) (i j t : ℕ) :
    srcRVal κA γA κB γB g20 g10 g02 g01 g22 g21 g12 g11 i j t
      = Rhone.Probability.Propagation.srcVal κA γA κB γB g20 g10 g02 g01 g22 g21 g12 g11 i j t :=
          rfl

theorem srcR_congr (κA γA κB γB : R) {f g : ℕ → ℕ → ℕ → R} {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j)
    (h : ∀ a b u, a + b < i + j → f a b u = g a b u) (t : ℕ) :
    srcR κA γA κB γB f i j t = srcR κA γA κB γB g i j t := by
  simp only [srcR, h (i - 2) j t (by omega), h (i - 2) j (t - 1) (by omega),
    h (i - 1) j t (by omega), h i (j - 2) t (by omega), h i (j - 2) (t - 1) (by omega),
    h i (j - 1) t (by omega), h (i - 2) (j - 2) (t - 2) (by omega),
    h (i - 2) (j - 1) (t - 2) (by omega), h (i - 1) (j - 2) (t - 2) (by omega),
    h (i - 1) (j - 1) (t - 1) (by omega)]

theorem srcR_map {S : Type*} [CommRing S] (f : R →+* S) (κA γA κB γB : R) (g : ℕ → ℕ → ℕ → R)
    (i j t : ℕ) :
    f (srcR κA γA κB γB g i j t)
      = srcR (f κA) (f γA) (f κB) (f γB) (fun a b u => f (g a b u)) i j t := by
  simp only [srcR, map_add, map_mul, map_natCast, map_ofNat]

noncomputable def psi (N : ∀ i j : ℕ, Matrix (Fin (min i j + 1)) (Fin (min i j + 1)) R)
    (κA γA κB γB : R) (p q : ℕ) (v : ℕ → R) (i j t : ℕ) : R :=
  if (i, j) = (p, q) then (if t ≤ min p q then v t else 0)
  else if p ≤ i ∧ q ≤ j then
    if hi : 2 ≤ i then
      if hj : 2 ≤ j then
        if ht : t < min i j + 1 then
          (N i j *ᵥ fun s : Fin (min i j + 1) =>
              srcRVal κA γA κB γB
                (fun u => psi N κA γA κB γB p q v (i - 2) j u)
                (fun u => psi N κA γA κB γB p q v (i - 1) j u)
                (fun u => psi N κA γA κB γB p q v i (j - 2) u)
                (fun u => psi N κA γA κB γB p q v i (j - 1) u)
                (fun u => psi N κA γA κB γB p q v (i - 2) (j - 2) u)
                (fun u => psi N κA γA κB γB p q v (i - 2) (j - 1) u)
                (fun u => psi N κA γA κB γB p q v (i - 1) (j - 2) u)
                (fun u => psi N κA γA κB γB p q v (i - 1) (j - 1) u)
                i j (s : ℕ)) ⟨t, ht⟩
        else 0
      else 0
    else 0
  else 0
termination_by i + j
decreasing_by all_goals omega

variable {N : ∀ i j : ℕ, Matrix (Fin (min i j + 1)) (Fin (min i j + 1)) R}
variable {κA γA κB γB : R} {p q : ℕ} {v : ℕ → R}

theorem psi_base (t : ℕ) :
    psi N κA γA κB γB p q v p q t = if t ≤ min p q then v t else 0 := by
  rw [psi, ite_eq_left rfl]

theorem psi_base_le {t : ℕ} (ht : t ≤ min p q) : psi N κA γA κB γB p q v p q t = v t := by
  rw [psi_base, ite_eq_left ht]

theorem psi_off {i j : ℕ} (h : ¬(p ≤ i ∧ q ≤ j)) (t : ℕ) :
    psi N κA γA κB γB p q v i j t = 0 := by
  rw [psi, ite_eq_right, ite_eq_right h]
  intro he
  exact h ⟨le_of_eq (congrArg Prod.fst he).symm, le_of_eq (congrArg Prod.snd he).symm⟩

theorem psi_range {i j t : ℕ} (h : min i j < t) : psi N κA γA κB γB p q v i j t = 0 := by
  rw [psi]
  by_cases he : (i, j) = (p, q)
  · have hi : i = p := congrArg Prod.fst he
    have hj : j = q := congrArg Prod.snd he
    subst hi; subst hj
    rw [ite_eq_left rfl, ite_eq_right (by omega)]
  · rw [ite_eq_right he]
    by_cases hu : p ≤ i ∧ q ≤ j
    · rw [ite_eq_left hu]
      by_cases hi : 2 ≤ i
      · rw [dite_eq_left hi]
        by_cases hj : 2 ≤ j
        · rw [dite_eq_left hj, dite_eq_right (by omega)]
        · rw [dite_eq_right hj]
      · rw [dite_eq_right hi]
    · rw [ite_eq_right hu]

theorem psi_small {i j t : ℕ} (hne : (i, j) ≠ (p, q)) (h : ¬(2 ≤ i ∧ 2 ≤ j)) :
    psi N κA γA κB γB p q v i j t = 0 := by
  rw [psi, ite_eq_right hne]
  by_cases hu : p ≤ i ∧ q ≤ j
  · rw [ite_eq_left hu]
    by_cases hi : 2 ≤ i
    · rw [dite_eq_left hi, dite_eq_right (by tauto)]
    · rw [dite_eq_right hi]
  · rw [ite_eq_right hu]

theorem psi_val {i j t : ℕ} (hpi : p ≤ i) (hqj : q ≤ j) (hne : (i, j) ≠ (p, q)) (hi : 2 ≤ i)
    (hj : 2 ≤ j) (ht : t < min i j + 1) :
    psi N κA γA κB γB p q v i j t
      = ∑ s : Fin (min i j + 1),
          N i j ⟨t, ht⟩ s * srcR κA γA κB γB (psi N κA γA κB γB p q v) i j (s : ℕ) := by
  rw [psi, ite_eq_right hne, ite_eq_left ⟨hpi, hqj⟩, dite_eq_left hi, dite_eq_left hj, dite_eq_left
      ht]
  rfl

theorem psi_eq_w {K : Type*} [Field K] (θA θB ρ κA γA κB γB : K) (p q : ℕ) (v : ℕ → K)
    (i j t : ℕ) :
    psi (fun i j => (T K i j θA θB ρ)⁻¹) κA γA κB γB p q v i j t
      = Rhone.Probability.Propagation.w θA θB ρ κA γA κB γB p q v i j t := by
  have key : ∀ n i j t, i + j = n →
      psi (fun i j => (T K i j θA θB ρ)⁻¹) κA γA κB γB p q v i j t
        = Rhone.Probability.Propagation.w θA θB ρ κA γA κB γB p q v i j t := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro i j t hn
      rw [psi, Rhone.Probability.Propagation.w]
      by_cases he : (i, j) = (p, q)
      · rw [ite_eq_left he, ite_eq_left he]
      · rw [ite_eq_right he, ite_eq_right he]
        by_cases hu : p ≤ i ∧ q ≤ j
        · rw [ite_eq_left hu, ite_eq_left hu]
          by_cases hi : 2 ≤ i
          · rw [dite_eq_left hi, dite_eq_left hi]
            by_cases hj : 2 ≤ j
            · rw [dite_eq_left hj, dite_eq_left hj]
              by_cases ht : t < min i j + 1
              · rw [dite_eq_left ht, dite_eq_left ht]
                have e : ∀ a b : ℕ, a + b < i + j →
                    (fun u => psi (fun i j => (T K i j θA θB ρ)⁻¹) κA γA κB γB p q v a b u)
                      = fun u => Rhone.Probability.Propagation.w θA θB ρ κA γA κB γB p q v a b u :=
                  fun a b hab => funext fun u => ih (a + b) (by omega) a b u rfl
                rw [e (i - 2) j (by omega), e (i - 1) j (by omega), e i (j - 2) (by omega),
                  e i (j - 1) (by omega), e (i - 2) (j - 2) (by omega),
                  e (i - 2) (j - 1) (by omega), e (i - 1) (j - 2) (by omega),
                  e (i - 1) (j - 1) (by omega)]
                rfl
              · rw [dite_eq_right ht, dite_eq_right ht]
            · rw [dite_eq_right hj, dite_eq_right hj]
          · rw [dite_eq_right hi, dite_eq_right hi]
        · rw [ite_eq_right hu, ite_eq_right hu]
  exact key (i + j) i j t rfl

theorem psi_map {S : Type*} [CommRing S] (f : R →+* S) (N : ∀ i j : ℕ,
    Matrix (Fin (min i j + 1)) (Fin (min i j + 1)) R) (κA γA κB γB : R) (p q : ℕ) (v : ℕ → R)
    (i j t : ℕ) :
    f (psi N κA γA κB γB p q v i j t)
      = psi (fun i j => (N i j).map f) (f κA) (f γA) (f κB) (f γB) p q (fun u => f (v u))
          i j t := by
  have key : ∀ n i j t, i + j = n →
      f (psi N κA γA κB γB p q v i j t)
        = psi (fun i j => (N i j).map f) (f κA) (f γA) (f κB) (f γB) p q (fun u => f (v u))
            i j t := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro i j t hn
      by_cases he : (i, j) = (p, q)
      · have hi : i = p := congrArg Prod.fst he
        have hj : j = q := congrArg Prod.snd he
        subst hi; subst hj
        rw [psi_base, psi_base]
        split_ifs
        · rfl
        · exact map_zero f
      · by_cases hu : p ≤ i ∧ q ≤ j
        · by_cases hij : 2 ≤ i ∧ 2 ≤ j
          · by_cases ht : t < min i j + 1
            · rw [psi_val hu.1 hu.2 he hij.1 hij.2 ht, psi_val hu.1 hu.2 he hij.1 hij.2 ht,
                map_sum]
              refine Finset.sum_congr rfl fun s _ => ?_
              have hfam : ∀ a b u, a + b < i + j →
                  f (psi N κA γA κB γB p q v a b u)
                    = psi (fun i j => (N i j).map f) (f κA) (f γA) (f κB) (f γB) p q
                        (fun u => f (v u)) a b u :=
                fun a b u hab => ih (a + b) (by omega) a b u rfl
              rw [map_mul, srcR_map, Matrix.map_apply,
                srcR_congr (f κA) (f γA) (f κB) (f γB) (by omega : 1 ≤ i) (by omega : 1 ≤ j)
                  hfam]
            · rw [psi_range (by omega), psi_range (by omega), map_zero]
          · rw [psi_small he hij, psi_small he hij, map_zero]
        · rw [psi_off hu, psi_off hu, map_zero]
  exact key (i + j) i j t rfl

end Rhone.Probability.Assembly
