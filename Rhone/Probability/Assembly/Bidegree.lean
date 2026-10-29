/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.Assembly.Hierarchy
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-! # `ψ̂^{i,j}_t` is `π`-bihomogeneous of bidegree `(i−p, j−q)` -/

@[expose] public section

namespace Rhone.Probability.Assembly

open MvPolynomial

abbrev PiRing (K : Type*) [CommRing K] := MvPolynomial (Fin 4) K

def wt : Fin 4 → ℕ × ℕ := ![(1, 0), (1, 0), (0, 1), (0, 1)]

@[simp] theorem wt_zero : wt 0 = (1, 0) := rfl
@[simp] theorem wt_one : wt 1 = (1, 0) := rfl
@[simp] theorem wt_two : wt 2 = (0, 1) := rfl
@[simp] theorem wt_three : wt 3 = (0, 1) := rfl

section Coords

variable {R : Type*} [CommRing R]

def kapR (π : Fin 2 → R) : R := π 0 * π 1

def gamR (π : Fin 2 → R) : R := π 1 - π 0

def epsR (R : Type*) [CommRing R] : Fin 2 → R := ![1, -1]

@[simp] theorem epsR_zero : epsR R 0 = 1 := rfl
@[simp] theorem epsR_one : epsR R 1 = -1 := rfl

theorem kapR_eq_kap {F : Type*} [Field F] (π : Fin 2 → F) :
    kapR π = Rhone.Probability.Multilinear.kap π := rfl

theorem gamR_eq_gam {F : Type*} [Field F] (π : Fin 2 → F) :
    gamR π = Rhone.Probability.Multilinear.gam π := rfl

end Coords

section Homog

variable {K : Type*} [CommRing K]

noncomputable def piAX (K : Type*) [CommRing K] : Fin 2 → PiRing K := ![X 0, X 1]

noncomputable def piBX (K : Type*) [CommRing K] : Fin 2 → PiRing K := ![X 2, X 3]

@[simp] theorem piAX_zero : piAX K 0 = X 0 := rfl
@[simp] theorem piAX_one : piAX K 1 = X 1 := rfl
@[simp] theorem piBX_zero : piBX K 0 = X 2 := rfl
@[simp] theorem piBX_one : piBX K 1 = X 3 := rfl

theorem natCast_homog (n : ℕ) : IsWeightedHomogeneous wt ((n : PiRing K)) 0 := by
  rw [← map_natCast (C : K →+* PiRing K) n]
  exact isWeightedHomogeneous_C _ _

theorem two_homog : IsWeightedHomogeneous wt ((2 : PiRing K)) 0 := by
  simpa using natCast_homog (K := K) 2

theorem homog_cmul {n x : PiRing K} {d : ℕ × ℕ} (hn : IsWeightedHomogeneous wt n 0)
    (hx : IsWeightedHomogeneous wt x d) : IsWeightedHomogeneous wt (n * x) d := by
  have h := hn.mul hx
  rwa [zero_add] at h

theorem homog_mul {a x : PiRing K} {da dx d : ℕ × ℕ} (ha : IsWeightedHomogeneous wt a da)
    (hx : IsWeightedHomogeneous wt x dx) (h : da + dx = d) :
    IsWeightedHomogeneous wt (a * x) d := h ▸ ha.mul hx

theorem kapA_homog : IsWeightedHomogeneous wt (kapR (piAX K)) (2, 0) := by
  rw [kapR, piAX_zero, piAX_one]
  exact homog_mul (isWeightedHomogeneous_X K wt 0) (isWeightedHomogeneous_X K wt 1) rfl

theorem gamA_homog : IsWeightedHomogeneous wt (gamR (piAX K)) (1, 0) := by
  rw [gamR, piAX_zero, piAX_one]
  exact IsWeightedHomogeneous.sub (isWeightedHomogeneous_X K wt 1) (isWeightedHomogeneous_X K wt 0)

theorem kapB_homog : IsWeightedHomogeneous wt (kapR (piBX K)) (0, 2) := by
  rw [kapR, piBX_zero, piBX_one]
  exact homog_mul (isWeightedHomogeneous_X K wt 2) (isWeightedHomogeneous_X K wt 3) rfl

theorem gamB_homog : IsWeightedHomogeneous wt (gamR (piBX K)) (0, 1) := by
  rw [gamR, piBX_zero, piBX_one]
  exact IsWeightedHomogeneous.sub (isWeightedHomogeneous_X K wt 3) (isWeightedHomogeneous_X K wt 2)

theorem srcR_homog {κA γA κB γB : PiRing K} {dκA dγA dκB dγB : ℕ × ℕ}
    (hκA : IsWeightedHomogeneous wt κA dκA) (hγA : IsWeightedHomogeneous wt γA dγA)
    (hκB : IsWeightedHomogeneous wt κB dκB) (hγB : IsWeightedHomogeneous wt γB dγB)
    {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) {D : ℕ → ℕ → ℕ × ℕ} {f : ℕ → ℕ → ℕ → PiRing K}
    {i j : ℕ} (hi1 : 1 ≤ i) (hj1 : 1 ≤ j)
    (hoff : ∀ a b u, ¬(p ≤ a ∧ q ≤ b) → f a b u = 0)
    (hf : ∀ a b u, a + b < i + j → IsWeightedHomogeneous wt (f a b u) (D a b))
    (e20 : p + 2 ≤ i → dκA + D (i - 2) j = D i j)
    (e10 : p + 1 ≤ i → dγA + D (i - 1) j = D i j)
    (e02 : q + 2 ≤ j → dκB + D i (j - 2) = D i j)
    (e01 : q + 1 ≤ j → dγB + D i (j - 1) = D i j)
    (e22 : p + 2 ≤ i → q + 2 ≤ j → dκA + dκB + D (i - 2) (j - 2) = D i j)
    (e21 : p + 2 ≤ i → q + 1 ≤ j → dκA + dγB + D (i - 2) (j - 1) = D i j)
    (e12 : p + 1 ≤ i → q + 2 ≤ j → dγA + dκB + D (i - 1) (j - 2) = D i j)
    (e11 : p + 1 ≤ i → q + 1 ≤ j → dγA + dγB + D (i - 1) (j - 1) = D i j)
    (t : ℕ) : IsWeightedHomogeneous wt (srcR κA γA κB γB f i j t) (D i j) := by
  have hT1 : IsWeightedHomogeneous wt
      (κA * ((((i - t) * (i - t - 1) : ℕ) : PiRing K) * f (i - 2) j t
        + 2 * (((i - t) * t : ℕ) : PiRing K) * f (i - 2) j (t - 1))) (D i j) := by
    by_cases h : p + 2 ≤ i
    · refine homog_mul hκA (IsWeightedHomogeneous.add ?_ ?_) (e20 h)
      · exact homog_cmul (natCast_homog _) (hf _ _ _ (by omega))
      · exact homog_cmul (homog_cmul two_homog (natCast_homog _)) (hf _ _ _ (by omega))
    · rw [hoff (i - 2) j t (by omega), hoff (i - 2) j (t - 1) (by omega)]
      simpa using isWeightedHomogeneous_zero K wt (D i j)
  have hT2 : IsWeightedHomogeneous wt
      (γA * (((i - t) * (i + t - 1) : ℕ) : PiRing K) * f (i - 1) j t) (D i j) := by
    by_cases h : p + 1 ≤ i
    · refine homog_mul ?_ (hf _ _ _ (by omega)) (e10 h)
      exact homog_mul hγA (natCast_homog _) (by simp)
    · rw [hoff (i - 1) j t (by omega)]
      simpa using isWeightedHomogeneous_zero K wt (D i j)
  have hT3 : IsWeightedHomogeneous wt
      (κB * ((((j - t) * (j - t - 1) : ℕ) : PiRing K) * f i (j - 2) t
        + 2 * (((j - t) * t : ℕ) : PiRing K) * f i (j - 2) (t - 1))) (D i j) := by
    by_cases h : q + 2 ≤ j
    · refine homog_mul hκB (IsWeightedHomogeneous.add ?_ ?_) (e02 h)
      · exact homog_cmul (natCast_homog _) (hf _ _ _ (by omega))
      · exact homog_cmul (homog_cmul two_homog (natCast_homog _)) (hf _ _ _ (by omega))
    · rw [hoff i (j - 2) t (by omega), hoff i (j - 2) (t - 1) (by omega)]
      simpa using isWeightedHomogeneous_zero K wt (D i j)
  have hT4 : IsWeightedHomogeneous wt
      (γB * (((j - t) * (j + t - 1) : ℕ) : PiRing K) * f i (j - 1) t) (D i j) := by
    by_cases h : q + 1 ≤ j
    · refine homog_mul ?_ (hf _ _ _ (by omega)) (e01 h)
      exact homog_mul hγB (natCast_homog _) (by simp)
    · rw [hoff i (j - 1) t (by omega)]
      simpa using isWeightedHomogeneous_zero K wt (D i j)
  have hT5 : IsWeightedHomogeneous wt
      (((t * (t - 1) : ℕ) : PiRing K) * (κA * κB * f (i - 2) (j - 2) (t - 2)
        + κA * γB * f (i - 2) (j - 1) (t - 2)
        + γA * κB * f (i - 1) (j - 2) (t - 2)
        + γA * γB * f (i - 1) (j - 1) (t - 1))) (D i j) := by
    refine homog_cmul (natCast_homog _) (IsWeightedHomogeneous.add
      (IsWeightedHomogeneous.add (IsWeightedHomogeneous.add ?_ ?_) ?_) ?_)
    · by_cases h : p + 2 ≤ i ∧ q + 2 ≤ j
      · exact homog_mul (hκA.mul hκB) (hf _ _ _ (by omega)) (e22 h.1 h.2)
      · rw [hoff (i - 2) (j - 2) (t - 2) (by omega)]
        simpa using isWeightedHomogeneous_zero K wt (D i j)
    · by_cases h : p + 2 ≤ i ∧ q + 1 ≤ j
      · exact homog_mul (hκA.mul hγB) (hf _ _ _ (by omega)) (e21 h.1 h.2)
      · rw [hoff (i - 2) (j - 1) (t - 2) (by omega)]
        simpa using isWeightedHomogeneous_zero K wt (D i j)
    · by_cases h : p + 1 ≤ i ∧ q + 2 ≤ j
      · exact homog_mul (hγA.mul hκB) (hf _ _ _ (by omega)) (e12 h.1 h.2)
      · rw [hoff (i - 1) (j - 2) (t - 2) (by omega)]
        simpa using isWeightedHomogeneous_zero K wt (D i j)
    · by_cases h : p + 1 ≤ i ∧ q + 1 ≤ j
      · exact homog_mul (hγA.mul hγB) (hf _ _ _ (by omega)) (e11 h.1 h.2)
      · rw [hoff (i - 1) (j - 1) (t - 1) (by omega)]
        simpa using isWeightedHomogeneous_zero K wt (D i j)
  exact (((hT1.add hT2).add hT3).add hT4).add hT5

theorem psi_homog {N : ∀ i j : ℕ, Matrix (Fin (min i j + 1)) (Fin (min i j + 1)) (PiRing K)}
    {κA γA κB γB : PiRing K} {p q : ℕ} {v : ℕ → PiRing K}
    (hN : ∀ i j s u, IsWeightedHomogeneous wt (N i j s u) 0)
    (hv : ∀ u, IsWeightedHomogeneous wt (v u) 0)
    (hκA : IsWeightedHomogeneous wt κA (2, 0)) (hγA : IsWeightedHomogeneous wt γA (1, 0))
    (hκB : IsWeightedHomogeneous wt κB (0, 2)) (hγB : IsWeightedHomogeneous wt γB (0, 1))
    (hp : 2 ≤ p) (hq : 2 ≤ q) (i j t : ℕ) :
    IsWeightedHomogeneous wt (psi N κA γA κB γB p q v i j t) (i - p, j - q) := by
  have key : ∀ n i j t, i + j = n →
      IsWeightedHomogeneous wt (psi N κA γA κB γB p q v i j t) (i - p, j - q) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro i j t hn
      by_cases he : (i, j) = (p, q)
      · have hi : i = p := congrArg Prod.fst he
        have hj : j = q := congrArg Prod.snd he
        subst hi; subst hj
        have hz : ((i - i : ℕ), (j - j : ℕ)) = (0 : ℕ × ℕ) := by simp
        rw [psi_base, hz]
        split_ifs with h
        · exact hv t
        · exact isWeightedHomogeneous_zero K wt 0
      · by_cases hu : p ≤ i ∧ q ≤ j
        · by_cases hij : 2 ≤ i ∧ 2 ≤ j
          · by_cases ht : t < min i j + 1
            · rw [psi_val hu.1 hu.2 he hij.1 hij.2 ht]
              refine IsWeightedHomogeneous.sum _ _ _ fun s _ => ?_
              refine homog_cmul (hN i j _ s) ?_
              refine srcR_homog (D := fun a b => (a - p, b - q)) hκA hγA hκB hγB (by omega)
                (by omega) (by omega) (by omega) (fun a b u h => psi_off h u)
                (fun a b u hab => ih (a + b) (by omega) a b u rfl)
                ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (s : ℕ)
              · intro h; simp only [Prod.mk_add_mk, Prod.mk.injEq]; omega
              · intro h; simp only [Prod.mk_add_mk, Prod.mk.injEq]; omega
              · intro h; simp only [Prod.mk_add_mk, Prod.mk.injEq]; omega
              · intro h; simp only [Prod.mk_add_mk, Prod.mk.injEq]; omega
              · intro h h'; simp only [Prod.mk_add_mk, Prod.mk.injEq]; omega
              · intro h h'; simp only [Prod.mk_add_mk, Prod.mk.injEq]; omega
              · intro h h'; simp only [Prod.mk_add_mk, Prod.mk.injEq]; omega
              · intro h h'; simp only [Prod.mk_add_mk, Prod.mk.injEq]; omega
            · rw [psi_range (by omega)]
              exact isWeightedHomogeneous_zero K wt _
          · rw [psi_small he hij]
            exact isWeightedHomogeneous_zero K wt _
        · rw [psi_off hu]
          exact isWeightedHomogeneous_zero K wt _
  exact key (i + j) i j t rfl

end Homog

end Rhone.Probability.Assembly
