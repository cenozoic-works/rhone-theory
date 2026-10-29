/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.Assembly.Hierarchy

/-! # Scaling of the residue hierarchy `ψ̂` under `π`, and the sign law of the reduced `χ` -/

@[expose] public section

namespace Rhone.Probability.Assembly

open Matrix

variable {R : Type*} [CommRing R]

theorem srcR_scale {lam mu κA γA κB γB : R} {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    {f g : ℕ → ℕ → ℕ → R} {i j : ℕ} (hi1 : 1 ≤ i) (hj1 : 1 ≤ j)
    (hoff : ∀ a b u, ¬(p ≤ a ∧ q ≤ b) → f a b u = 0)
    (hfg : ∀ a b u, a + b < i + j → g a b u = lam ^ (a - p) * mu ^ (b - q) * f a b u)
    (t : ℕ) :
    srcR (lam ^ 2 * κA) (lam * γA) (mu ^ 2 * κB) (mu * γB) g i j t
      = lam ^ (i - p) * mu ^ (j - q) * srcR κA γA κB γB f i j t := by
  have Q20 : ∀ u, lam ^ 2 * (lam ^ (i - 2 - p) * mu ^ (j - q) * f (i - 2) j u)
      = lam ^ (i - p) * mu ^ (j - q) * f (i - 2) j u := by
    intro u
    by_cases h : p + 2 ≤ i
    · have he : lam ^ 2 * lam ^ (i - 2 - p) = lam ^ (i - p) := by
        rw [← pow_add]; congr 1; omega
      linear_combination (mu ^ (j - q) * f (i - 2) j u) * he
    · rw [hoff (i - 2) j u (by omega)]; ring
  have Q10 : ∀ u, lam * (lam ^ (i - 1 - p) * mu ^ (j - q) * f (i - 1) j u)
      = lam ^ (i - p) * mu ^ (j - q) * f (i - 1) j u := by
    intro u
    by_cases h : p + 1 ≤ i
    · have he : lam ^ 1 * lam ^ (i - 1 - p) = lam ^ (i - p) := by
        rw [← pow_add]; congr 1; omega
      have he' : lam * lam ^ (i - 1 - p) = lam ^ (i - p) := by rwa [pow_one] at he
      linear_combination (mu ^ (j - q) * f (i - 1) j u) * he'
    · rw [hoff (i - 1) j u (by omega)]; ring
  have Q02 : ∀ u, mu ^ 2 * (lam ^ (i - p) * mu ^ (j - 2 - q) * f i (j - 2) u)
      = lam ^ (i - p) * mu ^ (j - q) * f i (j - 2) u := by
    intro u
    by_cases h : q + 2 ≤ j
    · have he : mu ^ 2 * mu ^ (j - 2 - q) = mu ^ (j - q) := by
        rw [← pow_add]; congr 1; omega
      linear_combination (lam ^ (i - p) * f i (j - 2) u) * he
    · rw [hoff i (j - 2) u (by omega)]; ring
  have Q01 : ∀ u, mu * (lam ^ (i - p) * mu ^ (j - 1 - q) * f i (j - 1) u)
      = lam ^ (i - p) * mu ^ (j - q) * f i (j - 1) u := by
    intro u
    by_cases h : q + 1 ≤ j
    · have he : mu ^ 1 * mu ^ (j - 1 - q) = mu ^ (j - q) := by
        rw [← pow_add]; congr 1; omega
      have he' : mu * mu ^ (j - 1 - q) = mu ^ (j - q) := by rwa [pow_one] at he
      linear_combination (lam ^ (i - p) * f i (j - 1) u) * he'
    · rw [hoff i (j - 1) u (by omega)]; ring
  have Q22 : ∀ u, lam ^ 2 * mu ^ 2 * (lam ^ (i - 2 - p) * mu ^ (j - 2 - q) * f (i - 2) (j - 2) u)
      = lam ^ (i - p) * mu ^ (j - q) * f (i - 2) (j - 2) u := by
    intro u
    by_cases h : p + 2 ≤ i ∧ q + 2 ≤ j
    · have hl : lam ^ 2 * lam ^ (i - 2 - p) = lam ^ (i - p) := by
        rw [← pow_add]; congr 1; omega
      have hm : mu ^ 2 * mu ^ (j - 2 - q) = mu ^ (j - q) := by
        rw [← pow_add]; congr 1; omega
      calc lam ^ 2 * mu ^ 2 * (lam ^ (i - 2 - p) * mu ^ (j - 2 - q) * f (i - 2) (j - 2) u)
          = (lam ^ 2 * lam ^ (i - 2 - p)) * (mu ^ 2 * mu ^ (j - 2 - q))
              * f (i - 2) (j - 2) u := by ring
        _ = lam ^ (i - p) * mu ^ (j - q) * f (i - 2) (j - 2) u := by rw [hl, hm]
    · rw [hoff (i - 2) (j - 2) u (by omega)]; ring
  have Q21 : ∀ u, lam ^ 2 * mu * (lam ^ (i - 2 - p) * mu ^ (j - 1 - q) * f (i - 2) (j - 1) u)
      = lam ^ (i - p) * mu ^ (j - q) * f (i - 2) (j - 1) u := by
    intro u
    by_cases h : p + 2 ≤ i ∧ q + 1 ≤ j
    · have hl : lam ^ 2 * lam ^ (i - 2 - p) = lam ^ (i - p) := by
        rw [← pow_add]; congr 1; omega
      have hm : mu ^ 1 * mu ^ (j - 1 - q) = mu ^ (j - q) := by
        rw [← pow_add]; congr 1; omega
      have hm' : mu * mu ^ (j - 1 - q) = mu ^ (j - q) := by rwa [pow_one] at hm
      calc lam ^ 2 * mu * (lam ^ (i - 2 - p) * mu ^ (j - 1 - q) * f (i - 2) (j - 1) u)
          = (lam ^ 2 * lam ^ (i - 2 - p)) * (mu * mu ^ (j - 1 - q))
              * f (i - 2) (j - 1) u := by ring
        _ = lam ^ (i - p) * mu ^ (j - q) * f (i - 2) (j - 1) u := by rw [hl, hm']
    · rw [hoff (i - 2) (j - 1) u (by omega)]; ring
  have Q12 : ∀ u, lam * mu ^ 2 * (lam ^ (i - 1 - p) * mu ^ (j - 2 - q) * f (i - 1) (j - 2) u)
      = lam ^ (i - p) * mu ^ (j - q) * f (i - 1) (j - 2) u := by
    intro u
    by_cases h : p + 1 ≤ i ∧ q + 2 ≤ j
    · have hl : lam ^ 1 * lam ^ (i - 1 - p) = lam ^ (i - p) := by
        rw [← pow_add]; congr 1; omega
      have hl' : lam * lam ^ (i - 1 - p) = lam ^ (i - p) := by rwa [pow_one] at hl
      have hm : mu ^ 2 * mu ^ (j - 2 - q) = mu ^ (j - q) := by
        rw [← pow_add]; congr 1; omega
      calc lam * mu ^ 2 * (lam ^ (i - 1 - p) * mu ^ (j - 2 - q) * f (i - 1) (j - 2) u)
          = (lam * lam ^ (i - 1 - p)) * (mu ^ 2 * mu ^ (j - 2 - q))
              * f (i - 1) (j - 2) u := by ring
        _ = lam ^ (i - p) * mu ^ (j - q) * f (i - 1) (j - 2) u := by rw [hl', hm]
    · rw [hoff (i - 1) (j - 2) u (by omega)]; ring
  have Q11 : ∀ u, lam * mu * (lam ^ (i - 1 - p) * mu ^ (j - 1 - q) * f (i - 1) (j - 1) u)
      = lam ^ (i - p) * mu ^ (j - q) * f (i - 1) (j - 1) u := by
    intro u
    by_cases h : p + 1 ≤ i ∧ q + 1 ≤ j
    · have hl : lam ^ 1 * lam ^ (i - 1 - p) = lam ^ (i - p) := by
        rw [← pow_add]; congr 1; omega
      have hl' : lam * lam ^ (i - 1 - p) = lam ^ (i - p) := by rwa [pow_one] at hl
      have hm : mu ^ 1 * mu ^ (j - 1 - q) = mu ^ (j - q) := by
        rw [← pow_add]; congr 1; omega
      have hm' : mu * mu ^ (j - 1 - q) = mu ^ (j - q) := by rwa [pow_one] at hm
      calc lam * mu * (lam ^ (i - 1 - p) * mu ^ (j - 1 - q) * f (i - 1) (j - 1) u)
          = (lam * lam ^ (i - 1 - p)) * (mu * mu ^ (j - 1 - q))
              * f (i - 1) (j - 1) u := by ring
        _ = lam ^ (i - p) * mu ^ (j - q) * f (i - 1) (j - 1) u := by rw [hl', hm']
    · rw [hoff (i - 1) (j - 1) u (by omega)]; ring
  simp only [srcR, hfg (i - 2) j t (by omega), hfg (i - 2) j (t - 1) (by omega),
    hfg (i - 1) j t (by omega), hfg i (j - 2) t (by omega), hfg i (j - 2) (t - 1) (by omega),
    hfg i (j - 1) t (by omega), hfg (i - 2) (j - 2) (t - 2) (by omega),
    hfg (i - 2) (j - 1) (t - 2) (by omega), hfg (i - 1) (j - 2) (t - 2) (by omega),
    hfg (i - 1) (j - 1) (t - 1) (by omega)]
  linear_combination (κA * (((i - t) * (i - t - 1) : ℕ) : R)) * Q20 t
    + (2 * κA * (((i - t) * t : ℕ) : R)) * Q20 (t - 1)
    + (γA * (((i - t) * (i + t - 1) : ℕ) : R)) * Q10 t
    + (κB * (((j - t) * (j - t - 1) : ℕ) : R)) * Q02 t
    + (2 * κB * (((j - t) * t : ℕ) : R)) * Q02 (t - 1)
    + (γB * (((j - t) * (j + t - 1) : ℕ) : R)) * Q01 t
    + (((t * (t - 1) : ℕ) : R) * κA * κB) * Q22 (t - 2)
    + (((t * (t - 1) : ℕ) : R) * κA * γB) * Q21 (t - 2)
    + (((t * (t - 1) : ℕ) : R) * γA * κB) * Q12 (t - 2)
    + (((t * (t - 1) : ℕ) : R) * γA * γB) * Q11 (t - 1)

theorem psi_scale (N : ∀ i j : ℕ, Matrix (Fin (min i j + 1)) (Fin (min i j + 1)) R)
    {κA γA κB γB : R} {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (v : ℕ → R) (lam mu : R)
    (i j t : ℕ) :
    psi N (lam ^ 2 * κA) (lam * γA) (mu ^ 2 * κB) (mu * γB) p q v i j t
      = lam ^ (i - p) * mu ^ (j - q) * psi N κA γA κB γB p q v i j t := by
  have key : ∀ n i j t, i + j = n →
      psi N (lam ^ 2 * κA) (lam * γA) (mu ^ 2 * κB) (mu * γB) p q v i j t
        = lam ^ (i - p) * mu ^ (j - q) * psi N κA γA κB γB p q v i j t := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro i j t hn
      by_cases he : (i, j) = (p, q)
      · have hi : i = p := congrArg Prod.fst he
        have hj : j = q := congrArg Prod.snd he
        subst hi; subst hj
        rw [psi_base, psi_base, Nat.sub_self, Nat.sub_self, pow_zero, pow_zero, one_mul, one_mul]
      · by_cases hu : p ≤ i ∧ q ≤ j
        · by_cases hij : 2 ≤ i ∧ 2 ≤ j
          · by_cases ht : t < min i j + 1
            · rw [psi_val hu.1 hu.2 he hij.1 hij.2 ht, psi_val hu.1 hu.2 he hij.1 hij.2 ht,
                Finset.mul_sum]
              refine Finset.sum_congr rfl fun s _ => ?_
              rw [srcR_scale (by omega) (by omega) (by omega) (by omega)
                (fun a b u h => psi_off h u) (fun a b u hab => ih (a + b) (by omega) a b u rfl)
                (s : ℕ)]
              ring
            · rw [psi_range (by omega), psi_range (by omega), mul_zero]
          · rw [psi_small he hij, psi_small he hij, mul_zero]
        · rw [psi_off hu, psi_off hu, mul_zero]
  exact key (i + j) i j t rfl

theorem chi_sign (N : ∀ i j : ℕ, Matrix (Fin (min i j + 1)) (Fin (min i j + 1)) R) {p q : ℕ}
    (hp : 2 ≤ p) (hq : 2 ≤ q) (v : ℕ → R) (γA γB : R) (i j t : ℕ) :
    psi N 0 γA 0 γB p q v i j t
      = γA ^ (i - p) * γB ^ (j - q) * psi N 0 1 0 1 p q v i j t := by
  have h := psi_scale N (κA := 0) (γA := 1) (κB := 0) (γB := 1) hp hq v γA γB i j t
  simpa using h

end Rhone.Probability.Assembly
