/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.RareAlleleHierarchy.Reduced
public import Rhone.Analysis.RareAlleleHierarchy.Inert

/-! # `Φ^{i,j}` vanishes at `p = 0` for `i ≥ 1` -/

@[expose] public section

namespace Rhone.Probability.RareAlleleHierarchy

open MvPolynomial Matrix

section Van

variable {K : Type*} [CommRing K]

def Van (v : Fin 2) (f : MvPolynomial (Fin 2) K) : Prop :=
  ∀ m : Fin 2 →₀ ℕ, m v = 0 → f.coeff m = 0

theorem Van.zero (v : Fin 2) : Van (K := K) v 0 := fun _ _ => by simp

theorem Van.add {v : Fin 2} {f g : MvPolynomial (Fin 2) K} (hf : Van v f) (hg : Van v g) :
    Van v (f + g) := fun m hm => by
      rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hf m hm, hg m hm, add_zero]

theorem Van.mul_left {v : Fin 2} {f : MvPolynomial (Fin 2) K} (h : Van v f)
    (g : MvPolynomial (Fin 2) K) : Van v (g * f) := by
  intro m hm
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  have hx' : x.1 + x.2 = m := by simpa using hx
  have : x.2 v = 0 := by
    have := congrArg (fun s : Fin 2 →₀ ℕ => s v) hx'
    simp only [Finsupp.add_apply] at this
    omega
  rw [h x.2 this, mul_zero]

theorem Van.sub {v : Fin 2} {f g : MvPolynomial (Fin 2) K} (hf : Van v f) (hg : Van v g) :
    Van v (f - g) := fun m hm => by rw [coeff_sub, hf m hm, hg m hm, sub_zero]

theorem Van.mul_right {v : Fin 2} {f : MvPolynomial (Fin 2) K} (h : Van v f)
    (g : MvPolynomial (Fin 2) K) : Van v (f * g) := by
  rw [mul_comm]
  exact h.mul_left g

theorem Van_X (v : Fin 2) : Van (K := K) v (X v) := by
  classical
  intro m hm
  rw [coeff_X]
  refine ite_eq_right fun hc => ?_
  have := congrArg (fun s : Fin 2 →₀ ℕ => s v) hc
  simp only [Finsupp.single_eq_same] at this
  omega

theorem Van_kapX : Van (K := K) 0 kapX := by
  rw [kapX, sq]
  exact Van.sub (Van_X 0) ((Van_X 0).mul_left (X 0))

theorem Van_kapY : Van (K := K) 1 kapY := by
  rw [kapY, sq]
  exact Van.sub (Van_X 1) ((Van_X 1).mul_left (X 1))

end Van

section Source

variable {K : Type*} [CommRing K] {Φ : ℕ → ℕ → ℕ → MvPolynomial (Fin 2) K}

theorem van_recursionSource {i j t : ℕ} (hi : 2 ≤ i) (hj : 1 ≤ j)
    (ih : ∀ a b u : ℕ, 1 ≤ a → a + b < i + j → Van 0 (Φ a b u)) :
    Van 0 (recursionSource kapX gamX kapY gamY Φ i j t) := by
  rw [recursionSource]
  refine Van.add (Van.add (Van.add (Van.add ?_ ?_) ?_) ?_) ?_
  · exact Van_kapX.mul_right _
  · exact (ih (i - 1) j t (by omega) (by omega)).mul_left _
  · exact (Van.add ((ih i (j - 2) t (by omega) (by omega)).mul_left _)
      ((ih i (j - 2) (t - 1) (by omega) (by omega)).mul_left _)).mul_left _
  · exact (ih i (j - 1) t (by omega) (by omega)).mul_left _
  · refine Van.mul_left ?_ _
    refine Van.add (Van.add (Van.add ?_ ?_) ?_) ?_
    · exact (Van_kapX.mul_right _).mul_right _
    · exact (Van_kapX.mul_right _).mul_right _
    · exact (ih (i - 1) (j - 2) (t - 2) (by omega) (by omega)).mul_left _
    · exact (ih (i - 1) (j - 1) (t - 1) (by omega) (by omega)).mul_left _

theorem van_recursionSource_zero {i : ℕ} (hi : 2 ≤ i)
    (ih : ∀ a b u : ℕ, 1 ≤ a → a + b < i → Van 0 (Φ a b u)) :
    Van 0 (recursionSource kapX gamX kapY gamY Φ i 0 0) := by
  have hsrc : recursionSource kapX gamX kapY gamY Φ i 0 0
      = kapX * ((((i - 0) * (i - 0 - 1) : ℕ) : MvPolynomial (Fin 2) K) * Φ (i - 2) 0 0
          + 2 * (((i - 0) * 0 : ℕ) : MvPolynomial (Fin 2) K) * Φ (i - 2) 0 (0 - 1))
        + gamX * (((i - 0) * (i + 0 - 1) : ℕ) : MvPolynomial (Fin 2) K) * Φ (i - 1) 0 0 := by
    simp only [recursionSource]
    norm_num
  rw [hsrc]
  exact Van.add (Van_kapX.mul_right _) ((ih (i - 1) 0 0 (by omega) (by omega)).mul_left _)

end Source

section Vanish

variable {K : Type*} [Field K] {θA θB ρ : K} {Φ : ℕ → ℕ → ℕ → MvPolynomial (Fin 2) K}

theorem coeff_two_natCast_mul (m : Fin 2 →₀ ℕ) (n : ℕ) (f : MvPolynomial (Fin 2) K) :
    (2 * ((n : ℕ) : MvPolynomial (Fin 2) K) * f).coeff m = 2 * (n : K) * f.coeff m := by
  have h : (2 : MvPolynomial (Fin 2) K) * ((n : ℕ) : MvPolynomial (Fin 2) K)
      = C (2 * (n : K)) := by
    rw [map_mul, map_ofNat, map_natCast]
  rw [h, coeff_C_mul]

theorem coeff_C_natCast_mul (m : Fin 2 →₀ ℕ) (c : K) (n : ℕ) (f : MvPolynomial (Fin 2) K) :
    (C c * ((n : ℕ) : MvPolynomial (Fin 2) K) * f).coeff m = c * (n : K) * f.coeff m := by
  have h : (C c : MvPolynomial (Fin 2) K) * ((n : ℕ) : MvPolynomial (Fin 2) K)
      = C (c * (n : K)) := by
    rw [map_mul, map_natCast]
  rw [h, coeff_C_mul]

theorem van_of_van_src (hD : IsRecursionSolution θA θB ρ Φ)
    (hE : LinearAlgebra.Tridiag.E K i j θA θB ρ ≠ 0)
    (hrange : ∀ i j t : ℕ, min i j ≤ t → Φ i j t = Φ i j (min i j))
    (hs : ∀ t : ℕ, t ≤ min i j → Van 0 (recursionSource kapX gamX kapY gamY Φ i j t)) (t : ℕ) :
    Van 0 (Φ i j t) := by
  intro m0 hm0
  have hmul : LinearAlgebra.Tridiag.T K i j θA θB ρ
      *ᵥ (fun s : Fin (min i j + 1) => (Φ i j (s : ℕ)).coeff m0) = 0 := by
    funext s
    have hst : (s : ℕ) ≤ min i j := by have := s.isLt; omega
    rw [Rhone.Probability.SlotDeletion.T_mulVec_apply i j θA θB ρ
      (fun u => (Φ i j u).coeff m0) s]
    have hrow := congrArg (fun p => p.coeff m0) (hD i j (s : ℕ) hst)
    rw [coeff_sub, coeff_sub, coeff_C_mul, coeff_two_natCast_mul, coeff_C_natCast_mul,
      hs (s : ℕ) hst m0 hm0] at hrow
    simp only [Pi.zero_apply]
    rw [← hrow]
  have hzero := LinearAlgebra.Tridiag.eq_zero_of_mulVec_eq_zero i j θA θB ρ hE hmul
  rcases Nat.lt_or_ge t (min i j + 1) with hlt | hge
  · exact congrFun hzero ⟨t, hlt⟩
  · rw [hrange i j t (by omega)]
    exact congrFun hzero ⟨min i j, Nat.lt_succ_self _⟩

theorem vanish_A (hD : IsRecursionSolution θA θB ρ Φ)
    (hE : ∀ i j : ℕ, LinearAlgebra.Tridiag.E K i j θA θB ρ ≠ 0)
    (h1A : ∀ b u : ℕ, Φ 1 b u = 0) (h1B : ∀ a u : ℕ, Φ a 1 u = 0)
    (hrange : ∀ i j t : ℕ, min i j ≤ t → Φ i j t = Φ i j (min i j))
    (i j t : ℕ) (hi : 1 ≤ i) : Van 0 (Φ i j t) := by
  have key : ∀ n i j t : ℕ, i + j ≤ n → 1 ≤ i → Van 0 (Φ i j t) := by
    intro n
    induction n with
    | zero => intro i j t hn hi; omega
    | succ n ih =>
      intro i j t hn hi
      have ihlt : ∀ a b u : ℕ, 1 ≤ a → a + b < i + j → Van 0 (Φ a b u) :=
        fun a b u ha hab => ih a b u (by omega) ha
      rcases Nat.eq_or_lt_of_le hi with hi1 | hi2
      · rw [← hi1, h1A j t]
        exact Van.zero 0
      · rcases Nat.eq_zero_or_pos j with rfl | hj
        · refine van_of_van_src hD (hE i 0) hrange (fun s hs => ?_) t
          have hs0 : s = 0 := by simpa using hs
          subst hs0
          exact van_recursionSource_zero (by omega) (fun a b u ha hab => ih a b u (by omega) ha)
        · rcases Nat.eq_or_lt_of_le hj with hj1 | hj2
          · rw [← hj1, h1B i t]
            exact Van.zero 0
          · exact van_of_van_src hD (hE i j) hrange
              (fun s _ => van_recursionSource (by omega) (by omega) ihlt) t
  exact key (i + j) i j t (le_refl _) hi

end Vanish

section Mirror

variable {K : Type*} [CommRing K]

def swp : Fin 2 → Fin 2 := ⇑(Equiv.swap (0 : Fin 2) 1)

theorem swp_injective : Function.Injective swp := (Equiv.swap (0 : Fin 2) 1).injective

@[simp] theorem swp_zero : swp 0 = 1 := Equiv.swap_apply_left 0 1
@[simp] theorem swp_one : swp 1 = 0 := Equiv.swap_apply_right 0 1

@[simp] theorem rename_swp_kapX :
    rename swp (kapX : MvPolynomial (Fin 2) K) = kapY := by
  simp [kapX, kapY]

@[simp] theorem rename_swp_gamX :
    rename swp (gamX : MvPolynomial (Fin 2) K) = gamY := by
  simp [gamX, gamY, map_ofNat]

@[simp] theorem rename_swp_kapY :
    rename swp (kapY : MvPolynomial (Fin 2) K) = kapX := by
  simp [kapX, kapY]

@[simp] theorem rename_swp_gamY :
    rename swp (gamY : MvPolynomial (Fin 2) K) = gamX := by
  simp [gamX, gamY, map_ofNat]

theorem rename_recursionSource (e : Fin 2 → Fin 2) (κA γA κB γB : MvPolynomial (Fin 2) K)
    (f : ℕ → ℕ → ℕ → MvPolynomial (Fin 2) K) (i j t : ℕ) :
    rename e (recursionSource κA γA κB γB f i j t)
      = recursionSource (rename e κA) (rename e γA) (rename e κB) (rename e γB)
          (fun a b u => rename e (f a b u)) i j t := by
  simp only [recursionSource, map_add, map_mul, map_natCast, map_ofNat]

theorem Van_one_of_Van_zero_rename {g : MvPolynomial (Fin 2) K}
    (h : Van 0 (rename swp g)) : Van 1 g := by
  intro d hd
  have hm : (Finsupp.mapDomain swp d) 0 = 0 := by
    rw [show (0 : Fin 2) = swp 1 from (swp_one).symm,
      Finsupp.mapDomain_apply_of_injective swp_injective d 1]
    exact hd
  have := h (Finsupp.mapDomain swp d) hm
  rwa [coeff_rename_mapDomain swp swp_injective g d] at this

theorem swp_comp_swp : swp ∘ swp = id := by
  funext x
  simp only [swp, Function.comp_apply, id_eq, Equiv.swap_apply_self]

theorem mapDomain_swp_swp (m : Fin 2 →₀ ℕ) :
    Finsupp.mapDomain swp (Finsupp.mapDomain swp m) = m := by
  rw [← Finsupp.mapDomain_comp, swp_comp_swp, Finsupp.mapDomain_id]

theorem mapDomain_swp_mon (a b : ℕ) : Finsupp.mapDomain swp (mon a b) = mon b a := by
  refine finsupp_ext_fin_two ?_ ?_
  · rw [show (0 : Fin 2) = swp 1 from swp_one.symm,
      Finsupp.mapDomain_apply_of_injective swp_injective (mon a b) 1, mon_apply_one, swp_one,
      mon_apply_zero]
  · rw [show (1 : Fin 2) = swp 0 from swp_zero.symm,
      Finsupp.mapDomain_apply_of_injective swp_injective (mon a b) 0, mon_apply_zero, swp_zero,
      mon_apply_one]

theorem cf_rename_swp (a b : ℕ) (g : MvPolynomial (Fin 2) K) :
    cf a b (rename swp g) = cf b a g := by
  rw [cf, ← mapDomain_swp_mon b a, coeff_rename_mapDomain swp swp_injective g (mon b a), cf]

theorem Van_rename_swp {g : MvPolynomial (Fin 2) K} {v : Fin 2} (h : Van (swp v) g) :
    Van v (rename swp g) := by
  intro m hm
  rw [← mapDomain_swp_swp m, coeff_rename_mapDomain swp swp_injective g _]
  refine h _ ?_
  rw [Finsupp.mapDomain_apply_of_injective swp_injective m v]
  exact hm

theorem dcoef_swap (i j t : ℕ) (a b ρ : K) :
    LinearAlgebra.Tridiag.dcoef K j i a b ρ t = LinearAlgebra.Tridiag.dcoef K i j b a ρ t := by
  simp only [LinearAlgebra.Tridiag.dcoef]
  rw [Nat.add_comm j i]
  ring

end Mirror

section MirrorMain

variable {K : Type*} [Field K] {θA θB ρ : K} {Φ : ℕ → ℕ → ℕ → MvPolynomial (Fin 2) K}

theorem isRecursionSolution_swap (hD : IsRecursionSolution θA θB ρ Φ) :
    IsRecursionSolution θB θA ρ (fun a b u => rename swp (Φ b a u)) := by
  intro i j t ht
  have hrow := congrArg (rename (R := K) swp) (hD j i t (by omega))
  rw [rename_recursionSource] at hrow
  simp only [map_sub, map_mul, rename_C, map_natCast, map_ofNat, rename_swp_kapX,
    rename_swp_gamX, rename_swp_kapY, rename_swp_gamY] at hrow
  rw [recursionSource_swap kapX gamX kapY gamY (fun a b u => rename swp (Φ b a u)) i j t] at hrow
  rw [← hrow, dcoef_swap i j t θA θB ρ, Nat.mul_comm (j - t) (i - t)]

theorem vanish_B (hD : IsRecursionSolution θA θB ρ Φ)
    (hE : ∀ i j : ℕ, LinearAlgebra.Tridiag.E K i j θA θB ρ ≠ 0)
    (h1A : ∀ b u : ℕ, Φ 1 b u = 0) (h1B : ∀ a u : ℕ, Φ a 1 u = 0)
    (hrange : ∀ i j t : ℕ, min i j ≤ t → Φ i j t = Φ i j (min i j))
    (i j t : ℕ) (hj : 1 ≤ j) : Van 1 (Φ i j t) := by
  refine Van_one_of_Van_zero_rename ?_
  refine vanish_A (Φ := fun a b u => rename swp (Φ b a u)) (isRecursionSolution_swap hD) ?_ ?_ ?_ ?_
      j i t hj
  · intro a b
    rw [Analysis.RareAlleleHierarchy.E_swap a b θB θA ρ]
    exact hE b a
  · intro b u
    rw [h1B b u, map_zero]
  · intro a u
    rw [h1A a u, map_zero]
  · intro a b u hu
    rw [hrange b a u (by omega), Nat.min_comm a b]

end MirrorMain

end Rhone.Probability.RareAlleleHierarchy
