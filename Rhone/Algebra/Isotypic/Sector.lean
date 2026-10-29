/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib

/-! # Sector deletion for an abstract block-graded system: denominators of contrasts -/

@[expose] public section

namespace Rhone.Algebra.Isotypic

open Finset

section HasDen

variable {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V] [Module R V]

def HasDen (L : Submodule R V) (d : R) (x : V) : Prop := d • x ∈ L

theorem hasDen_def (L : Submodule R V) (d : R) (x : V) : HasDen L d x ↔ d • x ∈ L := Iff.rfl

theorem HasDen.zero (L : Submodule R V) (d : R) : HasDen L d (0 : V) := by
  simp [HasDen]

theorem HasDen.add {L : Submodule R V} {d : R} {x y : V} (hx : HasDen L d x)
    (hy : HasDen L d y) : HasDen L d (x + y) := by
  simpa [HasDen, smul_add] using L.add_mem hx hy

theorem HasDen.neg {L : Submodule R V} {d : R} {x : V} (hx : HasDen L d x) :
    HasDen L d (-x) := by
  simpa [HasDen, smul_neg] using L.neg_mem hx

theorem HasDen.sub {L : Submodule R V} {d : R} {x y : V} (hx : HasDen L d x)
    (hy : HasDen L d y) : HasDen L d (x - y) := by
  simpa [sub_eq_add_neg] using hx.add hy.neg

theorem HasDen.smul {L : Submodule R V} {d : R} {x : V} (hx : HasDen L d x) (c : R) :
    HasDen L d (c • x) := by
  have h : d • (c • x) = c • (d • x) := smul_comm d c x
  rw [HasDen, h]
  exact L.smul_mem c hx

theorem HasDen.zsmul {L : Submodule R V} {d : R} {x : V} (hx : HasDen L d x) (n : ℤ) :
    HasDen L d (n • x) := by
  have h : d • (n • x) = n • (d • x) := smul_comm d n x
  rw [HasDen, h]
  exact zsmul_mem hx n

theorem HasDen.of_dvd {L : Submodule R V} {d e : R} {x : V} (hx : HasDen L d x) (h : d ∣ e) :
    HasDen L e x := by
  obtain ⟨c, rfl⟩ := h
  have h2 : (d * c) • x = c • (d • x) := by rw [mul_comm, mul_smul]
  rw [HasDen, h2]
  exact L.smul_mem c hx

theorem HasDen.sum {ι : Type*} {L : Submodule R V} {d : R} {s : Finset ι} {f : ι → V}
    (hf : ∀ i ∈ s, HasDen L d (f i)) : HasDen L d (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using HasDen.zero L d
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hf a (Finset.mem_insert_self a s)).add
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem HasDen.of_bezout {L : Submodule R V} {d₁ d₂ g : R} {x : V} (h₁ : HasDen L d₁ x)
    (h₂ : HasDen L d₂ x) {u v : R} (hg : u * d₁ + v * d₂ = g) : HasDen L g x := by
  rw [HasDen, ← hg, add_smul, mul_smul, mul_smul]
  exact L.add_mem (L.smul_mem u h₁) (L.smul_mem v h₂)

def Lat (R F : Type*) [CommRing R] [CommRing F] [Algebra R F] : Submodule R F :=
  LinearMap.range (Algebra.linearMap R F)

theorem hasDen_lat_iff {F : Type*} [CommRing F] [Algebra R F] (d : R) (x : F) :
    HasDen (Lat R F) d x ↔ ∃ a : R, algebraMap R F a = d • x := Iff.rfl

end HasDen

section HasDenGcd

variable {R : Type*} [EuclideanDomain R] [DecidableEq R] {V : Type*} [AddCommGroup V]
  [Module R V]

theorem HasDen.gcd_euclidean {L : Submodule R V} {d₁ d₂ : R} {x : V} (h₁ : HasDen L d₁ x)
    (h₂ : HasDen L d₂ x) : HasDen L (EuclideanDomain.gcd d₁ d₂) x :=
  h₁.of_bezout h₂ (u := EuclideanDomain.gcdA d₁ d₂) (v := EuclideanDomain.gcdB d₁ d₂)
    (by rw [mul_comm, mul_comm (EuclideanDomain.gcdB d₁ d₂) d₂];
        exact (EuclideanDomain.gcd_eq_gcd_ab d₁ d₂).symm)

end HasDenGcd

section Sym

variable {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V] [Module R V]

def perpProj (p : V →ₗ[R] V) : V →ₗ[R] V := LinearMap.id - p

@[simp] theorem perpProj_apply (p : V →ₗ[R] V) (x : V) : perpProj p x = x - p x := rfl

variable (G : Type*) [Group G] [Fintype G] [Invertible (Fintype.card G : R)]

def symA (ρ : G → (V →ₗ[R] V)) : V →ₗ[R] V := (⅟(Fintype.card G : R)) • ∑ g : G, ρ g

omit [Group G] in
theorem symA_apply (ρ : G → (V →ₗ[R] V)) (x : V) :
    symA G ρ x = (⅟(Fintype.card G : R)) • ∑ g : G, ρ g x := by
  simp [symA, LinearMap.sum_apply]

theorem smul_symA (ρ : G → (V →ₗ[R] V))
    (hρ : ∀ (g h : G) (x : V), ρ g (ρ h x) = ρ (g * h) x) (h : G) (x : V) :
    ρ h (symA G ρ x) = symA G ρ x := by
  rw [symA_apply, map_smul, map_sum]
  congr 1
  refine Fintype.sum_bijective (fun g => h * g) (Group.mulLeft_bijective h) _ _ ?_
  intro g
  exact hρ h g x

theorem symA_idem (ρ : G → (V →ₗ[R] V))
    (hρ : ∀ (g h : G) (x : V), ρ g (ρ h x) = ρ (g * h) x) (x : V) :
    symA G ρ (symA G ρ x) = symA G ρ x := by
  rw [symA_apply]
  have h : ∀ g : G, ρ g (symA G ρ x) = symA G ρ x := fun g => smul_symA G ρ hρ g x
  simp only [h, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul R, smul_smul, invOf_mul_self, one_smul]

omit [Group G] in
theorem symA_comm (ρ : G → (V →ₗ[R] V)) (M : V →ₗ[R] V)
    (hM : ∀ (g : G) (x : V), M (ρ g x) = ρ g (M x)) (x : V) :
    M (symA G ρ x) = symA G ρ (M x) := by
  rw [symA_apply, symA_apply, map_smul, map_sum]
  simp only [hM]

end Sym

section Det

variable {R : Type*} [CommRing R]

theorem cramerVec {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n R) (v : n → R) :
    A.det • v = A.adjugate.mulVec (A.mulVec v) := by
  rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem detCompl_dvd_det {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n]
    (Mb : ι → Matrix n n R) (s : Finset ι) :
    (∏ i ∈ s, (Mb i).det) ∣ (Matrix.blockDiagonal Mb).det := by
  rw [Matrix.det_blockDiagonal]
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ s)

end Det

section Bound

variable {R : Type*} [CommRing R]

def dBound (dc : ℕ → R) (B : R) (j : ℕ) : R := (∏ q ∈ Finset.Icc 2 j, dc q) * B

theorem dBound_mono (dc : ℕ → R) (B : R) {q j : ℕ} (h : q ≤ j) :
    dBound dc B q ∣ dBound dc B j :=
  mul_dvd_mul_right
    (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.Icc_subset_Icc_right h)) B

theorem base_dvd_dBound (dc : ℕ → R) (B : R) (j : ℕ) : B ∣ dBound dc B j :=
  dvd_mul_left B _

theorem dBound_succ (dc : ℕ → R) (B : R) {j : ℕ} (hj : 1 ≤ j) :
    dBound dc B (j + 1) = dc (j + 1) * dBound dc B j := by
  unfold dBound
  rw [Finset.prod_Icc_succ_top (by omega)]
  ring

end Bound

section Main

variable {R : Type*} [CommRing R] {V : ℕ → Type*} [∀ j, AddCommGroup (V j)]
  [∀ j, Module R (V j)]

theorem den_compl_dvd (L : ∀ j, Submodule R (V j)) (Mop : ∀ j, V j →ₗ[R] V j)
    (p : ∀ j, V j →ₗ[R] V j) (N : ∀ j, V j →ₗ[R] V j) (Θ : ∀ q j, V q →ₗ[R] V j)
    (Φ : ∀ j, V j) (Rlow : ∀ j, V j) (dc : ℕ → R) (B : R)
    (hp : ∀ j x, p j (p j x) = p j x)
    (hpM : ∀ j x, p j (Mop j x) = Mop j (p j x))
    (hpΘ : ∀ q j x, p j (Θ q j x) = Θ q j (p q x))
    (hLp : ∀ j x, x ∈ L j → p j x ∈ L j)
    (hLΘ : ∀ q j x, x ∈ L q → Θ q j x ∈ L j)
    (hLN : ∀ j x, x ∈ L j → N j x ∈ L j)
    (hcram : ∀ (j : ℕ) (x : V j), p j x = 0 → dc j • x = N j (Mop j x))
    (hsrc : ∀ j, Mop j (Φ j) = Rlow j + ∑ q ∈ Finset.range j, Θ q j (Φ q))
    (hRlow : ∀ j, B • Rlow j ∈ L j)
    (hΦ0 : p 0 (Φ 0) = Φ 0) (hΦ1 : Φ 1 = 0) :
    ∀ j, HasDen (L j) (dBound dc B j) (perpProj (p j) (Φ j)) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    by_cases hj : j ≤ 1
    · interval_cases j
      · simpa [perpProj_apply, hΦ0] using HasDen.zero (L 0) (dBound dc B 0)
      · simpa [perpProj_apply, hΦ1] using HasDen.zero (L 1) (dBound dc B 1)
    · obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 + 1 := ⟨j - 2, by omega⟩
      set y : V (n + 1 + 1) := perpProj (p (n + 1 + 1)) (Φ (n + 1 + 1)) with hy
      have hpy : p (n + 1 + 1) y = 0 := by
        rw [hy, perpProj_apply, map_sub, hp]
        exact sub_self _
      have hc : dc (n + 1 + 1) • y = N (n + 1 + 1) (Mop (n + 1 + 1) y) :=
        hcram (n + 1 + 1) y hpy
      have hMy : Mop (n + 1 + 1) y
          = perpProj (p (n + 1 + 1)) (Mop (n + 1 + 1) (Φ (n + 1 + 1))) := by
        rw [hy, perpProj_apply, map_sub, perpProj_apply, hpM]
      have hsplit : perpProj (p (n + 1 + 1)) (Mop (n + 1 + 1) (Φ (n + 1 + 1)))
          = perpProj (p (n + 1 + 1)) (Rlow (n + 1 + 1))
            + ∑ q ∈ Finset.range (n + 1 + 1),
                Θ q (n + 1 + 1) (perpProj (p q) (Φ q)) := by
        have hterm : ∀ q ∈ Finset.range (n + 1 + 1),
            Θ q (n + 1 + 1) (perpProj (p q) (Φ q))
              = Θ q (n + 1 + 1) (Φ q) - p (n + 1 + 1) (Θ q (n + 1 + 1) (Φ q)) := by
          intro q _
          rw [perpProj_apply, map_sub, hpΘ]
        have e1 : ∑ q ∈ Finset.range (n + 1 + 1), Θ q (n + 1 + 1) (perpProj (p q) (Φ q))
            = (∑ q ∈ Finset.range (n + 1 + 1), Θ q (n + 1 + 1) (Φ q))
              - p (n + 1 + 1) (∑ q ∈ Finset.range (n + 1 + 1), Θ q (n + 1 + 1) (Φ q)) := by
          rw [map_sum, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl hterm
        rw [e1, hsrc (n + 1 + 1), perpProj_apply, perpProj_apply, map_add]
        abel
      have hinner : dBound dc B (n + 1) • Mop (n + 1 + 1) y ∈ L (n + 1 + 1) := by
        rw [hMy, hsplit, smul_add]
        refine Submodule.add_mem _ ?_ ?_
        · have h1 : HasDen (L (n + 1 + 1)) (dBound dc B (n + 1)) (Rlow (n + 1 + 1)) :=
            HasDen.of_dvd (hRlow (n + 1 + 1)) (base_dvd_dBound dc B (n + 1))
          have h2 : HasDen (L (n + 1 + 1)) (dBound dc B (n + 1))
              (p (n + 1 + 1) (Rlow (n + 1 + 1))) := by
            rw [hasDen_def, ← map_smul]
            exact hLp (n + 1 + 1) _ h1
          exact h1.sub h2
        · rw [Finset.smul_sum]
          refine Submodule.sum_mem _ fun q hq => ?_
          have hql : q < n + 1 + 1 := Finset.mem_range.mp hq
          have hqIH : HasDen (L q) (dBound dc B (n + 1)) (perpProj (p q) (Φ q)) :=
            (ih q hql).of_dvd (dBound_mono dc B (by omega))
          rw [← map_smul]
          exact hLΘ q (n + 1 + 1) _ hqIH
      have hfin : dBound dc B (n + 1 + 1) • y
          = N (n + 1 + 1) (dBound dc B (n + 1) • Mop (n + 1 + 1) y) := by
        rw [map_smul, ← hc, smul_smul, dBound_succ dc B (by omega : 1 ≤ n + 1), mul_comm]
      rw [hasDen_def, hfin]
      exact hLN (n + 1 + 1) _ hinner

end Main

section Contrast

variable {R : Type*} [CommRing R] {V W : Type*} [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W]

theorem contrast_of_symA_perp (p : V →ₗ[R] V) (ψ : V →ₗ[R] W) (g : V →ₗ[R] V)
    (hg : ∀ x : V, ψ (g (p x)) = ψ (p x)) (Φ : V) :
    ψ Φ - ψ (g Φ) = ψ (perpProj p Φ) - ψ (g (perpProj p Φ)) := by
  have h1 : ψ (perpProj p Φ) = ψ Φ - ψ (p Φ) := by rw [perpProj_apply, map_sub]
  have h2 : ψ (g (perpProj p Φ)) = ψ (g Φ) - ψ (p Φ) := by
    rw [perpProj_apply, map_sub, map_sub, hg]
  rw [h1, h2]
  abel

variable (G : Type*) [Group G] [Fintype G] [Invertible (Fintype.card G : R)]

theorem contrast_symA_perp (ρ : G → (V →ₗ[R] V))
    (hρ : ∀ (g h : G) (x : V), ρ g (ρ h x) = ρ (g * h) x) (ψ : V →ₗ[R] W) (h : G) (Φ : V) :
    ψ Φ - ψ (ρ h Φ) = ψ (perpProj (symA G ρ) Φ) - ψ (ρ h (perpProj (symA G ρ) Φ)) :=
  contrast_of_symA_perp (symA G ρ) ψ (ρ h) (fun x => by rw [smul_symA G ρ hρ h x]) Φ

end Contrast

section Assembly

variable {R : Type*} [CommRing R] {V : ℕ → Type*} [∀ j, AddCommGroup (V j)]
  [∀ j, Module R (V j)] {W : Type*} [AddCommGroup W] [Module R W]

theorem den_contrast (L : ∀ j, Submodule R (V j)) (L' : Submodule R W)
    (Mop : ∀ j, V j →ₗ[R] V j) (p : ∀ j, V j →ₗ[R] V j) (N : ∀ j, V j →ₗ[R] V j)
    (Θ : ∀ q j, V q →ₗ[R] V j) (Φ : ∀ j, V j) (Rlow : ∀ j, V j) (dc : ℕ → R) (B : R)
    (hp : ∀ j x, p j (p j x) = p j x)
    (hpM : ∀ j x, p j (Mop j x) = Mop j (p j x))
    (hpΘ : ∀ q j x, p j (Θ q j x) = Θ q j (p q x))
    (hLp : ∀ j x, x ∈ L j → p j x ∈ L j)
    (hLΘ : ∀ q j x, x ∈ L q → Θ q j x ∈ L j)
    (hLN : ∀ j x, x ∈ L j → N j x ∈ L j)
    (hcram : ∀ (j : ℕ) (x : V j), p j x = 0 → dc j • x = N j (Mop j x))
    (hsrc : ∀ j, Mop j (Φ j) = Rlow j + ∑ q ∈ Finset.range j, Θ q j (Φ q))
    (hRlow : ∀ j, B • Rlow j ∈ L j)
    (hΦ0 : p 0 (Φ 0) = Φ 0) (hΦ1 : Φ 1 = 0)
    (j : ℕ) (ψ : V j →ₗ[R] W) (g : V j →ₗ[R] V j)
    (hψL : ∀ x ∈ L j, ψ x ∈ L') (hgL : ∀ x ∈ L j, g x ∈ L j)
    (hg : ∀ x : V j, ψ (g (p j x)) = ψ (p j x)) :
    HasDen L' (dBound dc B j) (ψ (Φ j) - ψ (g (Φ j))) := by
  have hmain : HasDen (L j) (dBound dc B j) (perpProj (p j) (Φ j)) :=
    den_compl_dvd L Mop p N Θ Φ Rlow dc B hp hpM hpΘ hLp hLΘ hLN hcram hsrc hRlow hΦ0 hΦ1 j
  rw [contrast_of_symA_perp (p j) ψ g hg (Φ j)]
  have h1 : HasDen L' (dBound dc B j) (ψ (perpProj (p j) (Φ j))) := by
    rw [hasDen_def, ← map_smul]
    exact hψL _ hmain
  have h2 : HasDen L' (dBound dc B j) (ψ (g (perpProj (p j) (Φ j)))) := by
    rw [hasDen_def, ← map_smul, ← map_smul]
    exact hψL _ (hgL _ hmain)
  exact h1.sub h2

end Assembly

end Rhone.Algebra.Isotypic
