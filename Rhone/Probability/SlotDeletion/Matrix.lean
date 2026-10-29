/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.SlotDeletion.Source

/-! # The hierarchy recursion as a tridiagonal system, and vanishing of `Φ^{i,1}` -/

@[expose] public section

universe u

namespace Rhone.Probability.SlotDeletion

open Finset Matrix LinearAlgebra.Recursion Denominator LinearAlgebra.Multilinear Multilinear

section PhiMin

variable {F : Type*} [Field F] (q : Config 2 2 → F) (πA πB : Fin 2 → F)

theorem canM_of_min_le {i j t : ℕ} (h : min i j ≤ t) : canM i j t = canM i j (min i j) := by
  ext p
  simp only [mem_canM]
  constructor
  · rintro ⟨h1, _⟩
    exact ⟨h1, by have := p.1.isLt; have := p.2.isLt; omega⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by omega⟩

theorem Phi_of_min_le {i j t : ℕ} (h : min i j ≤ t) :
    Phi q πA πB i j t = Phi q πA πB i j (min i j) := by
  rw [Phi, Phi, canM_of_min_le h]

end PhiMin

section MulVec

variable {F : Type*} [CommRing F]

theorem sum_ite_val {m : ℕ} (k : ℕ) (X : ℕ → F) :
    (∑ t' : Fin (m + 1), if (t' : ℕ) = k then X (t' : ℕ) else 0)
      = if k < m + 1 then X k else 0 := by
  by_cases h : k < m + 1
  · rw [ite_eq_left h,
      Finset.sum_eq_single (⟨k, h⟩ : Fin (m + 1)) (fun b _ hb => by
        rw [ite_eq_right fun hc => hb (Fin.ext hc)]) fun hc => absurd (Finset.mem_univ _) hc]
    simp
  · rw [ite_eq_right h]
    refine Finset.sum_eq_zero fun t' _ => ite_eq_right fun hc => h ?_
    rw [← hc]
    exact t'.isLt

theorem T_mulVec_apply (i j : ℕ) (θA θB ρ : F) (Ψ : ℕ → F) (t : Fin (min i j + 1)) :
    (LinearAlgebra.Tridiag.T F i j θA θB ρ *ᵥ fun s => Ψ (s : ℕ)) t
      = LinearAlgebra.Tridiag.dcoef F i j θA θB ρ (t : ℕ) * Ψ (t : ℕ)
        - 2 * (((i - (t : ℕ)) * (j - (t : ℕ)) : ℕ) : F) * Ψ ((t : ℕ) + 1)
        - ρ * ((t : ℕ) : F) * Ψ ((t : ℕ) - 1) := by
  have hsplit : ∀ t' : Fin (min i j + 1),
      LinearAlgebra.Tridiag.T F i j θA θB ρ t t' * Ψ (t' : ℕ)
        = (if (t' : ℕ) = (t : ℕ) then LinearAlgebra.Tridiag.dcoef F i j θA θB ρ (t : ℕ) * Ψ (t' : ℕ)
            else 0)
          + (if (t' : ℕ) = (t : ℕ) + 1 then LinearAlgebra.Tridiag.bcoef F i j (t : ℕ) * Ψ (t' : ℕ)
              else 0)
          + (if (t : ℕ) = (t' : ℕ) + 1 then LinearAlgebra.Tridiag.ccoef F ρ (t' : ℕ) * Ψ (t' : ℕ)
              else 0) := by
    intro t'
    simp only [LinearAlgebra.Tridiag.T_apply, LinearAlgebra.Tridiag.tridEntry]
    by_cases h1 : (t' : ℕ) = (t : ℕ)
    · rw [ite_eq_left h1, ite_eq_left h1, ite_eq_right (by omega : ¬((t' : ℕ) = (t : ℕ) + 1)),
        ite_eq_right (by omega : ¬((t : ℕ) = (t' : ℕ) + 1))]
      ring
    · rw [ite_eq_right h1, ite_eq_right h1]
      by_cases h2 : (t' : ℕ) = (t : ℕ) + 1
      · rw [ite_eq_left h2, ite_eq_left h2, ite_eq_right (by omega : ¬((t : ℕ) = (t' : ℕ) + 1))]
        ring
      · rw [ite_eq_right h2, ite_eq_right h2]
        by_cases h3 : (t : ℕ) = (t' : ℕ) + 1
        · rw [ite_eq_left h3, ite_eq_left h3]
          ring
        · rw [ite_eq_right h3, ite_eq_right h3]
          ring
  simp only [Matrix.mulVec, dotProduct, hsplit]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    sum_ite_val (t : ℕ) (fun s => LinearAlgebra.Tridiag.dcoef F i j θA θB ρ (t : ℕ) * Ψ s),
    sum_ite_val ((t : ℕ) + 1) (fun s => LinearAlgebra.Tridiag.bcoef F i j (t : ℕ) * Ψ s),
    ite_eq_left t.isLt]
  have hb : (if (t : ℕ) + 1 < min i j + 1 then LinearAlgebra.Tridiag.bcoef F i j (t : ℕ) * Ψ
      ((t : ℕ) + 1)
      else 0) = LinearAlgebra.Tridiag.bcoef F i j (t : ℕ) * Ψ ((t : ℕ) + 1) := by
    by_cases h : (t : ℕ) + 1 < min i j + 1
    · rw [ite_eq_left h]
    · rw [ite_eq_right h]
      have hmin : (t : ℕ) = min i j := by have := t.isLt; omega
      have : (i - (t : ℕ)) * (j - (t : ℕ)) = 0 := by
        rcases Nat.le_total i j with hij | hij
        · have : (t : ℕ) = i := by rw [hmin, min_eq_left hij]
          simp [this]
        · have : (t : ℕ) = j := by rw [hmin, min_eq_right hij]
          simp [this]
      rw [LinearAlgebra.Tridiag.bcoef, this]
      simp
  have hc : (∑ t' : Fin (min i j + 1),
      if (t : ℕ) = (t' : ℕ) + 1 then LinearAlgebra.Tridiag.ccoef F ρ (t' : ℕ) * Ψ (t' : ℕ) else 0)
      = -(ρ * ((t : ℕ) : F) * Ψ ((t : ℕ) - 1)) := by
    rcases Nat.eq_zero_or_pos (t : ℕ) with h0 | h0
    · rw [Finset.sum_eq_zero fun t' _ => ite_eq_right (by omega), h0]
      simp
    · have hlt : (t : ℕ) - 1 < min i j + 1 := by have := t.isLt; omega
      rw [Finset.sum_eq_single (⟨(t : ℕ) - 1, hlt⟩ : Fin (min i j + 1))
        (fun b _ hb => ite_eq_right fun hcc => hb (Fin.ext (show (b : ℕ) = (t : ℕ) - 1 by omega)))
        fun hcc => absurd (Finset.mem_univ _) hcc,
        ite_eq_left (show (t : ℕ) = ((t : ℕ) - 1) + 1 by omega), LinearAlgebra.Tridiag.ccoef]
      have hcast : (((t : ℕ) - 1 : ℕ) : F) + 1 = ((t : ℕ) : F) := by
        rw [Nat.cast_sub h0, Nat.cast_one]
        ring
      rw [hcast]
      ring
  rw [hb, hc, LinearAlgebra.Tridiag.bcoef]
  ring

end MulVec

section MatrixForm

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA πB : Fin 2 → F}
variable (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
variable {q : Config 2 2 → F} (hq : IsSolution θA θB ρ πA πB q)
include hθA hθB hρ hq

theorem T_mulVec_Phi_eq_phiRecursionSource (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1)
    (i j : ℕ) :
    LinearAlgebra.Tridiag.T F i j θA θB ρ *ᵥ (fun t : Fin (min i j + 1) => Phi q πA πB i j (t : ℕ))
      = fun t : Fin (min i j + 1) => phiRecursionSource q πA πB i j (t : ℕ) := by
  funext t
  have hti : (t : ℕ) ≤ i := by have := t.isLt; omega
  have htj : (t : ℕ) ≤ j := by have := t.isLt; omega
  rw [T_mulVec_apply i j θA θB ρ (fun s => Phi q πA πB i j s) t,
    ← dgQ_mul_Phi_sub_eq_phiRecursionSource hθA hθB hρ hq hπA hπB i j (t : ℕ) hti htj, dgQ_eq_dcoef]
  ring

end MatrixForm

section EOne

variable {F : Type*} [Field F]

theorem cont_two (d b c : ℕ → F) : LinearAlgebra.Tridiag.cont d b c 2 = d 1 * d 0 - b 0 * c 0 := by
  simp [LinearAlgebra.Tridiag.cont]

variable (θA θB ρ : F)

theorem E_zero_one : LinearAlgebra.Tridiag.E F 0 1 θA θB ρ = θB := by
  rw [LinearAlgebra.Tridiag.E_eq_cont]
  norm_num [LinearAlgebra.Tridiag.cont, LinearAlgebra.Tridiag.dcoef]

theorem E_j_one {i : ℕ} (hi : 1 ≤ i) :
    LinearAlgebra.Tridiag.E F i 1 θA θB ρ
      = ((i : F) * ((i : F) - 1) + θA * i + θB)
        * ((i : F) * ((i : F) + 1) + θA * i + θB + ρ) := by
  have hmin : min i 1 = 1 := min_eq_right hi
  have hs : ((i - 1 : ℕ) : F) = (i : F) - 1 := by rw [Nat.cast_sub hi, Nat.cast_one]
  have hd0 : LinearAlgebra.Tridiag.dcoef F i 1 θA θB ρ 0 = ((i : F) + 1) * (i : F) + θA * i + θB :=
      by
    simp only [LinearAlgebra.Tridiag.dcoef, Nat.sub_zero, Nat.add_sub_cancel, Nat.cast_mul,
        Nat.cast_add,
      Nat.cast_one, Nat.cast_zero, mul_zero, add_zero, mul_one]
  have hd1 : LinearAlgebra.Tridiag.dcoef F i 1 θA θB ρ 1 = (i : F) * ((i : F) - 1) + θA * i + θB +
      ρ := by
    simp only [LinearAlgebra.Tridiag.dcoef, Nat.add_sub_cancel, Nat.cast_mul, hs, Nat.cast_one,
        mul_one]
  have hb0 : LinearAlgebra.Tridiag.bcoef F i 1 0 = -2 * (i : F) := by
    simp only [LinearAlgebra.Tridiag.bcoef, Nat.sub_zero, mul_one]
  have hc0 : LinearAlgebra.Tridiag.ccoef F ρ 0 = -ρ := by
    simp only [LinearAlgebra.Tridiag.ccoef, Nat.cast_zero, zero_add, mul_one]
  rw [LinearAlgebra.Tridiag.E_eq_cont, hmin, show (1 : ℕ) + 1 = 2 from rfl, cont_two, hd0, hd1, hb0,
      hc0]
  ring

variable {θA θB ρ}

theorem E_j_one_pos [LinearOrder F] [IsStrictOrderedRing F] (hθA : 0 < θA) (hθB : 0 < θB)
    (hρ : 0 ≤ ρ) (i : ℕ) : 0 < LinearAlgebra.Tridiag.E F i 1 θA θB ρ := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [E_zero_one]; exact hθB
  · rw [E_j_one θA θB ρ hi]
    have h0 : (1 : F) ≤ (i : F) := by exact_mod_cast Nat.one_le_cast.mpr hi
    have h1 : (0 : F) ≤ (i : F) * ((i : F) - 1) := mul_nonneg (by linarith) (by linarith)
    have h2 : (0 : F) ≤ (i : F) * ((i : F) + 1) := mul_nonneg (by linarith) (by linarith)
    have h3 : (0 : F) ≤ θA * i := mul_nonneg hθA.le (by linarith)
    exact mul_pos (by linarith) (by linarith)

end EOne

section Cor41

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA πB : Fin 2 → F}
variable (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
variable {q : Config 2 2 → F} (hq : IsSolution θA θB ρ πA πB q)
include hθA hθB hρ hq

omit hθA hθB hρ hq in
theorem phiRecursionSource_j_one_eq_zero (i : ℕ)
    (hlow : ∀ i' < i, ∀ t' : ℕ, Phi q πA πB i' 1 t' = 0)
    {t : ℕ} (ht : t ≤ min i 1) : phiRecursionSource q πA πB i 1 t = 0 := by
  have ht1 : t ≤ 1 := le_trans ht (min_le_right i 1)
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · have ht0 : t = 0 := by simpa using le_trans ht (min_le_left 0 1)
    subst ht0
    norm_num [phiRecursionSource]
  · have hA : ∀ t' : ℕ, Phi q πA πB (i - 2) 1 t' = 0 := hlow _ (by omega)
    have hB : ∀ t' : ℕ, Phi q πA πB (i - 1) 1 t' = 0 := hlow _ (by omega)
    interval_cases t <;> simp [phiRecursionSource, hA, hB]

theorem Phi_j_one (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1) (i t : ℕ) :
    Phi q πA πB i 1 t = 0 := by
  induction i using Nat.strong_induction_on generalizing t with
  | _ i ih =>
    have hzero : LinearAlgebra.Tridiag.T F i 1 θA θB ρ
        *ᵥ (fun s : Fin (min i 1 + 1) => Phi q πA πB i 1 (s : ℕ)) = 0 := by
      rw [T_mulVec_Phi_eq_phiRecursionSource hθA hθB hρ hq hπA hπB i 1]
      funext s
      exact phiRecursionSource_j_one_eq_zero i (fun i' hi' t' => ih i' hi' t')
        (by have := s.isLt; omega)
    have hE : LinearAlgebra.Tridiag.E F i 1 θA θB ρ ≠ 0 := (E_j_one_pos hθA hθB hρ i).ne'
    have hres := LinearAlgebra.Tridiag.eq_zero_of_mulVec_eq_zero i 1 θA θB ρ hE hzero
    rcases Nat.lt_or_ge t (min i 1) with hlt | hge
    · exact congrFun hres ⟨t, by omega⟩
    · rw [Phi_of_min_le q πA πB hge]
      exact congrFun hres ⟨min i 1, Nat.lt_succ_self _⟩

theorem Phi_j_one_factor (hπB : πB 0 + πB 1 = 1) (i t : ℕ) : Phi q πA πB i 1 t = 0 :=
  Q_eq_zero_of_one_B_slot hθA hθB hρ hq (canM i 1 t) (isMatching_canM i 1 t)
    (Fintype.card_fin 1) _ _ fun _ => mean_fvec hπB

end Cor41

section MirrorA

variable {KA KB : ℕ} {SA SB : Type*}
variable [Fintype SA] [DecidableEq SA] [Fintype SB] [DecidableEq SB]
variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}
variable (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
variable {q : Config KA KB → F} (hq : IsSolution θA θB ρ πA πB q)
include hθA hθB hρ hq

theorem Q_eq_zero_of_one_A_slot (M : Finset (SA × SB)) (hM : IsMatching M)
    (hcard : Fintype.card SA = 1) (s : SA → Fin KA → F) (w : SB → Fin KB → F)
    (hcen : ∀ u, mean πA (s u) = 0) : Q q M s w = 0 := by
  obtain ⟨u₀, hu₀⟩ := Fintype.card_eq_one_iff.mp hcard
  have huniv : (univ : Finset SA) = {u₀} :=
    Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_univ _, fun x _ => hu₀ x⟩
  have hA : (∑ α : SA → Fin KA, (∏ u, s u (α u)) * qOne θA πA (mAof α)) = 0 := by
    have hterm : ∀ α : SA → Fin KA,
        (∏ u, s u (α u)) * qOne θA πA (mAof α) = s u₀ (α u₀) * πA (α u₀) := by
      intro α
      have hprod : (∏ u, s u (α u)) = s u₀ (α u₀) :=
        Finset.prod_eq_single_of_mem u₀ (Finset.mem_univ _) fun u _ hu => absurd (hu₀ u) hu
      have hm : mAof α = incf (fun _ => 0) (α u₀) := by
        funext i
        rw [mAof, huniv, incf_apply, Finset.filter_singleton]
        by_cases h : α u₀ = i
        · rw [ite_eq_left h, Finset.card_singleton, ite_eq_left h.symm]
        · rw [ite_eq_right h, Finset.card_empty, ite_eq_right fun hc => h hc.symm]
      rw [hprod, hm, qOne_eA hθA.ne']
    rw [Finset.sum_congr rfl fun α _ => hterm α]
    let e : (SA → Fin KA) ≃ Fin KA :=
      { toFun := fun α => α u₀
        invFun := fun i _ => i
        left_inv := fun α => funext fun u => by rw [hu₀ u]
        right_inv := fun _ => rfl }
    rw [Fintype.sum_equiv e (fun α => s u₀ (α u₀) * πA (α u₀)) (fun i => s u₀ i * πA i)
      fun _ => rfl]
    have hz := hcen u₀
    rw [mean] at hz
    rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) => mul_comm (s u₀ i) (πA i), hz]
  rw [Q_factor hθA hθB hρ hq M hM (Or.inl (le_of_eq hcard)) s w, hA, zero_mul]

end MirrorA

section PhiIOne

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA πB : Fin 2 → F}
variable (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
variable {q : Config 2 2 → F} (hq : IsSolution θA θB ρ πA πB q)
include hθA hθB hρ hq

theorem Phi_i_one (hπA : πA 0 + πA 1 = 1) (j t : ℕ) : Phi q πA πB 1 j t = 0 :=
  Q_eq_zero_of_one_A_slot hθA hθB hρ hq (canM 1 j t) (isMatching_canM 1 j t)
    (Fintype.card_fin 1) _ _ fun _ => mean_fvec hπA

end PhiIOne

end Rhone.Probability.SlotDeletion
