/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.AlleleLumping.Terms
public import Rhone.Probability.ExplicitFormula.Main

/-! # Allele lumping: every biallelic coarsening is given by the explicit formula -/
set_option linter.style.longLine false

@[expose] public section

namespace Rhone.Probability.AlleleLumping

open Finset LinearAlgebra.Recursion LinearAlgebra.Recursion.Config

variable {KA KB KA' KB' : ℕ} {F : Type*} [Field F]

theorem pushV_id {K : ℕ} (v : Fin K → ℕ) : LinearAlgebra.AlleleLumping.pushV id v = v := by
  funext p
  simp [LinearAlgebra.AlleleLumping.pushV, Finset.filter_eq']

theorem pushM_id (m : Fin KA → Fin KB → ℕ) : LinearAlgebra.AlleleLumping.pushM id id m = m := by
  funext p r
  simp [LinearAlgebra.AlleleLumping.pushM, Finset.filter_eq']

theorem push_id (η : Config KA KB) : LinearAlgebra.AlleleLumping.push id id η = η := by
  simp only [LinearAlgebra.AlleleLumping.push, pushV_id, pushM_id]

theorem pushPi_id {K : ℕ} (π : Fin K → F) : LinearAlgebra.AlleleLumping.pushPi id π = π := by
  funext p
  simp [LinearAlgebra.AlleleLumping.pushPi, Finset.filter_eq']

theorem fibre_id (η : Config KA KB) : LinearAlgebra.AlleleLumping.fibre id id η = {η} := by
  ext ξ
  rw [LinearAlgebra.AlleleLumping.mem_fibre, push_id, Finset.mem_singleton]

theorem lumpSum_id (h : Config KA KB → F) (η : Config KA KB) :
    LinearAlgebra.AlleleLumping.lumpSum id id h η = (LinearAlgebra.AlleleLumping.mult η : F) * h
        η := by
  rw [LinearAlgebra.AlleleLumping.lumpSum, fibre_id, Finset.sum_singleton]

theorem mult_mul_rhs [CharZero F] (θA θB ρ : F) (πA : Fin KA → F) (πB : Fin KB → F)
    (q : Config KA KB → F) (η : Config KA KB) :
    (LinearAlgebra.AlleleLumping.mult η : F) * rhs θA θB ρ πA πB q η
      = LinearAlgebra.AlleleLumping.urhs θA θB ρ πA πB
          (fun ζ => (LinearAlgebra.AlleleLumping.mult ζ : F) * q ζ) η := by
  have h := LinearAlgebra.AlleleLumping.lumpSum_rhs id id q η θA θB ρ πA πB
  rw [lumpSum_id, pushPi_id, pushPi_id] at h
  rw [h]
  congr 1
  funext ζ
  exact lumpSum_id q ζ

theorem push_zero (fA : Fin KA → Fin KA') (fB : Fin KB → Fin KB') :
    LinearAlgebra.AlleleLumping.push fA fB (0 : Config KA KB) = 0 := by
  refine Config.ext ?_ ?_ ?_
  · funext p; simp [LinearAlgebra.AlleleLumping.push, LinearAlgebra.AlleleLumping.pushV]
  · funext r; simp [LinearAlgebra.AlleleLumping.push, LinearAlgebra.AlleleLumping.pushV]
  · funext p r; simp [LinearAlgebra.AlleleLumping.push, LinearAlgebra.AlleleLumping.pushM]

theorem fibre_zero (fA : Fin KA → Fin KA') (fB : Fin KB → Fin KB') :
    LinearAlgebra.AlleleLumping.fibre fA fB (0 : Config KA' KB') = {0} := by
  ext ξ
  rw [LinearAlgebra.AlleleLumping.mem_fibre, Finset.mem_singleton]
  constructor
  · intro h
    refine Config.eq_zero_of_n_eq_zero ξ ?_
    rw [← LinearAlgebra.AlleleLumping.n_push fA fB ξ, h, Config.n_zero]
  · rintro rfl
    exact push_zero fA fB

theorem lumpSum_zero (fA : Fin KA → Fin KA') (fB : Fin KB → Fin KB') (h : Config KA KB → F) :
    LinearAlgebra.AlleleLumping.lumpSum fA fB h 0 = h 0 := by
  rw [LinearAlgebra.AlleleLumping.lumpSum, fibre_zero, Finset.sum_singleton,
      LinearAlgebra.AlleleLumping.mult_zero, Nat.cast_one, one_mul]

noncomputable def lump (fA : Fin KA → Fin KA') (fB : Fin KB → Fin KB') (q : Config KA KB → F)
    (η : Config KA' KB') : F :=
  (LinearAlgebra.AlleleLumping.mult η : F)⁻¹ * LinearAlgebra.AlleleLumping.lumpSum fA fB q η

variable [CharZero F]

theorem mult_cast_ne_zero (η : Config KA KB) : (LinearAlgebra.AlleleLumping.mult η : F) ≠ 0 :=
  Nat.cast_ne_zero.mpr (LinearAlgebra.AlleleLumping.mult_pos η).ne'

theorem mult_mul_lump (fA : Fin KA → Fin KA') (fB : Fin KB → Fin KB') (q : Config KA KB → F)
    (η : Config KA' KB') : (LinearAlgebra.AlleleLumping.mult η : F) * lump fA fB q η =
        LinearAlgebra.AlleleLumping.lumpSum fA fB q η := by
  rw [lump, mul_inv_cancel_left₀ (mult_cast_ne_zero η)]

theorem mult_eA (p : Fin KA) : LinearAlgebra.AlleleLumping.mult (Config.eA p : Config KA KB) = 1 :=
    by
  have h := LinearAlgebra.AlleleLumping.mult_addA (0 : Config KA KB) p
  rw [LinearAlgebra.AlleleLumping.mult_zero, Config.sumA_zero, Config.zero_a] at h
  change LinearAlgebra.AlleleLumping.mult (Config.eA p : Config KA KB) * (0 + 1) = (0 + 1) * 1 at h
  simpa using h

theorem mult_eB (r : Fin KB) : LinearAlgebra.AlleleLumping.mult (Config.eB r : Config KA KB) = 1 :=
    by
  have h := LinearAlgebra.AlleleLumping.mult_addB (0 : Config KA KB) r
  rw [LinearAlgebra.AlleleLumping.mult_zero, Config.sumB_zero, Config.zero_b] at h
  change LinearAlgebra.AlleleLumping.mult (Config.eB r : Config KA KB) * (0 + 1) = (0 + 1) * 1 at h
  simpa using h

theorem mult_eC (p : Fin KA) (r : Fin KB) : LinearAlgebra.AlleleLumping.mult
    (Config.eC p r : Config KA KB) = 1 := by
  have h := LinearAlgebra.AlleleLumping.mult_addC (0 : Config KA KB) p r
  rw [LinearAlgebra.AlleleLumping.mult_zero, Config.t_zero, Config.zero_c] at h
  change LinearAlgebra.AlleleLumping.mult (Config.eC p r : Config KA KB) * (0 + 1) = (0 + 1) *
      1 at h
  simpa using h

variable {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}

theorem lump_isSolution {q : Config KA KB → F} (hq : IsSolution θA θB ρ πA πB q)
    (fA : Fin KA → Fin KA') (fB : Fin KB → Fin KB') :
    IsSolution θA θB ρ (LinearAlgebra.AlleleLumping.pushPi fA πA)
        (LinearAlgebra.AlleleLumping.pushPi fB πB) (lump fA fB q) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [lump, lumpSum_zero, LinearAlgebra.AlleleLumping.mult_zero, hq.empty]
    simp
  · intro p
    rw [lump, mult_eA, Nat.cast_one, inv_one, one_mul]
    have hw := LinearAlgebra.AlleleLumping.sum_lumpSum_weight fA fB (univ.filter fun i => fA i = p)
      (fun i ζ => (ζ.a i : F)) q (Config.eA p) 1 (fun ζ hζ => by
        have ha : ∑ i with fA i = p, ζ.a i = (LinearAlgebra.AlleleLumping.push fA fB ζ).a p := rfl
        rw [← Nat.cast_sum, ha, hζ]
        simp [Config.eA, incf_self])
    rw [one_mul] at hw
    rw [← hw, LinearAlgebra.AlleleLumping.pushPi]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hp : fA i = p := (Finset.mem_filter.mp hi).2
    have h := LinearAlgebra.AlleleLumping.lumpSum_addA fA fB q (0 : Config KA' KB') i
    rw [lumpSum_zero, hp] at h
    change LinearAlgebra.AlleleLumping.lumpSum fA fB (fun ζ => (ζ.a i : F) * q ζ)
        (LinearAlgebra.AlleleLumping.addA 0 p) = _
    rw [← h, ← hq.bdryA i]
    simp
    rfl
  · intro r
    rw [lump, mult_eB, Nat.cast_one, inv_one, one_mul]
    have hw := LinearAlgebra.AlleleLumping.sum_lumpSum_weight fA fB (univ.filter fun j => fB j = r)
      (fun j ζ => (ζ.b j : F)) q (Config.eB r) 1 (fun ζ hζ => by
        have hb : ∑ j with fB j = r, ζ.b j = (LinearAlgebra.AlleleLumping.push fA fB ζ).b r := rfl
        rw [← Nat.cast_sum, hb, hζ]
        simp [Config.eB, incf_self])
    rw [one_mul] at hw
    rw [← hw, LinearAlgebra.AlleleLumping.pushPi]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hr : fB j = r := (Finset.mem_filter.mp hj).2
    have h := LinearAlgebra.AlleleLumping.lumpSum_addB fA fB q (0 : Config KA' KB') j
    rw [lumpSum_zero, hr] at h
    change LinearAlgebra.AlleleLumping.lumpSum fA fB (fun ζ => (ζ.b j : F) * q ζ)
        (LinearAlgebra.AlleleLumping.addB 0 r) = _
    rw [← h, ← hq.bdryB j]
    simp
    rfl
  · intro p r
    rw [lump, mult_eC, Nat.cast_one, inv_one, one_mul]
    have hw := LinearAlgebra.AlleleLumping.sum_lumpSum_weight₂ fA fB (univ.filter fun i => fA i = p)
      (univ.filter fun j => fB j = r)
      (fun i j ζ => (ζ.c i j : F)) q (Config.eC p r) 1 (fun ζ hζ => by
        have hc : ∑ i with fA i = p, ∑ j with fB j = r, ζ.c i j = (LinearAlgebra.AlleleLumping.push fA fB ζ).c p r := rfl
        simp only [← Nat.cast_sum]
        rw [hc, hζ]
        simp [Config.eC, incC_self, incf_self])
    rw [one_mul] at hw
    rw [← hw, LinearAlgebra.AlleleLumping.pushPi, LinearAlgebra.AlleleLumping.pushPi,
        Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
    have hp : fA i = p := (Finset.mem_filter.mp hi).2
    have hr : fB j = r := (Finset.mem_filter.mp hj).2
    have h := LinearAlgebra.AlleleLumping.lumpSum_addC fA fB q (0 : Config KA' KB') i j
    rw [lumpSum_zero, hp, hr] at h
    change LinearAlgebra.AlleleLumping.lumpSum fA fB (fun ζ => (ζ.c i j : F) * q ζ)
        (LinearAlgebra.AlleleLumping.addC 0 p r) = _
    rw [← h, ← hq.bdryC i j]
    simp
    rfl
  · intro η hn
    have h1 : LinearAlgebra.AlleleLumping.lumpSum fA fB (rhs θA θB ρ πA πB q) η
        = diag θA θB ρ η * LinearAlgebra.AlleleLumping.lumpSum fA fB q η := by
      rw [← LinearAlgebra.AlleleLumping.lumpSum_const_mul]
      refine LinearAlgebra.AlleleLumping.lumpSum_congr fun ξ hξ => ?_
      rw [← hq.recursion ξ (by rw [← LinearAlgebra.AlleleLumping.n_push fA fB ξ, hξ]; exact hn)]
      congr 1
      rw [← hξ]
      simp only [LinearAlgebra.Recursion.diag, LinearAlgebra.AlleleLumping.n_push,
          LinearAlgebra.AlleleLumping.nA_push, LinearAlgebra.AlleleLumping.nB_push,
          LinearAlgebra.AlleleLumping.t_push]
    have h2 := mult_mul_rhs θA θB ρ (LinearAlgebra.AlleleLumping.pushPi fA πA)
        (LinearAlgebra.AlleleLumping.pushPi fB πB) (lump fA fB q) η
    simp only [mult_mul_lump] at h2
    refine mul_left_cancel₀ (mult_cast_ne_zero (F := F) η) ?_
    rw [h2, ← LinearAlgebra.AlleleLumping.lumpSum_rhs, h1, mul_left_comm, mult_mul_lump]

variable [LinearOrder F] [IsStrictOrderedRing F]

theorem lumping_eq_qExplicit {q : Config KA KB → F}
    (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hπA : ∑ i, πA i = 1) (hπB : ∑ j, πB j = 1)
    (hq : IsSolution θA θB ρ πA πB q)
    (fA : Fin KA → Fin 2) (fB : Fin KB → Fin 2) (η : Config 2 2) :
    (LinearAlgebra.AlleleLumping.mult η : F) * ExplicitFormula.qExplicit θA θB ρ
        (LinearAlgebra.AlleleLumping.pushPi fA πA) (LinearAlgebra.AlleleLumping.pushPi fB πB) η
      = ∑ ξ ∈ LinearAlgebra.AlleleLumping.fibre fA fB η, (LinearAlgebra.AlleleLumping.mult ξ : F) *
          q ξ := by
  have hA : LinearAlgebra.AlleleLumping.pushPi fA πA 0 + LinearAlgebra.AlleleLumping.pushPi fA πA
      1 = 1 := by
    rw [← Fin.sum_univ_two (LinearAlgebra.AlleleLumping.pushPi fA πA), ← hπA]
    exact Finset.sum_fiberwise univ fA πA
  have hB : LinearAlgebra.AlleleLumping.pushPi fB πB 0 + LinearAlgebra.AlleleLumping.pushPi fB πB
      1 = 1 := by
    rw [← Fin.sum_univ_two (LinearAlgebra.AlleleLumping.pushPi fB πB), ← hπB]
    exact Finset.sum_fiberwise univ fB πB
  rw [← ExplicitFormula.q_eq_qExplicit hθA hθB hρ hA hB (lump_isSolution hq fA fB) η, mult_mul_lump]
  rfl

end Rhone.Probability.AlleleLumping
