/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.Multilinear.Moves
public import Rhone.LinearAlgebra.Multilinear.Multi

/-! # The multilinear extension `Q` -/

@[expose] public section

namespace Rhone.Probability.Multilinear

open Finset LinearAlgebra.Recursion Denominator

variable {KA KB : ℕ} {F : Type*} [CommRing F] {SA SB : Type*}

theorem prod_update {ι : Type*} [Fintype ι] [DecidableEq ι] {K : ℕ} (s : ι → Fin K → F)
    (u : ι) (x : Fin K → F) (α : ι → Fin K) :
    (∏ u', Function.update s u x u' (α u')) = x (α u) * ∏ u' ∈ univ.erase u, s u' (α u') := by
  have h : (fun u' => Function.update s u x u' (α u'))
      = Function.update (fun u' => s u' (α u')) u (x (α u)) := by
    funext u'
    by_cases hu : u' = u
    · subst hu; simp
    · simp [Function.update_of_ne hu]
  calc (∏ u', Function.update s u x u' (α u'))
      = ∏ u', Function.update (fun u'' => s u'' (α u'')) u (x (α u)) u' := by rw [h]
    _ = x (α u) * ∏ u' ∈ univ \ {u}, s u' (α u') :=
        Finset.prod_update_of_mem (Finset.mem_univ u) _ _
    _ = x (α u) * ∏ u' ∈ univ.erase u, s u' (α u') := by
        rw [Finset.sdiff_singleton_eq_erase]

section Q

variable [Fintype SA] [DecidableEq SA] [Fintype SB] [DecidableEq SB]

def Q (q : Config KA KB → F) (M : Finset (SA × SB))
    (s : SA → Fin KA → F) (w : SB → Fin KB → F) : F :=
  ∑ α : SA → Fin KA, ∑ β : SB → Fin KB,
    (∏ u, s u (α u)) * (∏ v, w v (β v)) * q (xi M α β)

variable (q : Config KA KB → F) (M : Finset (SA × SB))

theorem Q_isMultiA (w : SB → Fin KB → F) : LinearAlgebra.Multilinear.IsMulti (fun s => Q q M s w) :=
    by
  refine LinearAlgebra.Multilinear.isMulti_of (fun s u x y => ?_) (fun s u c x => ?_)
  · simp only [Q]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [prod_update, prod_update, prod_update]
    simp only [Pi.add_apply]
    ring
  · simp only [Q, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
    rw [prod_update, prod_update]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

theorem Q_isMultiB (s : SA → Fin KA → F) : LinearAlgebra.Multilinear.IsMulti (fun w => Q q M s w) :=
    by
  refine LinearAlgebra.Multilinear.isMulti_of (fun w v x y => ?_) (fun w v c x => ?_)
  · simp only [Q]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [prod_update, prod_update, prod_update]
    simp only [Pi.add_apply]
    ring
  · simp only [Q, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
    rw [prod_update, prod_update]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

theorem Q_basis (α : SA → Fin KA) (β : SB → Fin KB) :
    Q q M (fun u => Pi.single (α u) 1) (fun v => Pi.single (β v) 1) = q (xi M α β) := by
  have hin : ∀ α' : SA → Fin KA, (∑ β' : SB → Fin KB,
      (if α' = α then (1 : F) else 0) * (if β' = β then (1 : F) else 0) * q (xi M α' β'))
      = (if α' = α then (1 : F) else 0) * q (xi M α' β) := by
    intro α'
    rw [Finset.sum_eq_single β (fun b _ hb => by simp [hb])
      fun hb => absurd (Finset.mem_univ β) hb]
    simp
  simp only [Q, LinearAlgebra.Multilinear.prod_single_apply]
  rw [Finset.sum_congr rfl fun α' _ => hin α',
    Finset.sum_eq_single α (fun a _ ha => by simp [ha]) fun ha => absurd (Finset.mem_univ α) ha]
  simp

end Q

section Had

variable [DecidableEq SA] [DecidableEq SB]

def hadA (k m : SA) (s : SA → Fin KA → F) : SA → Fin KA → F :=
  Function.update (Function.update s k (s k * s m)) m 1

def hadB (l n : SB) (w : SB → Fin KB → F) : SB → Fin KB → F :=
  Function.update (Function.update w l (w l * w n)) n 1

variable {k m : SA} (hkm : k ≠ m) (s : SA → Fin KA → F)
include hkm

theorem hadA_update_left (x : Fin KA → F) :
    hadA k m (Function.update s k x) = Function.update (hadA k m s) k (x * s m) := by
  funext u
  simp only [hadA, Function.update_apply]
  by_cases h1 : u = m <;> by_cases h2 : u = k <;> simp_all [Ne.symm hkm]

theorem hadA_update_right (x : Fin KA → F) :
    hadA k m (Function.update s m x) = Function.update (hadA k m s) k (s k * x) := by
  funext u
  simp only [hadA, Function.update_apply]
  by_cases h1 : u = m <;> by_cases h2 : u = k <;> simp_all [Ne.symm hkm]

theorem hadA_update_other {p : SA} (hpk : p ≠ k) (hpm : p ≠ m) (x : Fin KA → F) :
    hadA k m (Function.update s p x) = Function.update (hadA k m s) p x := by
  funext u
  simp only [hadA, Function.update_apply]
  by_cases h1 : u = m <;> by_cases h2 : u = k <;> by_cases h3 : u = p <;>
    simp_all [Ne.symm hkm, Ne.symm hpk, Ne.symm hpm]

end Had

section HadB

variable [DecidableEq SB] {l n : SB} (hln : l ≠ n) (w : SB → Fin KB → F)
include hln

theorem hadB_update_left (x : Fin KB → F) :
    hadB l n (Function.update w l x) = Function.update (hadB l n w) l (x * w n) := by
  funext v
  simp only [hadB, Function.update_apply]
  by_cases h1 : v = n <;> by_cases h2 : v = l <;> simp_all [Ne.symm hln]

theorem hadB_update_right (x : Fin KB → F) :
    hadB l n (Function.update w n x) = Function.update (hadB l n w) l (w l * x) := by
  funext v
  simp only [hadB, Function.update_apply]
  by_cases h1 : v = n <;> by_cases h2 : v = l <;> simp_all [Ne.symm hln]

theorem hadB_update_other {p : SB} (hpl : p ≠ l) (hpn : p ≠ n) (x : Fin KB → F) :
    hadB l n (Function.update w p x) = Function.update (hadB l n w) p x := by
  funext v
  simp only [hadB, Function.update_apply]
  by_cases h1 : v = n <;> by_cases h2 : v = l <;> by_cases h3 : v = p <;>
    simp_all [Ne.symm hln, Ne.symm hpl, Ne.symm hpn]

end HadB

section Terms

variable [Fintype SA] [DecidableEq SA] [Fintype SB] [DecidableEq SB]
variable (q : Config KA KB → F) (M : Finset (SA × SB))

theorem Q_hadA_isMultiA (w : SB → Fin KB → F) {k m : SA} (hkm : k ≠ m) :
    LinearAlgebra.Multilinear.IsMulti (fun s => Q q M (hadA k m s) w) := by
  refine LinearAlgebra.Multilinear.isMulti_of (fun s p x y => ?_) (fun s p c x => ?_)
  · rcases eq_or_ne p k with rfl | hpk
    · rw [hadA_update_left hkm, hadA_update_left hkm, hadA_update_left hkm,
        show (x + y) * s m = x * s m + y * s m from by ring]
      exact (Q_isMultiA q M w).add _ _ _ _
    · rcases eq_or_ne p m with rfl | hpm
      · rw [hadA_update_right hkm, hadA_update_right hkm, hadA_update_right hkm,
          show s k * (x + y) = s k * x + s k * y from by ring]
        exact (Q_isMultiA q M w).add _ _ _ _
      · rw [hadA_update_other hkm s hpk hpm, hadA_update_other hkm s hpk hpm,
          hadA_update_other hkm s hpk hpm]
        exact (Q_isMultiA q M w).add _ _ _ _
  · rcases eq_or_ne p k with rfl | hpk
    · rw [hadA_update_left hkm, hadA_update_left hkm,
        show (c • x) * s m = c • (x * s m) from by
          funext i; simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]; ring]
      exact (Q_isMultiA q M w).smul _ _ _ _
    · rcases eq_or_ne p m with rfl | hpm
      · rw [hadA_update_right hkm, hadA_update_right hkm,
          show s k * (c • x) = c • (s k * x) from by
            funext i; simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]; ring]
        exact (Q_isMultiA q M w).smul _ _ _ _
      · rw [hadA_update_other hkm s hpk hpm, hadA_update_other hkm s hpk hpm]
        exact (Q_isMultiA q M w).smul _ _ _ _

theorem Q_hadB_isMultiB (s : SA → Fin KA → F) {l n : SB} (hln : l ≠ n) :
    LinearAlgebra.Multilinear.IsMulti (fun w => Q q M s (hadB l n w)) := by
  refine LinearAlgebra.Multilinear.isMulti_of (fun w p x y => ?_) (fun w p c x => ?_)
  · rcases eq_or_ne p l with rfl | hpl
    · rw [hadB_update_left hln, hadB_update_left hln, hadB_update_left hln,
        show (x + y) * w n = x * w n + y * w n from by ring]
      exact (Q_isMultiB q M s).add _ _ _ _
    · rcases eq_or_ne p n with rfl | hpn
      · rw [hadB_update_right hln, hadB_update_right hln, hadB_update_right hln,
          show w l * (x + y) = w l * x + w l * y from by ring]
        exact (Q_isMultiB q M s).add _ _ _ _
      · rw [hadB_update_other hln w hpl hpn, hadB_update_other hln w hpl hpn,
          hadB_update_other hln w hpl hpn]
        exact (Q_isMultiB q M s).add _ _ _ _
  · rcases eq_or_ne p l with rfl | hpl
    · rw [hadB_update_left hln, hadB_update_left hln,
        show (c • x) * w n = c • (x * w n) from by
          funext j; simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]; ring]
      exact (Q_isMultiB q M s).smul _ _ _ _
    · rcases eq_or_ne p n with rfl | hpn
      · rw [hadB_update_right hln, hadB_update_right hln,
          show w l * (c • x) = c • (w l * x) from by
            funext j; simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]; ring]
        exact (Q_isMultiB q M s).smul _ _ _ _
      · rw [hadB_update_other hln w hpl hpn, hadB_update_other hln w hpl hpn]
        exact (Q_isMultiB q M s).smul _ _ _ _

def mean {K : ℕ} (π x : Fin K → F) : F := ∑ i, π i * x i

theorem mean_add {K : ℕ} (π x y : Fin K → F) : mean π (x + y) = mean π x + mean π y := by
  simp only [mean, Pi.add_apply, mul_add]
  exact Finset.sum_add_distrib

theorem mean_smul {K : ℕ} (π x : Fin K → F) (c : F) : mean π (c • x) = c * mean π x := by
  simp only [mean, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem mean_single {K : ℕ} (π : Fin K → F) (i : Fin K) : mean π (Pi.single i 1) = π i := by
  simp only [mean, Pi.single_apply, mul_ite, mul_one, mul_zero]
  simp

theorem Q_mutA_isMultiA (πA : Fin KA → F) (w : SB → Fin KB → F) (u : SA) :
    LinearAlgebra.Multilinear.IsMulti (fun s => mean πA (s u) * Q q M (Function.update s u 1) w) :=
        by
  refine LinearAlgebra.Multilinear.isMulti_of (fun s p x y => ?_) (fun s p c x => ?_)
  · rcases eq_or_ne p u with rfl | hpu
    · simp only [Function.update_self, Function.update_idem, mean_add]
      ring
    · simp only [Function.update_of_ne (Ne.symm hpu), Function.update_comm hpu]
      have hadd := (Q_isMultiA q M w).add (Function.update s u 1) p x y
      rw [hadd]; ring
  · rcases eq_or_ne p u with rfl | hpu
    · simp only [Function.update_self, Function.update_idem, mean_smul]
      ring
    · simp only [Function.update_of_ne (Ne.symm hpu), Function.update_comm hpu]
      have hsm := (Q_isMultiA q M w).smul (Function.update s u 1) p c x
      rw [hsm]; ring

theorem Q_mutB_isMultiB (πB : Fin KB → F) (s : SA → Fin KA → F) (v : SB) :
    LinearAlgebra.Multilinear.IsMulti (fun w => mean πB (w v) * Q q M s (Function.update w v 1)) :=
        by
  refine LinearAlgebra.Multilinear.isMulti_of (fun w p x y => ?_) (fun w p c x => ?_)
  · rcases eq_or_ne p v with rfl | hpv
    · simp only [Function.update_self, Function.update_idem, mean_add]
      ring
    · simp only [Function.update_of_ne (Ne.symm hpv), Function.update_comm hpv]
      have hadd := (Q_isMultiB q M s).add (Function.update w v 1) p x y
      rw [hadd]; ring
  · rcases eq_or_ne p v with rfl | hpv
    · simp only [Function.update_self, Function.update_idem, mean_smul]
      ring
    · simp only [Function.update_of_ne (Ne.symm hpv), Function.update_comm hpv]
      have hsm := (Q_isMultiB q M s).smul (Function.update w v 1) p c x
      rw [hsm]; ring

end Terms

end Rhone.Probability.Multilinear
