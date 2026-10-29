/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.RecombinationExpansion.Sigma

/-! # Closed form for the `σ` coefficients -/

@[expose] public section

namespace Rhone.Probability.RecombinationExpansion

open LinearAlgebra.Recursion LinearAlgebra.Recursion.Config Analysis.RecombinationExpansion

theorem nat_absorb (n k : ℕ) :
    (n + 1) * Nat.choose n k = (n + 1 - k) * Nat.choose (n + 1) k :=
  (Nat.mul_comm _ _).trans ((Nat.choose_mul_succ_eq n k).trans (Nat.mul_comm _ _))

theorem sum_sub_eq {ι : Type*} [Fintype ι] {c d : ι → ℕ} (h : ∀ p, d p ≤ c p) :
    (∑ p, (c p - d p)) + ∑ p, d p = ∑ p, c p := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun p _ => Nat.sub_add_cancel (h p)

variable {KA KB : ℕ}

def cf (ξ : Config KA KB) (p : Fin KA × Fin KB) : ℕ := ξ.c p.1 p.2

theorem t_eq_sum_cf (ξ : Config KA KB) : (∑ p : Fin KA × Fin KB, cf ξ p) = ξ.t := by
  rw [Fintype.sum_prod_type]
  rfl

def dset (ξ : Config KA KB) : Finset (Fin KA × Fin KB → ℕ) :=
  Fintype.piFinset fun p => Finset.range (cf ξ p + 1)

theorem mem_dset {ξ : Config KA KB} {d : Fin KA × Fin KB → ℕ} :
    d ∈ dset ξ ↔ ∀ p, d p ≤ cf ξ p := by
  simp only [dset, Fintype.mem_piFinset, Finset.mem_range, Nat.lt_succ_iff]

theorem cf_mem_dset (ξ : Config KA KB) : cf ξ ∈ dset ξ := mem_dset.2 fun _ => le_refl _

def cfg (ξ : Config KA KB) (d : Fin KA × Fin KB → ℕ) : Config KA KB :=
  ⟨fun i => ξ.a i + ∑ j, (ξ.c i j - d (i, j)),
   fun j => ξ.b j + ∑ i, (ξ.c i j - d (i, j)),
   fun i j => d (i, j)⟩

theorem cfg_self (ξ : Config KA KB) : cfg ξ (cf ξ) = ξ := by
  refine Config.ext ?_ ?_ rfl
  · funext i
    change ξ.a i + ∑ j, (ξ.c i j - ξ.c i j) = ξ.a i
    simp
  · funext j
    change ξ.b j + ∑ i, (ξ.c i j - ξ.c i j) = ξ.b j
    simp

section Weights

variable {F : Type*} [Field F] [CharZero F]

def wt (ξ : Config KA KB) (d : Fin KA × Fin KB → ℕ) : F :=
  ((∏ p : Fin KA × Fin KB, Nat.choose (cf ξ p) (d p) : ℕ) : F)
    / (((Nat.choose ξ.t (∑ p, d p) : ℕ) : F) * ((∑ p, d p : ℕ) : F))

def sigmaClosed (S : Config KA KB → F) (ξ : Config KA KB) : F :=
  ∑ d ∈ dset ξ, wt ξ d * S (cfg ξ d)

theorem wt_eq_zero_of_sum_eq_zero (ξ : Config KA KB) {d : Fin KA × Fin KB → ℕ}
    (h : (∑ p, d p) = 0) : (wt ξ d : F) = 0 := by
  rw [wt, h]
  simp

theorem sigmaClosed_of_t_eq_zero (S : Config KA KB → F) {ξ : Config KA KB} (ht : ξ.t = 0) :
    sigmaClosed S ξ = 0 := by
  refine Finset.sum_eq_zero fun d hd => ?_
  have hle := mem_dset.1 hd
  have hz : (∑ p, d p) = 0 := by
    refine Nat.eq_zero_of_le_zero ?_
    calc (∑ p, d p) ≤ ∑ p, cf ξ p := Finset.sum_le_sum fun p _ => hle p
      _ = 0 := by rw [t_eq_sum_cf, ht]
  rw [wt_eq_zero_of_sum_eq_zero ξ hz, zero_mul]

end Weights

theorem cf_split_self (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) :
    cf (ξ.split i j) (i, j) = ξ.c i j - 1 := by
  change decC ξ.c i j i j = ξ.c i j - 1
  rw [decC_self, decf_self]

theorem cf_split_of_ne (ξ : Config KA KB) (i : Fin KA) (j : Fin KB)
    {p : Fin KA × Fin KB} (h : p ≠ (i, j)) : cf (ξ.split i j) p = cf ξ p := by
  rcases p with ⟨i', j'⟩
  by_cases hi : i' = i
  · subst hi
    have hj : j' ≠ j := by
      intro hj; exact h (by rw [hj])
    change decC ξ.c i' j i' j' = ξ.c i' j'
    rw [decC_self, decf_of_ne _ hj]
  · change decC ξ.c i j i' j' = ξ.c i' j'
    exact decC_of_ne ξ.c j hi j'

theorem cf_split_le (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) (p : Fin KA × Fin KB) :
    cf (ξ.split i j) p ≤ cf ξ p := by
  by_cases h : p = (i, j)
  · subst h
    rw [cf_split_self]
    exact Nat.sub_le _ _
  · rw [cf_split_of_ne ξ i j h]

theorem dset_split_subset (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) :
    dset (ξ.split i j) ⊆ dset ξ := fun _ hd =>
  mem_dset.2 fun p => le_trans (mem_dset.1 hd p) (cf_split_le ξ i j p)

theorem cfg_split (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) {d : Fin KA × Fin KB → ℕ}
    (hlt : d (i, j) < ξ.c i j) :
    cfg (ξ.split i j) d = cfg ξ d := by
  refine Config.ext ?_ ?_ rfl
  · funext i'
    change incf ξ.a i i' + ∑ j', ((ξ.split i j).c i' j' - d (i', j'))
      = ξ.a i' + ∑ j', (ξ.c i' j' - d (i', j'))
    by_cases hi : i' = i
    · subst hi
      have hother : (∑ j' ∈ Finset.univ.erase j, ((ξ.split i' j).c i' j' - d (i', j')))
          = ∑ j' ∈ Finset.univ.erase j, (ξ.c i' j' - d (i', j')) :=
        Finset.sum_congr rfl fun j' hj' => by
          have hne : j' ≠ j := (Finset.mem_erase.1 hj').1
          change cf (ξ.split i' j) (i', j') - d (i', j') = cf ξ (i', j') - d (i', j')
          rw [cf_split_of_ne ξ i' j (fun hp => hne (congrArg Prod.snd hp))]
      have hcell : (ξ.split i' j).c i' j = ξ.c i' j - 1 := cf_split_self ξ i' j
      rw [sum_eq_add_erase (fun j' => (ξ.split i' j).c i' j' - d (i', j')) j,
        sum_eq_add_erase (fun j' => ξ.c i' j' - d (i', j')) j, hother, hcell, incf_self]
      omega
    · rw [incf_of_ne _ hi]
      refine congrArg (fun s => ξ.a i' + s) (Finset.sum_congr rfl fun j' _ => ?_)
      change cf (ξ.split i j) (i', j') - d (i', j') = cf ξ (i', j') - d (i', j')
      rw [cf_split_of_ne ξ i j (fun hp => hi (congrArg Prod.fst hp))]
  · funext j'
    change incf ξ.b j j' + ∑ i', ((ξ.split i j).c i' j' - d (i', j'))
      = ξ.b j' + ∑ i', (ξ.c i' j' - d (i', j'))
    by_cases hj : j' = j
    · subst hj
      have hother : (∑ i' ∈ Finset.univ.erase i, ((ξ.split i j').c i' j' - d (i', j')))
          = ∑ i' ∈ Finset.univ.erase i, (ξ.c i' j' - d (i', j')) :=
        Finset.sum_congr rfl fun i' hi' => by
          have hne : i' ≠ i := (Finset.mem_erase.1 hi').1
          change cf (ξ.split i j') (i', j') - d (i', j') = cf ξ (i', j') - d (i', j')
          rw [cf_split_of_ne ξ i j' (fun hp => hne (congrArg Prod.fst hp))]
      have hcell : (ξ.split i j').c i j' = ξ.c i j' - 1 := cf_split_self ξ i j'
      rw [sum_eq_add_erase (fun i' => (ξ.split i j').c i' j' - d (i', j')) i,
        sum_eq_add_erase (fun i' => ξ.c i' j' - d (i', j')) i, hother, hcell, incf_self]
      omega
    · rw [incf_of_ne _ hj]
      refine congrArg (fun s => ξ.b j' + s) (Finset.sum_congr rfl fun i' _ => ?_)
      change cf (ξ.split i j) (i', j') - d (i', j') = cf ξ (i', j') - d (i', j')
      rw [cf_split_of_ne ξ i j (fun hp => hj (congrArg Prod.snd hp))]

theorem prod_split_mul (ξ : Config KA KB) (i : Fin KA) (j : Fin KB)
    {d : Fin KA × Fin KB → ℕ} (hd : d ∈ dset ξ) :
    ξ.c i j * ∏ p : Fin KA × Fin KB, Nat.choose (cf (ξ.split i j) p) (d p)
      = (ξ.c i j - d (i, j)) * ∏ p : Fin KA × Fin KB, Nat.choose (cf ξ p) (d p) := by
  have hle := mem_dset.1 hd
  have hij : d (i, j) ≤ ξ.c i j := hle (i, j)
  by_cases hc : ξ.c i j = 0
  · have hdij : d (i, j) = 0 := by omega
    rw [hc, hdij]
    simp
  · have hpeel1 : Nat.choose (cf (ξ.split i j) (i, j)) (d (i, j))
        * ∏ p ∈ Finset.univ.erase (i, j), Nat.choose (cf (ξ.split i j) p) (d p)
        = ∏ p : Fin KA × Fin KB, Nat.choose (cf (ξ.split i j) p) (d p) :=
      Finset.mul_prod_erase Finset.univ
        (fun p => Nat.choose (cf (ξ.split i j) p) (d p)) (Finset.mem_univ (i, j))
    have hpeel2 : Nat.choose (cf ξ (i, j)) (d (i, j))
        * ∏ p ∈ Finset.univ.erase (i, j), Nat.choose (cf ξ p) (d p)
        = ∏ p : Fin KA × Fin KB, Nat.choose (cf ξ p) (d p) :=
      Finset.mul_prod_erase Finset.univ
        (fun p => Nat.choose (cf ξ p) (d p)) (Finset.mem_univ (i, j))
    have hrest : (∏ p ∈ Finset.univ.erase (i, j), Nat.choose (cf (ξ.split i j) p) (d p))
        = ∏ p ∈ Finset.univ.erase (i, j), Nat.choose (cf ξ p) (d p) :=
      Finset.prod_congr rfl fun p hp => by
        rw [cf_split_of_ne ξ i j (Finset.mem_erase.1 hp).1]
    obtain ⟨m, hm⟩ : ∃ m, ξ.c i j = m + 1 := ⟨ξ.c i j - 1, by omega⟩
    have habs : ξ.c i j * Nat.choose (cf (ξ.split i j) (i, j)) (d (i, j))
        = (ξ.c i j - d (i, j)) * Nat.choose (cf ξ (i, j)) (d (i, j)) := by
      have hcf : cf ξ (i, j) = ξ.c i j := rfl
      rw [cf_split_self, hcf, hm]
      simpa using nat_absorb m (d (i, j))
    rw [← hpeel1, ← hpeel2, hrest, ← Nat.mul_assoc, habs, Nat.mul_assoc]

theorem sum_prod_split (ξ : Config KA KB) {d : Fin KA × Fin KB → ℕ} (hd : d ∈ dset ξ) :
    (∑ i, ∑ j, ξ.c i j * ∏ p : Fin KA × Fin KB, Nat.choose (cf (ξ.split i j) p) (d p))
      = (ξ.t - ∑ p, d p) * ∏ p : Fin KA × Fin KB, Nat.choose (cf ξ p) (d p) := by
  have hle := mem_dset.1 hd
  have hstep : ∀ i : Fin KA, ∀ j : Fin KB,
      ξ.c i j * ∏ p : Fin KA × Fin KB, Nat.choose (cf (ξ.split i j) p) (d p)
        = (cf ξ (i, j) - d (i, j)) * ∏ p : Fin KA × Fin KB, Nat.choose (cf ξ p) (d p) :=
    fun i j => prod_split_mul ξ i j hd
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hstep i j]
  simp only [← Finset.sum_mul]
  congr 1
  have hprod : (∑ i, ∑ j, (cf ξ (i, j) - d (i, j)))
      = ∑ p : Fin KA × Fin KB, (cf ξ p - d p) :=
    (Fintype.sum_prod_type (fun p : Fin KA × Fin KB => cf ξ p - d p)).symm
  rw [hprod]
  have hcons := sum_sub_eq (c := cf ξ) (d := d) hle
  rw [t_eq_sum_cf] at hcons
  omega

theorem sum_eq_zero_iff_eq_zero {d : Fin KA × Fin KB → ℕ} :
    (∑ p, d p) = 0 ↔ ∀ p, d p = 0 := by
  constructor
  · intro h p
    exact Nat.le_zero.1 (h ▸ Finset.single_le_sum (f := d) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ p))
  · intro h
    exact Finset.sum_eq_zero fun p _ => h p

theorem eq_cf_of_sum_eq {ξ : Config KA KB} {d : Fin KA × Fin KB → ℕ} (hd : d ∈ dset ξ)
    (h : (∑ p, d p) = ξ.t) : d = cf ξ := by
  have hle := mem_dset.1 hd
  have hsum : (∑ p, (cf ξ p - d p)) + ∑ p, d p = ∑ p, cf ξ p := sum_sub_eq hle
  rw [t_eq_sum_cf, h] at hsum
  have hzero : ∀ p, cf ξ p - d p = 0 := sum_eq_zero_iff_eq_zero.1 (by omega)
  funext p
  have h1 := hzero p
  have h2 := hle p
  omega

section Identity

variable {F : Type*} [Field F] [CharZero F]

theorem cast_term (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) (d : Fin KA × Fin KB → ℕ) :
    ((ξ.c i j : ℕ) : F) * wt (ξ.split i j) d
      = ((ξ.c i j * ∏ p : Fin KA × Fin KB, Nat.choose (cf (ξ.split i j) p) (d p) : ℕ) : F)
        / (((Nat.choose (ξ.t - 1) (∑ p, d p) : ℕ) : F) * ((∑ p, d p : ℕ) : F)) := by
  by_cases hc : ξ.c i j = 0
  · rw [hc]
    simp
  · have hts : (ξ.split i j).t = ξ.t - 1 := by
      have := ξ.t_split i j hc; omega
    rw [wt, hts, Nat.cast_mul, mul_div_assoc']

theorem wt_identity (ξ : Config KA KB) (ht : ξ.t ≠ 0) {d : Fin KA × Fin KB → ℕ}
    (hd : d ∈ dset ξ) :
    ((ξ.t : ℕ) : F) * wt ξ d
      = (∑ i, ∑ j, ((ξ.c i j : ℕ) : F) * wt (ξ.split i j) d)
        + (if d = cf ξ then (1 : F) else 0) := by
  have hle := mem_dset.1 hd
  have hkt : (∑ p, d p) ≤ ξ.t := by
    have h := Finset.sum_le_sum (f := d) (g := cf ξ) fun p (_ : p ∈ Finset.univ) => hle p
    rwa [t_eq_sum_cf] at h
  have hsum : (∑ i, ∑ j, ((ξ.c i j : ℕ) : F) * wt (ξ.split i j) d)
      = (((ξ.t - ∑ p, d p) * ∏ p : Fin KA × Fin KB, Nat.choose (cf ξ p) (d p) : ℕ) : F)
        / (((Nat.choose (ξ.t - 1) (∑ p, d p) : ℕ) : F) * ((∑ p, d p : ℕ) : F)) := by
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      cast_term (F := F) ξ i j d]
    simp only [← Finset.sum_div, ← Nat.cast_sum]
    rw [sum_prod_split ξ hd]
  rw [hsum]
  rcases Nat.eq_zero_or_pos (∑ p, d p) with hk0 | hk0
  · have hne : d ≠ cf ξ := by
      intro hcontra
      exact ht (by rw [← t_eq_sum_cf, ← hcontra, hk0])
    rw [ite_eq_right hne, wt, hk0]
    simp
  · rcases Nat.lt_or_ge (∑ p, d p) ξ.t with hlt | hge
    · have hne : d ≠ cf ξ := by
        intro hcontra
        rw [hcontra, t_eq_sum_cf] at hlt
        omega
      have hc1 : (0 : ℕ) < Nat.choose ξ.t (∑ p, d p) := Nat.choose_pos hkt
      have hc2 : (0 : ℕ) < Nat.choose (ξ.t - 1) (∑ p, d p) := Nat.choose_pos (by omega)
      have hd1 : ((Nat.choose ξ.t (∑ p, d p) : ℕ) : F) * ((∑ p, d p : ℕ) : F) ≠ 0 :=
        mul_ne_zero (Nat.cast_ne_zero.2 (by omega)) (Nat.cast_ne_zero.2 (by omega))
      have hd2 : ((Nat.choose (ξ.t - 1) (∑ p, d p) : ℕ) : F) * ((∑ p, d p : ℕ) : F) ≠ 0 :=
        mul_ne_zero (Nat.cast_ne_zero.2 (by omega)) (Nat.cast_ne_zero.2 (by omega))
      have habs : ξ.t * Nat.choose (ξ.t - 1) (∑ p, d p)
          = (ξ.t - ∑ p, d p) * Nat.choose ξ.t (∑ p, d p) := by
        obtain ⟨m, hm⟩ : ∃ m, ξ.t = m + 1 := ⟨ξ.t - 1, by omega⟩
        rw [hm]
        simpa using nat_absorb m (∑ p, d p)
      have hnat : ξ.t * (∏ p : Fin KA × Fin KB, Nat.choose (cf ξ p) (d p))
            * (Nat.choose (ξ.t - 1) (∑ p, d p) * (∑ p, d p))
          = (ξ.t - ∑ p, d p) * (∏ p : Fin KA × Fin KB, Nat.choose (cf ξ p) (d p))
            * (Nat.choose ξ.t (∑ p, d p) * (∑ p, d p)) := by
        have hre : ξ.t * (∏ p : Fin KA × Fin KB, Nat.choose (cf ξ p) (d p))
              * (Nat.choose (ξ.t - 1) (∑ p, d p) * (∑ p, d p))
            = (ξ.t * Nat.choose (ξ.t - 1) (∑ p, d p))
              * ((∏ p : Fin KA × Fin KB, Nat.choose (cf ξ p) (d p)) * (∑ p, d p)) := by ring
        rw [hre, habs]
        ring
      rw [ite_eq_right hne, add_zero, wt, mul_div_assoc', div_eq_div_iff hd1 hd2]
      exact_mod_cast congrArg (fun n : ℕ => (n : F)) hnat
    · have hkeq : (∑ p, d p) = ξ.t := le_antisymm hkt hge
      have hdc : d = cf ξ := eq_cf_of_sum_eq hd hkeq
      have htF : ((ξ.t : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.2 ht
      have hprod : (∏ p : Fin KA × Fin KB, Nat.choose (cf ξ p) (d p)) = 1 := by
        rw [hdc]
        exact Finset.prod_eq_one fun p _ => Nat.choose_self _
      rw [ite_eq_left hdc, wt, hprod, hkeq, Nat.choose_self, Nat.sub_self, Nat.cast_one,
        Nat.zero_mul, Nat.cast_zero, zero_div, zero_add, one_mul, mul_one_div, div_self htF]

end Identity

section Solve

variable {F : Type*} [Field F] [CharZero F]

theorem sigmaClosed_split_eq (S : Config KA KB → F) (ξ : Config KA KB) (i : Fin KA)
    (j : Fin KB) :
    ((ξ.c i j : ℕ) : F) * sigmaClosed S (ξ.split i j)
      = ∑ d ∈ dset ξ, ((ξ.c i j : ℕ) : F) * wt (ξ.split i j) d * S (cfg ξ d) := by
  by_cases hc : ξ.c i j = 0
  · rw [hc]
    simp
  · have h1 : (∑ d ∈ dset (ξ.split i j), wt (ξ.split i j) d * S (cfg (ξ.split i j) d))
        = ∑ d ∈ dset (ξ.split i j), wt (ξ.split i j) d * S (cfg ξ d) :=
      Finset.sum_congr rfl fun d hd => by
        have hb := mem_dset.1 hd (i, j)
        rw [cf_split_self] at hb
        rw [cfg_split ξ i j (by omega)]
    have h2 : (∑ d ∈ dset (ξ.split i j), wt (ξ.split i j) d * S (cfg ξ d))
        = ∑ d ∈ dset ξ, wt (ξ.split i j) d * S (cfg ξ d) := by
      refine Finset.sum_subset (dset_split_subset ξ i j) ?_
      intro d hdxi hdnot
      have hdij : d (i, j) = ξ.c i j := by
        by_contra hne
        refine hdnot (mem_dset.2 fun p => ?_)
        by_cases hp : p = (i, j)
        · subst hp
          rw [cf_split_self]
          have hb := mem_dset.1 hdxi (i, j)
          have hcf : cf ξ (i, j) = ξ.c i j := rfl
          rw [hcf] at hb
          omega
        · rw [cf_split_of_ne ξ i j hp]
          exact mem_dset.1 hdxi p
      have hzero : (wt (ξ.split i j) d : F) = 0 := by
        have hp0 : (∏ p : Fin KA × Fin KB, Nat.choose (cf (ξ.split i j) p) (d p)) = 0 := by
          refine Finset.prod_eq_zero (Finset.mem_univ (i, j)) ?_
          rw [cf_split_self, hdij]
          exact Nat.choose_eq_zero_of_lt (by omega)
        rw [wt, hp0]
        simp
      rw [hzero, zero_mul]
    rw [sigmaClosed, h1, h2, Finset.mul_sum]
    exact Finset.sum_congr rfl fun d _ => (mul_assoc _ _ _).symm

theorem sigmaClosed_isSigma (S : Config KA KB → F) : IsSigma S (sigmaClosed S) := by
  refine ⟨fun ξ ht => sigmaClosed_of_t_eq_zero S ht, fun ξ ht => ?_⟩
  have hswap : (∑ i, ∑ j, ((ξ.c i j : ℕ) : F) * sigmaClosed S (ξ.split i j))
      = ∑ d ∈ dset ξ, (∑ i, ∑ j, ((ξ.c i j : ℕ) : F) * wt (ξ.split i j) d) * S (cfg ξ d) := by
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      sigmaClosed_split_eq S ξ i j]
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => (Finset.sum_mul _ _ _).symm
  have hterm : ∀ d ∈ dset ξ,
      (∑ i, ∑ j, ((ξ.c i j : ℕ) : F) * wt (ξ.split i j) d) * S (cfg ξ d)
        = ((ξ.t : ℕ) : F) * (wt ξ d * S (cfg ξ d))
          - (if d = cf ξ then S (cfg ξ d) else 0) := by
    intro d hd
    have h := wt_identity (F := F) ξ ht hd
    have h' : (∑ i, ∑ j, ((ξ.c i j : ℕ) : F) * wt (ξ.split i j) d)
        = ((ξ.t : ℕ) : F) * wt ξ d - (if d = cf ξ then (1 : F) else 0) :=
      eq_sub_of_add_eq h.symm
    rw [h']
    by_cases hdc : d = cf ξ
    · rw [ite_eq_left hdc, ite_eq_left hdc]; ring
    · rw [ite_eq_right hdc, ite_eq_right hdc]; ring
  have hlast : (∑ d ∈ dset ξ, if d = cf ξ then S (cfg ξ d) else 0) = S ξ := by
    rw [Finset.sum_ite_eq' (dset ξ) (cf ξ) (fun d => S (cfg ξ d)), ite_eq_left (cf_mem_dset ξ),
      cfg_self]
  have hsig : (∑ d ∈ dset ξ, wt ξ d * S (cfg ξ d)) = sigmaClosed S ξ := rfl
  rw [hswap, Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum, hlast, hsig]
  ring

theorem sigmaSol_eq_sigmaClosed (S : Config KA KB → F) : sigmaSol S = sigmaClosed S :=
  (sigmaSol_isSigma S).unique (sigmaClosed_isSigma S)

theorem sigmaClosed_L1 (S : Config KA KB → F) (hS : ∀ ξ : Config KA KB, ξ.t = 0 → S ξ = 0)
    (ξ : Config KA KB) : L1 (sigmaClosed S) ξ = S ξ :=
  (sigmaClosed_isSigma S).L1_eq hS ξ

end Solve

end Rhone.Probability.RecombinationExpansion
