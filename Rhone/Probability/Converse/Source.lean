/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.Converse.Reduced

/-! # The recursion source at `t = 1` factorizes -/

@[expose] public section

namespace Rhone.Probability.Converse

open Finset LinearAlgebra.Recursion LinearAlgebra.Recursion.Config Analysis.RecombinationExpansion
    RecombinationExpansion
open Analysis.RecombinationExpansion RecombinationExpansion

variable {KA KB : ℕ}

@[simp] theorem cfg0_mA (a : Fin KA → ℕ) (b : Fin KB → ℕ) : (cfg0 a b).mA = a := by
  funext i
  simp [Config.mA, Config.cRow, cfg0]

@[simp] theorem cfg0_mB (a : Fin KA → ℕ) (b : Fin KB → ℕ) : (cfg0 a b).mB = b := by
  funext j
  simp [Config.mB, Config.cCol, cfg0]

private theorem nat_mul_pred_eq_zero {x : ℕ} (h : x ≤ 1) : x * (x - 1) = 0 := by
  interval_cases x <;> rfl

abbrev cfg1 (a : Fin KA → ℕ) (b : Fin KB → ℕ) (i₀ : Fin KA) (j₀ : Fin KB) : Config KA KB :=
  (cfg0 a b).mergeAB i₀ j₀

@[simp] theorem cfg1_a (a : Fin KA → ℕ) (b : Fin KB → ℕ) (i₀ : Fin KA) (j₀ : Fin KB) :
    (cfg1 a b i₀ j₀).a = decf a i₀ := rfl

@[simp] theorem cfg1_b (a : Fin KA → ℕ) (b : Fin KB → ℕ) (i₀ : Fin KA) (j₀ : Fin KB) :
    (cfg1 a b i₀ j₀).b = decf b j₀ := rfl

@[simp] theorem cfg1_t (a : Fin KA → ℕ) (b : Fin KB → ℕ) (i₀ : Fin KA) (j₀ : Fin KB) :
    (cfg1 a b i₀ j₀).t = 1 := by
  rw [Config.t_mergeAB, cfg0_t]

theorem cfg1_c (a : Fin KA → ℕ) (b : Fin KB → ℕ) (i₀ : Fin KA) (j₀ : Fin KB)
    (i : Fin KA) (j : Fin KB) :
    (cfg1 a b i₀ j₀).c i j = if i = i₀ then (if j = j₀ then 1 else 0) else 0 := by
  by_cases hi : i = i₀
  · subst hi
    by_cases hj : j = j₀
    · subst hj
      rw [ite_eq_left rfl, ite_eq_left rfl]
      change incC (fun _ _ => (0 : ℕ)) i j i j = 1
      rw [incC, Function.update_self, incf_self]
    · rw [ite_eq_left rfl, ite_eq_right hj]
      change incC (fun _ _ => (0 : ℕ)) i j₀ i j = 0
      rw [incC, Function.update_self, incf_of_ne _ hj]
  · rw [ite_eq_right hi]
    change incC (fun _ _ => (0 : ℕ)) i₀ j₀ i j = 0
    rw [incC_of_ne _ _ hi]

theorem cfg1_cRow (a : Fin KA → ℕ) (b : Fin KB → ℕ) (i₀ : Fin KA) (j₀ : Fin KB) (i : Fin KA) :
    (cfg1 a b i₀ j₀).cRow i = if i = i₀ then 1 else 0 := by
  rw [show (cfg1 a b i₀ j₀).cRow = incf (cfg0 a b).cRow i₀ from Config.cRow_incC _ i₀ j₀]
  have hz : (cfg0 a b).cRow = fun _ => 0 := by
    funext i'
    simp [Config.cRow, cfg0]
  by_cases hi : i = i₀
  · subst hi
    rw [ite_eq_left rfl, incf_self, hz]
  · rw [ite_eq_right hi, incf_of_ne _ hi, hz]

theorem cfg1_cCol (a : Fin KA → ℕ) (b : Fin KB → ℕ) (i₀ : Fin KA) (j₀ : Fin KB) (j : Fin KB) :
    (cfg1 a b i₀ j₀).cCol j = if j = j₀ then 1 else 0 := by
  rw [show (cfg1 a b i₀ j₀).cCol = incf (cfg0 a b).cCol j₀ from Config.cCol_incC _ i₀ j₀]
  have hz : (cfg0 a b).cCol = fun _ => 0 := by
    funext j'
    simp [Config.cCol, cfg0]
  by_cases hj : j = j₀
  · subst hj
    rw [ite_eq_left rfl, incf_self, hz]
  · rw [ite_eq_right hj, incf_of_ne _ hj, hz]

theorem cfg1_mA {a : Fin KA → ℕ} (b : Fin KB → ℕ) {i₀ : Fin KA} (j₀ : Fin KB)
    (ha : a i₀ ≠ 0) : (cfg1 a b i₀ j₀).mA = a := by
  rw [Config.mA_mergeAB (cfg0 a b) j₀ ha, cfg0_mA]

theorem cfg1_mB (a : Fin KA → ℕ) {b : Fin KB → ℕ} (i₀ : Fin KA) {j₀ : Fin KB}
    (hb : b j₀ ≠ 0) : (cfg1 a b i₀ j₀).mB = b := by
  rw [Config.mB_mergeAB (cfg0 a b) i₀ hb, cfg0_mB]

theorem eq_mergeAB_of_t_eq_one (ξ : Config KA KB) {i₀ : Fin KA} {j₀ : Fin KB}
    (ht : ξ.t = 1) (hc : ξ.c i₀ j₀ = 1) : ξ = cfg1 ξ.mA ξ.mB i₀ j₀ := by
  have hczero : ∀ i j, (i ≠ i₀ ∨ j ≠ j₀) → ξ.c i j = 0 := by
    intro i j hij
    by_contra hne
    have hle : ξ.c i₀ j₀ + ξ.c i j ≤ ξ.t := by
      rw [Config.t]
      rcases hij with h | h
      · have h1 : ∑ j', ξ.c i₀ j' + ∑ j', ξ.c i j' ≤ ∑ i', ∑ j', ξ.c i' j' :=
          pair_le_sum (fun i' => ∑ j', ξ.c i' j') (Ne.symm h)
        have h2 : ξ.c i₀ j₀ ≤ ∑ j', ξ.c i₀ j' :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j₀)
        have h3 : ξ.c i j ≤ ∑ j', ξ.c i j' :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
        omega
      · by_cases hii : i = i₀
        · subst hii
          have h1 : ξ.c i j₀ + ξ.c i j ≤ ∑ j', ξ.c i j' :=
            pair_le_sum (fun j' => ξ.c i j') (Ne.symm h)
          have h2 : ∑ j', ξ.c i j' ≤ ∑ i', ∑ j', ξ.c i' j' :=
            Finset.single_le_sum (f := fun i' => ∑ j', ξ.c i' j')
              (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
          omega
        · have h1 : ∑ j', ξ.c i₀ j' + ∑ j', ξ.c i j' ≤ ∑ i', ∑ j', ξ.c i' j' :=
            pair_le_sum (fun i' => ∑ j', ξ.c i' j') (Ne.symm hii)
          have h2 : ξ.c i₀ j₀ ≤ ∑ j', ξ.c i₀ j' :=
            Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j₀)
          have h3 : ξ.c i j ≤ ∑ j', ξ.c i j' :=
            Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
          omega
    omega
  have hrow : ξ.cRow i₀ = 1 := by
    rw [Config.cRow, Finset.sum_eq_single j₀ (fun j' _ hj => hczero i₀ j' (Or.inr hj))
      (fun h => absurd (Finset.mem_univ j₀) h), hc]
  have hcol : ξ.cCol j₀ = 1 := by
    rw [Config.cCol, Finset.sum_eq_single i₀ (fun i' _ hi => hczero i' j₀ (Or.inl hi))
      (fun h => absurd (Finset.mem_univ i₀) h), hc]
  refine Config.ext ?_ ?_ ?_
  · funext i
    by_cases hi : i = i₀
    · subst hi
      change ξ.a i = decf ξ.mA i i
      rw [decf_self, Config.mA, hrow]
      omega
    · change ξ.a i = decf ξ.mA i₀ i
      rw [decf_of_ne _ hi, Config.mA]
      have : ξ.cRow i = 0 := Finset.sum_eq_zero fun j' _ => hczero i j' (Or.inl hi)
      omega
  · funext j
    by_cases hj : j = j₀
    · subst hj
      change ξ.b j = decf ξ.mB j j
      rw [decf_self, Config.mB, hcol]
      omega
    · change ξ.b j = decf ξ.mB j₀ j
      rw [decf_of_ne _ hj, Config.mB]
      have : ξ.cCol j = 0 := Finset.sum_eq_zero fun i' _ => hczero i' j (Or.inr hj)
      omega
  · funext i j
    rw [cfg1_c]
    by_cases hi : i = i₀
    · subst hi
      by_cases hj : j = j₀
      · subst hj
        rw [ite_eq_left rfl, ite_eq_left rfl, hc]
      · rw [ite_eq_left rfl, ite_eq_right hj]
        exact hczero i j (Or.inr hj)
    · rw [ite_eq_right hi]
      exact hczero i j (Or.inl hi)

section Sigma

variable {F : Type*} [Field F]

theorem sigmaOf_eq_L1_of_t_eq_one (q2 : Config KA KB → F) (ξ : Config KA KB) (ht : ξ.t = 1) :
    sigmaOf q2 ξ = L1 q2 ξ := by
  rw [← sigma_L1 q2 ξ, L1, ht]
  have hterm : ∀ i : Fin KA, ∀ j : Fin KB,
      ((ξ.c i j : ℕ) : F) * sigmaOf q2 (ξ.split i j) = 0 := by
    intro i j
    by_cases hc : ξ.c i j = 0
    · rw [hc]
      simp
    · rw [sigma_t_zero q2 (by have := ξ.t_split i j hc; omega), mul_zero]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hterm i j]
  simp

end Sigma

section TwoQ1

variable {F : Type*} [Field F]
variable {θA θB : F} {πA : Fin KA → F} {πB : Fin KB → F}

theorem L0_twoQ1_of_t_eq_one (ξ : Config KA KB) (ht : ξ.t = 1) :
    L0 θA θB πA πB (twoQ1 θA θB πA πB) ξ
      = -∑ i, ∑ j, ((ξ.coalAB i j : ℕ) : F) * twoQ1 θA θB πA πB (ξ.mergeAB i j) := by
  have hz : ∀ η : Config KA KB, η.t ≤ 1 → twoQ1 θA θB πA πB η = 0 := fun η h =>
    twoQ1_eq_zero_of_t_le_one η h
  have e0 : twoQ1 θA θB πA πB ξ = 0 := hz ξ (by omega)
  have e1 : (∑ i, ((ξ.coalA i : ℕ) : F) * twoQ1 θA θB πA πB (ξ.dropA i)) = 0 :=
    Finset.sum_eq_zero fun i _ => by
      rw [hz _ (by rw [Config.t_dropA]; omega), mul_zero]
  have e2 : (∑ j, ((ξ.coalB j : ℕ) : F) * twoQ1 θA θB πA πB (ξ.dropB j)) = 0 :=
    Finset.sum_eq_zero fun j _ => by
      rw [hz _ (by rw [Config.t_dropB]; omega), mul_zero]
  have e3 : (∑ i, ∑ j, ((ξ.coalC i j : ℕ) : F) * twoQ1 θA θB πA πB (ξ.dropC i j)) = 0 :=
    Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by
      rw [Config.coalC, nat_mul_pred_eq_zero (le_trans (c_le_t ξ i j) (le_of_eq ht))]
      simp
  have e5 : (∑ i, πA i * (((ξ.a i : ℕ) : F) * twoQ1 θA θB πA πB (ξ.dropA i)
      + ∑ j, ((ξ.c i j : ℕ) : F) * twoQ1 θA θB πA πB (ξ.killA i j))) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    have hA0 : twoQ1 θA θB πA πB (ξ.dropA i) = 0 := hz _ (by rw [Config.t_dropA]; omega)
    have hK0 : (∑ j, ((ξ.c i j : ℕ) : F) * twoQ1 θA θB πA πB (ξ.killA i j)) = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hc : ξ.c i j = 0
      · rw [hc]
        simp
      · rw [hz _ (by have := ξ.t_killA i j hc; omega), mul_zero]
    rw [hA0, mul_zero, zero_add, hK0, mul_zero]
  have e6 : (∑ j, πB j * (((ξ.b j : ℕ) : F) * twoQ1 θA θB πA πB (ξ.dropB j)
      + ∑ i, ((ξ.c i j : ℕ) : F) * twoQ1 θA θB πA πB (ξ.killB i j))) = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    have hB0 : twoQ1 θA θB πA πB (ξ.dropB j) = 0 := hz _ (by rw [Config.t_dropB]; omega)
    have hK0 : (∑ i, ((ξ.c i j : ℕ) : F) * twoQ1 θA θB πA πB (ξ.killB i j)) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases hc : ξ.c i j = 0
      · rw [hc]
        simp
      · rw [hz _ (by have := ξ.t_killB i j hc; omega), mul_zero]
    rw [hB0, mul_zero, zero_add, hK0, mul_zero]
  rw [L0, Lop, rhs, e0, e1, e2, e3, e5, e6]
  ring

theorem twoQ1_mergeAB_eval (a : Fin KA → ℕ) (b : Fin KB → ℕ) (i₀ : Fin KA) (j₀ : Fin KB)
    (ha : a i₀ ≠ 0) (hb : b j₀ ≠ 0) (k : Fin KA) (l : Fin KB)
    (hak : decf a i₀ k ≠ 0) (hbl : decf b j₀ l ≠ 0) :
    twoQ1 θA θB πA πB ((cfg1 a b i₀ j₀).mergeAB k l)
      = 2 * ((if k = i₀ then qOne θA πA a - qOne θA πA (decf a i₀) else qOne θA πA a)
          * (if l = j₀ then qOne θB πB b - qOne θB πB (decf b j₀) else qOne θB πB b)) := by
  set ζ := cfg1 a b i₀ j₀ with hζ
  set η := ζ.mergeAB k l with hη
  have hmAζ : ζ.mA = a := cfg1_mA b j₀ ha
  have hmBζ : ζ.mB = b := cfg1_mB a i₀ hb
  have hmA : η.mA = a := by rw [hη, Config.mA_mergeAB ζ l hak, hmAζ]
  have hmB : η.mB = b := by rw [hη, Config.mB_mergeAB ζ k hbl, hmBζ]
  have ht : η.t = 2 := by rw [hη, Config.t_mergeAB, hζ, cfg1_t]
  have hrow : ∀ i, η.cRow i = (if i = i₀ then 1 else 0) + (if i = k then 1 else 0) := by
    intro i
    rw [hη, show (ζ.mergeAB k l).cRow = incf ζ.cRow k from Config.cRow_incC ζ k l]
    by_cases hik : i = k
    · subst hik
      rw [incf_self, hζ, cfg1_cRow, ite_eq_left rfl]
    · rw [incf_of_ne _ hik, ite_eq_right hik, add_zero, hζ, cfg1_cRow]
  have hcol : ∀ j, η.cCol j = (if j = j₀ then 1 else 0) + (if j = l then 1 else 0) := by
    intro j
    rw [hη, show (ζ.mergeAB k l).cCol = incf ζ.cCol l from Config.cCol_incC ζ k l]
    by_cases hjl : j = l
    · subst hjl
      rw [incf_self, hζ, cfg1_cCol, ite_eq_left rfl]
    · rw [incf_of_ne _ hjl, ite_eq_right hjl, add_zero, hζ, cfg1_cCol]
  have hentry : ∀ i j, η.c i j
      = (if i = i₀ then (if j = j₀ then 1 else 0) else 0)
        + (if i = k then (if j = l then 1 else 0) else 0) := by
    intro i j
    have hzc : ζ.c i j = if i = i₀ then (if j = j₀ then 1 else 0) else 0 := by
      rw [hζ]
      exact cfg1_c a b i₀ j₀ i j
    change incC ζ.c k l i j = _
    by_cases hik : i = k
    · subst hik
      by_cases hjl : j = l
      · subst hjl
        rw [incC, Function.update_self, incf_self, hzc]
        simp
      · rw [incC, Function.update_self, incf_of_ne _ hjl, hzc]
        simp [hjl]
    · rw [incC_of_ne _ _ hik, hzc]
      simp [hik]
  have hrowsum : (∑ i, ((η.cRow i * (η.cRow i - 1) : ℕ) : F) * qOne θA πA (decf η.mA i))
      = if k = i₀ then 2 * qOne θA πA (decf a i₀) else 0 := by
    rw [hmA]
    by_cases hk : k = i₀
    · subst hk
      rw [ite_eq_left rfl, Finset.sum_eq_single k]
      · rw [hrow k]
        norm_num
      · intro i _ hik
        rw [hrow i]
        simp [hik]
      · intro h
        exact absurd (Finset.mem_univ k) h
    · rw [ite_eq_right hk]
      refine Finset.sum_eq_zero fun i _ => ?_
      have hle : η.cRow i ≤ 1 := by
        rw [hrow i]
        split_ifs <;> omega
      rw [nat_mul_pred_eq_zero hle]
      simp
  have hcolsum : (∑ j, ((η.cCol j * (η.cCol j - 1) : ℕ) : F) * qOne θB πB (decf η.mB j))
      = if l = j₀ then 2 * qOne θB πB (decf b j₀) else 0 := by
    rw [hmB]
    by_cases hl : l = j₀
    · subst hl
      rw [ite_eq_left rfl, Finset.sum_eq_single l]
      · rw [hcol l]
        norm_num
      · intro j _ hjl
        rw [hcol j]
        simp [hjl]
      · intro h
        exact absurd (Finset.mem_univ l) h
    · rw [ite_eq_right hl]
      refine Finset.sum_eq_zero fun j _ => ?_
      have hle : η.cCol j ≤ 1 := by
        rw [hcol j]
        split_ifs <;> omega
      rw [nat_mul_pred_eq_zero hle]
      simp
  have hpairsum : (∑ i, ∑ j, ((η.c i j * (η.c i j - 1) : ℕ) : F)
        * (qOne θA πA (decf η.mA i) * qOne θB πB (decf η.mB j)))
      = if k = i₀ then (if l = j₀ then
          2 * (qOne θA πA (decf a i₀) * qOne θB πB (decf b j₀)) else 0) else 0 := by
    rw [hmA, hmB]
    by_cases hk : k = i₀
    · subst hk
      by_cases hl : l = j₀
      · subst hl
        rw [ite_eq_left rfl, ite_eq_left rfl, Finset.sum_eq_single k]
        · rw [Finset.sum_eq_single l]
          · rw [hentry k l]
            norm_num
          · intro j _ hjl
            rw [hentry k j]
            simp [hjl]
          · intro h
            exact absurd (Finset.mem_univ l) h
        · intro i _ hik
          refine Finset.sum_eq_zero fun j _ => ?_
          rw [hentry i j]
          simp [hik]
        · intro h
          exact absurd (Finset.mem_univ k) h
      · rw [ite_eq_left rfl, ite_eq_right hl]
        refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
        have hle : η.c i j ≤ 1 := by
          rw [hentry i j]
          split_ifs <;> omega
        rw [nat_mul_pred_eq_zero hle]
        simp
    · rw [ite_eq_right hk]
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      have hle : η.c i j ≤ 1 := by
        rw [hentry i j]
        split_ifs <;> omega
      rw [nat_mul_pred_eq_zero hle]
      simp
  have hdiag : ((η.t * (η.t - 1) : ℕ) : F) = 2 := by rw [ht]; norm_num
  rw [twoQ1, hdiag, hrowsum, hcolsum, hpairsum, hmA, hmB]
  by_cases hk : k = i₀
  · by_cases hl : l = j₀
    · simp only [ite_eq_left hk, ite_eq_left hl]
      ring
    · simp only [ite_eq_left hk, ite_eq_right hl]
      ring
  · by_cases hl : l = j₀
    · simp only [ite_eq_right hk, ite_eq_left hl]
      ring
    · simp only [ite_eq_right hk, ite_eq_right hl]
      ring

end TwoQ1

section Bracket

variable {F : Type*} [Field F]
variable {θ : F} {π : Fin KA → F}

theorem sum_aF_eq {a : Fin KA → ℕ} {i₀ : Fin KA} (ha : a i₀ ≠ 0)
    (hden : rising θ (∑ k, a k) ≠ 0)
    (hne : θ * π i₀ + ((a i₀ : ℕ) : F) - 1 ≠ 0) :
    (∑ k, ((decf a i₀ k : ℕ) : F)
        * (if k = i₀ then qOne θ π a - qOne θ π (decf a i₀) else qOne θ π a))
      = qOne θ π a * Gcoef θ π a i₀ := by
  have hstep := qOne_step_of_ne_zero (θ := θ) (π := π) a ha hden
  have hsplit : ∀ k : Fin KA, ((decf a i₀ k : ℕ) : F)
      * (if k = i₀ then qOne θ π a - qOne θ π (decf a i₀) else qOne θ π a)
      = ((decf a i₀ k : ℕ) : F) * qOne θ π a
        - (if k = i₀ then ((decf a i₀ k : ℕ) : F) * qOne θ π (decf a i₀) else 0) := by
    intro k
    by_cases hk : k = i₀
    · rw [ite_eq_left hk, ite_eq_left hk]
      ring
    · rw [ite_eq_right hk, ite_eq_right hk]
      ring
  have hsecond : (∑ k, if k = i₀ then ((decf a i₀ k : ℕ) : F) * qOne θ π (decf a i₀) else 0)
      = ((decf a i₀ i₀ : ℕ) : F) * qOne θ π (decf a i₀) := by
    rw [Finset.sum_eq_single i₀ (fun k _ hk => ite_eq_right hk)
      (fun h => absurd (Finset.mem_univ i₀) h), ite_eq_left rfl]
  rw [Finset.sum_congr rfl fun k _ => hsplit k, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Nat.cast_sum, hsecond, decf_self]
  have hcast : ((∑ k, decf a i₀ k : ℕ) : F) = ((∑ k, a k : ℕ) : F) - 1 := by
    have h0 := sum_decf (f := a) (i := i₀) ha
    have hc : (((∑ k, decf a i₀ k) + 1 : ℕ) : F) = ((∑ k, a k : ℕ) : F) := by rw [h0]
    rw [Nat.cast_add, Nat.cast_one] at hc
    exact eq_sub_of_add_eq hc
  have hcast2 : ((a i₀ - 1 : ℕ) : F) = ((a i₀ : ℕ) : F) - 1 := by
    have hadd : ((a i₀ - 1 : ℕ) : F) + ((1 : ℕ) : F) = (((a i₀ - 1) + 1 : ℕ) : F) :=
      (Nat.cast_add _ _).symm
    rw [Nat.cast_one] at hadd
    have h1 : ((a i₀ - 1 : ℕ) : F) + 1 = ((a i₀ : ℕ) : F) := by
      rw [hadd]
      congr 1
      omega
    exact eq_sub_of_add_eq h1
  rw [hcast, hcast2, Gcoef, ← mul_div_assoc, eq_div_iff hne]
  linear_combination (-(((a i₀ : ℕ) : F) - 1)) * hstep

end Bracket

section LemmaR12

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB : F} {πA : Fin KA → F} {πB : Fin KB → F}

theorem neg_L0_twoQ1_cfg1 (hθA : 0 < θA) (hπA : ∀ i, 0 < πA i) (hθB : 0 < θB)
    (hπB : ∀ j, 0 < πB j) (a : Fin KA → ℕ) (b : Fin KB → ℕ) {i₀ : Fin KA} {j₀ : Fin KB}
    (ha : a i₀ ≠ 0) (hb : b j₀ ≠ 0) :
    -L0 θA θB πA πB (twoQ1 θA θB πA πB) (cfg1 a b i₀ j₀)
      = 4 * (qOne θA πA a * qOne θB πB b) * Gcoef θA πA a i₀ * Gcoef θB πB b j₀ := by
  set ζ := cfg1 a b i₀ j₀ with hζ
  have hdenA : rising θA (∑ k, a k) ≠ 0 := rising_ne_zero hθA _
  have hdenB : rising θB (∑ k, b k) ≠ 0 := rising_ne_zero hθB _
  have hneA : θA * πA i₀ + ((a i₀ : ℕ) : F) - 1 ≠ 0 := by
    have h1 : (0 : F) < θA * πA i₀ := mul_pos hθA (hπA i₀)
    have h2 : (1 : F) ≤ ((a i₀ : ℕ) : F) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 ha
    exact ne_of_gt (by linarith)
  have hneB : θB * πB j₀ + ((b j₀ : ℕ) : F) - 1 ≠ 0 := by
    have h1 : (0 : F) < θB * πB j₀ := mul_pos hθB (hπB j₀)
    have h2 : (1 : F) ≤ ((b j₀ : ℕ) : F) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 hb
    exact ne_of_gt (by linarith)
  rw [L0_twoQ1_of_t_eq_one ζ (by rw [hζ, cfg1_t]), neg_neg]
  have hterm : ∀ k : Fin KA, ∀ l : Fin KB,
      ((ζ.coalAB k l : ℕ) : F) * twoQ1 θA θB πA πB (ζ.mergeAB k l)
        = 4 * ((((decf a i₀ k : ℕ) : F)
              * (if k = i₀ then qOne θA πA a - qOne θA πA (decf a i₀) else qOne θA πA a))
            * (((decf b j₀ l : ℕ) : F)
              * (if l = j₀ then qOne θB πB b - qOne θB πB (decf b j₀) else qOne θB πB b))) := by
    intro k l
    have hcoal : ζ.coalAB k l = 2 * (decf a i₀ k * decf b j₀ l) := rfl
    by_cases hak : decf a i₀ k = 0
    · rw [hcoal, hak]
      simp
    by_cases hbl : decf b j₀ l = 0
    · rw [hcoal, hbl]
      simp
    · rw [hcoal, twoQ1_mergeAB_eval a b i₀ j₀ ha hb k l hak hbl]
      push_cast
      ring
  rw [Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => hterm k l]
  have hin : ∀ k : Fin KA,
      (∑ l, 4 * ((((decf a i₀ k : ℕ) : F)
            * (if k = i₀ then qOne θA πA a - qOne θA πA (decf a i₀) else qOne θA πA a))
          * (((decf b j₀ l : ℕ) : F)
            * (if l = j₀ then qOne θB πB b - qOne θB πB (decf b j₀) else qOne θB πB b))))
        = (4 * (qOne θB πB b * Gcoef θB πB b j₀)) * (((decf a i₀ k : ℕ) : F)
            * (if k = i₀ then qOne θA πA a - qOne θA πA (decf a i₀) else qOne θA πA a)) := by
    intro k
    rw [← sum_aF_eq (θ := θB) (π := πB) hb hdenB hneB, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [Finset.sum_congr rfl fun k _ => hin k, ← Finset.mul_sum,
    sum_aF_eq (θ := θA) (π := πA) ha hdenA hneA]
  ring

theorem sigma_cfg1_eq (hθA : 0 < θA) (hπA : ∀ i, 0 < πA i) (hθB : 0 < θB)
    (hπB : ∀ j, 0 < πB j) {q2 : Config KA KB → F} (a : Fin KA → ℕ) (b : Fin KB → ℕ)
    {i₀ : Fin KA} {j₀ : Fin KB} (ha : a i₀ ≠ 0) (hb : b j₀ ≠ 0)
    (hL1 : 2 * L1 q2 (cfg1 a b i₀ j₀)
      = -L0 θA θB πA πB (twoQ1 θA θB πA πB) (cfg1 a b i₀ j₀)) :
    sigmaOf q2 (cfg1 a b i₀ j₀)
      = 2 * (qOne θA πA a * qOne θB πB b) * Gcoef θA πA a i₀ * Gcoef θB πB b j₀ := by
  rw [sigmaOf_eq_L1_of_t_eq_one q2 _ (cfg1_t a b i₀ j₀)]
  have h := neg_L0_twoQ1_cfg1 hθA hπA hθB hπB a b ha hb
  rw [h] at hL1
  linarith [hL1]

theorem sigma_t_one_eq (hθA : 0 < θA) (hπA : ∀ i, 0 < πA i) (hθB : 0 < θB)
    (hπB : ∀ j, 0 < πB j) {q2 : Config KA KB → F} (ξ : Config KA KB) {i₀ : Fin KA}
    {j₀ : Fin KB} (ht : ξ.t = 1) (hc : ξ.c i₀ j₀ = 1)
    (hL1 : 2 * L1 q2 ξ = -L0 θA θB πA πB (twoQ1 θA θB πA πB) ξ) :
    sigmaOf q2 ξ = 2 * (qOne θA πA ξ.mA * qOne θB πB ξ.mB)
      * Gcoef θA πA ξ.mA i₀ * Gcoef θB πB ξ.mB j₀ := by
  have hmA : ξ.mA i₀ ≠ 0 := by
    have h1 : ξ.c i₀ j₀ ≤ ξ.cRow i₀ := ξ.le_cRow i₀ j₀
    have h2 : ξ.cRow i₀ ≤ ξ.mA i₀ := Nat.le_add_left _ _
    omega
  have hmB : ξ.mB j₀ ≠ 0 := by
    have h1 : ξ.c i₀ j₀ ≤ ξ.cCol j₀ := ξ.le_cCol i₀ j₀
    have h2 : ξ.cCol j₀ ≤ ξ.mB j₀ := Nat.le_add_left _ _
    omega
  have hxi : ξ = cfg1 ξ.mA ξ.mB i₀ j₀ := eq_mergeAB_of_t_eq_one ξ ht hc
  conv_lhs => rw [hxi]
  refine sigma_cfg1_eq hθA hπA hθB hπB ξ.mA ξ.mB hmA hmB ?_
  rw [← hxi]
  exact hL1

end LemmaR12

end Rhone.Probability.Converse
