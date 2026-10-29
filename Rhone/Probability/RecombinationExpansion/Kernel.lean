/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.RecombinationExpansion.Residual

/-! # Sector base points and the recursion evaluated at a sector base -/

@[expose] public section

namespace Rhone.Probability.RecombinationExpansion

open LinearAlgebra.Recursion LinearAlgebra.Recursion.Config Analysis.RecombinationExpansion

variable {KA KB : ℕ}

def sectorBase (ξ : Config KA KB) : Config KA KB := ⟨ξ.mA, ξ.mB, fun _ _ => 0⟩

theorem sectorBase_unique {ξ η : Config KA KB} (ht : η.t = 0) (hA : η.mA = ξ.mA)
    (hB : η.mB = ξ.mB) : η = sectorBase ξ := by
  have hc : η.c = fun _ _ => 0 := η.c_eq_zero_of_t ht
  refine Config.ext ?_ ?_ hc
  · funext i
    have h : η.a i + η.cRow i = ξ.mA i := congrFun hA i
    have hr : η.cRow i = 0 := by simp [Config.cRow, hc]
    change η.a i = ξ.mA i
    omega
  · funext j
    have h : η.b j + η.cCol j = ξ.mB j := congrFun hB j
    have hr : η.cCol j = 0 := by simp [Config.cCol, hc]
    change η.b j = ξ.mB j
    omega

@[simp] theorem t_sectorBase (ξ : Config KA KB) : (sectorBase ξ).t = 0 := by
  simp [sectorBase, Config.t]

@[simp] theorem mA_sectorBase (ξ : Config KA KB) : (sectorBase ξ).mA = ξ.mA := by
  funext i; simp [sectorBase, Config.mA, Config.cRow]

@[simp] theorem mB_sectorBase (ξ : Config KA KB) : (sectorBase ξ).mB = ξ.mB := by
  funext j; simp [sectorBase, Config.mB, Config.cCol]

theorem sectorBase_eq_self {ξ : Config KA KB} (ht : ξ.t = 0) : sectorBase ξ = ξ :=
  (sectorBase_unique ht rfl rfl).symm

theorem sectorBase_congr {ξ η : Config KA KB} (hA : ξ.mA = η.mA) (hB : ξ.mB = η.mB) :
    sectorBase ξ = sectorBase η := by
  simp only [sectorBase, hA, hB]

theorem sectorBase_split (ξ : Config KA KB) {i : Fin KA} {j : Fin KB} (h : ξ.c i j ≠ 0) :
    sectorBase (ξ.split i j) = sectorBase ξ :=
  sectorBase_congr (ξ.mA_split h) (ξ.mB_split h)

theorem sectorBase_mergeAB (ξ : Config KA KB) {i : Fin KA} {j : Fin KB} (ha : ξ.a i ≠ 0)
    (hb : ξ.b j ≠ 0) : sectorBase (ξ.mergeAB i j) = sectorBase ξ :=
  sectorBase_congr (ξ.mA_mergeAB j ha) (ξ.mB_mergeAB i hb)

section Kernel

variable {F : Type*} [Field F] [CharZero F]

theorem eq_at_sectorBase {v : Config KA KB → F} {ζ : Config KA KB}
    (hv : ∀ η : Config KA KB, η.mA = ζ.mA → η.mB = ζ.mB → L1 v η = 0) :
    ∀ n : ℕ, ∀ ξ : Config KA KB, ξ.t = n → ξ.mA = ζ.mA → ξ.mB = ζ.mB →
      v ξ = v (sectorBase ζ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ξ hn hA hB
    rcases Nat.eq_zero_or_pos n with hz | hpos
    · rw [hz] at hn
      rw [sectorBase_unique (ξ := ζ) hn hA hB]
    · have hterm : ∀ i : Fin KA, ∀ j : Fin KB,
          ((ξ.c i j : ℕ) : F) * v (ξ.split i j)
            = ((ξ.c i j : ℕ) : F) * v (sectorBase ζ) := by
        intro i j
        by_cases hc : ξ.c i j = 0
        · rw [hc]; simp
        · have hlt : (ξ.split i j).t < n := by
            have := ξ.t_split i j hc; omega
          rw [ih _ hlt (ξ.split i j) rfl (by rw [ξ.mA_split hc, hA])
            (by rw [ξ.mB_split hc, hB])]
      have hker := hv ξ hA hB
      rw [L1, Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hterm i j] at hker
      simp only [← Finset.sum_mul, ← Finset.sum_mul] at hker
      rw [show (∑ i, ∑ j, ((ξ.c i j : ℕ) : F)) = ((ξ.t : ℕ) : F) from cast_sum_c ξ] at hker
      have hne : ((ξ.t : ℕ) : F) ≠ 0 := by
        rw [hn]
        exact Nat.cast_ne_zero.2 (by omega)
      have : ((ξ.t : ℕ) : F) * (v ξ - v (sectorBase ζ)) = 0 := by linear_combination hker
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hne)

theorem ker_L1_const {v : Config KA KB → F} (hv : ∀ η : Config KA KB, L1 v η = 0)
    {ξ η : Config KA KB} (hA : ξ.mA = η.mA) (hB : ξ.mB = η.mB) : v ξ = v η := by
  have h1 := eq_at_sectorBase (ζ := ξ) (fun _ _ _ => hv _) ξ.t ξ rfl rfl rfl
  have h2 := eq_at_sectorBase (ζ := ξ) (fun _ _ _ => hv _) η.t η rfl hA.symm hB.symm
  rw [h1, h2]

theorem ker_L1_iff (v : Config KA KB → F) :
    (∀ η : Config KA KB, L1 v η = 0)
      ↔ ∀ ξ η : Config KA KB, ξ.mA = η.mA → ξ.mB = η.mB → v ξ = v η := by
  constructor
  · intro hv ξ η hA hB
    exact ker_L1_const hv hA hB
  · intro hc η
    exact L1_of_sector_const η fun i j hij => hc _ _ (η.mA_split hij) (η.mB_split hij)

theorem sub_sector_const_of_L1_eq {f g : Config KA KB → F}
    (h : ∀ η : Config KA KB, L1 f η = L1 g η) {ξ η : Config KA KB}
    (hA : ξ.mA = η.mA) (hB : ξ.mB = η.mB) : f ξ - g ξ = f η - g η := by
  have hker : ∀ ζ : Config KA KB, L1 (fun ω => f ω - g ω) ζ = 0 := by
    intro ζ
    rw [L1_sub, h ζ, sub_self]
  exact ker_L1_const hker hA hB

end Kernel

section Splitting

variable {F : Type*} [Field F]

def sigmaOf (f : Config KA KB → F) (ξ : Config KA KB) : F := f ξ - f (sectorBase ξ)

@[simp] theorem sigma_t_zero (f : Config KA KB → F) {ξ : Config KA KB} (ht : ξ.t = 0) :
    sigmaOf f ξ = 0 := by
  rw [sigmaOf, sectorBase_eq_self ht, sub_self]

theorem sigma_L1 (f : Config KA KB → F) (ξ : Config KA KB) :
    L1 (sigmaOf f) ξ = L1 f ξ := by
  have hRef : L1 (fun ω => f (sectorBase ω)) ξ = 0 :=
    L1_of_sector_const ξ fun i j hij => by rw [sectorBase_split ξ hij]
  have hfun : (sigmaOf f : Config KA KB → F)
      = fun ω => f ω - f (sectorBase ω) := rfl
  rw [hfun, L1_sub, hRef, sub_zero]

theorem sigma_split_mergeAB (f : Config KA KB → F) {ξ : Config KA KB} (ht : ξ.t = 0)
    (i : Fin KA) (j : Fin KB) (ha : ξ.a i ≠ 0) (hb : ξ.b j ≠ 0) :
    f (ξ.mergeAB i j) = f ξ + sigmaOf f (ξ.mergeAB i j) := by
  rw [sigmaOf, sectorBase_mergeAB ξ ha hb, sectorBase_eq_self ht]
  ring

theorem residual_t_zero_sigma {θA θB : F} {πA : Fin KA → F} {πB : Fin KB → F}
    {q2 : Config KA KB → F} (ξ : Config KA KB) (ht : ξ.t = 0)
    (hL0 : L0 θA θB πA πB q2 ξ = 0) :
    (((ξ.nA * (ξ.nA - 1) : ℕ) : F) + θA * ((ξ.nA : ℕ) : F)
        + ((ξ.nB * (ξ.nB - 1) : ℕ) : F) + θB * ((ξ.nB : ℕ) : F)) * q2 ξ
      = (∑ i, (((ξ.a i * (ξ.a i - 1) : ℕ) : F) + θA * πA i * ((ξ.a i : ℕ) : F))
          * q2 (ξ.dropA i))
        + (∑ j, (((ξ.b j * (ξ.b j - 1) : ℕ) : F) + θB * πB j * ((ξ.b j : ℕ) : F))
            * q2 (ξ.dropB j))
        + (∑ i, ∑ j, ((ξ.coalAB i j : ℕ) : F) * sigmaOf q2 (ξ.mergeAB i j)) :=
  residual_t_zero ξ ht hL0 fun i j ha hb => sigma_split_mergeAB q2 ht i j ha hb

end Splitting

end Rhone.Probability.RecombinationExpansion
