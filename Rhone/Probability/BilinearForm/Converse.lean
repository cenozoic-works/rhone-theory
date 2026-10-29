/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.BilinearForm.Coeff

/-! # The converse for `t ≥ 2`: `q₁ ≢ 0` -/

@[expose] public section

namespace Rhone.Probability.BilinearForm

open Finset LinearAlgebra.Recursion Config Denominator

variable {KA KB : ℕ}

theorem X_add_C_ne_zero {σ : Type*} (s : σ) (c : ℚ) :
    (MvPolynomial.X s + MvPolynomial.C c : MvPolynomial σ ℚ) ≠ 0 := by
  intro h
  have e0 : MvPolynomial.eval (fun _ => (0 : ℚ))
      (MvPolynomial.X s + MvPolynomial.C c : MvPolynomial σ ℚ) = c := by simp
  have e1 : MvPolynomial.eval (fun _ => (1 : ℚ))
      (MvPolynomial.X s + MvPolynomial.C c : MvPolynomial σ ℚ) = 1 + c := by simp
  rw [h, map_zero] at e0 e1
  linarith

theorem sum_X_add_C_ne_zero {σ ι : Type*} [Fintype ι] (f : ι → σ)
    (hf : Function.Injective f) (i₀ : ι) (c : ℚ) :
    (∑ i, MvPolynomial.X (f i) + MvPolynomial.C c : MvPolynomial σ ℚ) ≠ 0 := by
  classical
  intro h
  have e0 : MvPolynomial.eval (fun _ => (0 : ℚ))
      (∑ i, MvPolynomial.X (f i) + MvPolynomial.C c : MvPolynomial σ ℚ) = c := by simp
  have e1 : MvPolynomial.eval (fun x => if x = f i₀ then (1 : ℚ) else 0)
      (∑ i, MvPolynomial.X (f i) + MvPolynomial.C c : MvPolynomial σ ℚ) = 1 + c := by
    simp only [map_add, map_sum, MvPolynomial.eval_X, MvPolynomial.eval_C]
    congr 1
    rw [Finset.sum_eq_single_of_mem i₀ (Finset.mem_univ i₀)]
    · simp
    · intro i _ hi
      simp [hf.ne hi]
  rw [h, map_zero] at e0 e1
  linarith

abbrev genRing (KA KB : ℕ) : Type := MvPolynomial (Fin KA ⊕ Fin KB) ℚ

abbrev genField (KA KB : ℕ) : Type := FractionRing (genRing KA KB)

theorem genMap_ne_zero {p : genRing KA KB} (hp : p ≠ 0) :
    algebraMap (genRing KA KB) (genField KA KB) p ≠ 0 := by
  rw [Ne, IsFractionRing.to_map_eq_zero_iff]
  exact hp

noncomputable def genA (KA KB : ℕ) (i : Fin KA) : genField KA KB :=
  algebraMap (genRing KA KB) (genField KA KB) (MvPolynomial.X (Sum.inl i))

noncomputable def genB (KA KB : ℕ) (j : Fin KB) : genField KA KB :=
  algebraMap (genRing KA KB) (genField KA KB) (MvPolynomial.X (Sum.inr j))

noncomputable def genThA (KA KB : ℕ) : genField KA KB := ∑ i, genA KA KB i

noncomputable def genThB (KA KB : ℕ) : genField KA KB := ∑ j, genB KA KB j

noncomputable def genPiA (KA KB : ℕ) (i : Fin KA) : genField KA KB :=
  genA KA KB i / genThA KA KB

noncomputable def genPiB (KA KB : ℕ) (j : Fin KB) : genField KA KB :=
  genB KA KB j / genThB KA KB

theorem genThA_eq (KA KB : ℕ) : genThA KA KB
    = algebraMap (genRing KA KB) (genField KA KB) (∑ i, MvPolynomial.X (Sum.inl i)) := by
  rw [map_sum]
  rfl

theorem genThB_eq (KA KB : ℕ) : genThB KA KB
    = algebraMap (genRing KA KB) (genField KA KB) (∑ j, MvPolynomial.X (Sum.inr j)) := by
  rw [map_sum]
  rfl

theorem genThA_add_natCast_ne_zero (hKA : 0 < KA) (r : ℕ) :
    genThA KA KB + ((r : ℕ) : genField KA KB) ≠ 0 := by
  have hpoly : (∑ i, MvPolynomial.X (Sum.inl i) + MvPolynomial.C ((r : ℕ) : ℚ)
      : genRing KA KB) ≠ 0 :=
    sum_X_add_C_ne_zero _ Sum.inl_injective ⟨0, hKA⟩ _
  have heq : genThA KA KB + ((r : ℕ) : genField KA KB)
      = algebraMap (genRing KA KB) (genField KA KB)
          (∑ i, MvPolynomial.X (Sum.inl i) + MvPolynomial.C ((r : ℕ) : ℚ)) := by
    rw [map_add, ← genThA_eq, MvPolynomial.C_eq_coe_nat, map_natCast]
  rw [heq]
  exact genMap_ne_zero hpoly

theorem genThB_add_natCast_ne_zero (hKB : 0 < KB) (r : ℕ) :
    genThB KA KB + ((r : ℕ) : genField KA KB) ≠ 0 := by
  have hpoly : (∑ j, MvPolynomial.X (Sum.inr j) + MvPolynomial.C ((r : ℕ) : ℚ)
      : genRing KA KB) ≠ 0 :=
    sum_X_add_C_ne_zero _ Sum.inr_injective ⟨0, hKB⟩ _
  have heq : genThB KA KB + ((r : ℕ) : genField KA KB)
      = algebraMap (genRing KA KB) (genField KA KB)
          (∑ j, MvPolynomial.X (Sum.inr j) + MvPolynomial.C ((r : ℕ) : ℚ)) := by
    rw [map_add, ← genThB_eq, MvPolynomial.C_eq_coe_nat, map_natCast]
  rw [heq]
  exact genMap_ne_zero hpoly

theorem genA_add_natCast_ne_zero (i : Fin KA) (r : ℕ) :
    genA KA KB i + ((r : ℕ) : genField KA KB) ≠ 0 := by
  have hpoly := X_add_C_ne_zero (Sum.inl i : Fin KA ⊕ Fin KB) ((r : ℕ) : ℚ)
  have heq : genA KA KB i + ((r : ℕ) : genField KA KB)
      = algebraMap (genRing KA KB) (genField KA KB)
          (MvPolynomial.X (Sum.inl i) + MvPolynomial.C ((r : ℕ) : ℚ)) := by
    rw [map_add, MvPolynomial.C_eq_coe_nat, map_natCast]
    rfl
  rw [heq]
  exact genMap_ne_zero hpoly

theorem genB_add_natCast_ne_zero (j : Fin KB) (r : ℕ) :
    genB KA KB j + ((r : ℕ) : genField KA KB) ≠ 0 := by
  have hpoly := X_add_C_ne_zero (Sum.inr j : Fin KA ⊕ Fin KB) ((r : ℕ) : ℚ)
  have heq : genB KA KB j + ((r : ℕ) : genField KA KB)
      = algebraMap (genRing KA KB) (genField KA KB)
          (MvPolynomial.X (Sum.inr j) + MvPolynomial.C ((r : ℕ) : ℚ)) := by
    rw [map_add, MvPolynomial.C_eq_coe_nat, map_natCast]
    rfl
  rw [heq]
  exact genMap_ne_zero hpoly

theorem genThA_ne_zero (hKA : 0 < KA) : genThA KA KB ≠ 0 := by
  have h := genThA_add_natCast_ne_zero (KB := KB) hKA 0
  simpa using h

theorem genThB_ne_zero (hKB : 0 < KB) : genThB KA KB ≠ 0 := by
  have h := genThB_add_natCast_ne_zero (KA := KA) hKB 0
  simpa using h

theorem sum_genPiA (hKA : 0 < KA) : (∑ i, genPiA KA KB i) = 1 := by
  have h1 : (∑ i, genPiA KA KB i) = (∑ i, genA KA KB i) / genThA KA KB := by
    rw [Finset.sum_div]
    rfl
  rw [h1]
  exact div_self (genThA_ne_zero hKA)

theorem sum_genPiB (hKB : 0 < KB) : (∑ j, genPiB KA KB j) = 1 := by
  have h1 : (∑ j, genPiB KA KB j) = (∑ j, genB KA KB j) / genThB KA KB := by
    rw [Finset.sum_div]
    rfl
  rw [h1]
  exact div_self (genThB_ne_zero hKB)

theorem genThA_mul_genPiA (hKA : 0 < KA) (i : Fin KA) :
    genThA KA KB * genPiA KA KB i = genA KA KB i := by
  have h := genThA_ne_zero (KB := KB) hKA
  rw [genPiA]
  field_simp

theorem genThB_mul_genPiB (hKB : 0 < KB) (j : Fin KB) :
    genThB KA KB * genPiB KA KB j = genB KA KB j := by
  have h := genThB_ne_zero (KA := KA) hKB
  rw [genPiB]
  field_simp

theorem rising_genThA_ne_zero (hKA : 0 < KA) (k : ℕ) :
    rising (genThA KA KB) k ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun r _ => genThA_add_natCast_ne_zero hKA r

theorem rising_genThB_ne_zero (hKB : 0 < KB) (k : ℕ) :
    rising (genThB KA KB) k ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun r _ => genThB_add_natCast_ne_zero hKB r

theorem rising_genA_ne_zero (i : Fin KA) (k : ℕ) :
    rising (genA KA KB i) k ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun r _ => genA_add_natCast_ne_zero i r

theorem rising_genB_ne_zero (j : Fin KB) (k : ℕ) :
    rising (genB KA KB j) k ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun r _ => genB_add_natCast_ne_zero j r

theorem qOne_genA_ne_zero (hKA : 0 < KA) (m : Fin KA → ℕ) :
    qOne (genThA KA KB) (genPiA KA KB) m ≠ 0 := by
  rw [qOne]
  refine div_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => ?_) (rising_genThA_ne_zero hKA _)
  rw [genThA_mul_genPiA hKA i]
  exact rising_genA_ne_zero i _

theorem qOne_genB_ne_zero (hKB : 0 < KB) (m : Fin KB → ℕ) :
    qOne (genThB KA KB) (genPiB KA KB) m ≠ 0 := by
  rw [qOne]
  refine div_ne_zero (Finset.prod_ne_zero_iff.mpr fun j _ => ?_) (rising_genThB_ne_zero hKB _)
  rw [genThB_mul_genPiB hKB j]
  exact rising_genB_ne_zero j _

noncomputable def dpolyA (ξ : Config KA KB) (i : Fin KA) : genRing KA KB :=
  MvPolynomial.X (Sum.inl i) + MvPolynomial.C (((ξ.mA i : ℕ) : ℚ) - 1)

noncomputable def dpolyB (ξ : Config KA KB) (j : Fin KB) : genRing KA KB :=
  MvPolynomial.X (Sum.inr j) + MvPolynomial.C (((ξ.mB j : ℕ) : ℚ) - 1)

theorem dvalA_gen (hKA : 0 < KA) (ξ : Config KA KB) (i : Fin KA) :
    dvalA (genThA KA KB) (genPiA KA KB) ξ i
      = algebraMap (genRing KA KB) (genField KA KB) (dpolyA ξ i) := by
  have hC : (MvPolynomial.C (((ξ.mA i : ℕ) : ℚ) - 1) : genRing KA KB)
      = (((ξ.mA i : ℕ)) : genRing KA KB) - 1 := by
    rw [map_sub, map_one, MvPolynomial.C_eq_coe_nat]
  rw [dpolyA, hC, map_add, map_sub, map_natCast, map_one, dvalA, genThA_mul_genPiA hKA i, genA]
  ring

theorem dvalB_gen (hKB : 0 < KB) (ξ : Config KA KB) (j : Fin KB) :
    dvalB (genThB KA KB) (genPiB KA KB) ξ j
      = algebraMap (genRing KA KB) (genField KA KB) (dpolyB ξ j) := by
  have hC : (MvPolynomial.C (((ξ.mB j : ℕ) : ℚ) - 1) : genRing KA KB)
      = (((ξ.mB j : ℕ)) : genRing KA KB) - 1 := by
    rw [map_sub, map_one, MvPolynomial.C_eq_coe_nat]
  rw [dpolyB, hC, map_add, map_sub, map_natCast, map_one, dvalB, genThB_mul_genPiB hKB j, genB]
  ring

def genPt (ξ : Config KA KB) (dA₀ : Fin KA → ℚ) (dB₀ : Fin KB → ℚ) :
    Fin KA ⊕ Fin KB → ℚ :=
  Sum.elim (fun i => dA₀ i - (((ξ.mA i : ℕ) : ℚ) - 1))
    (fun j => dB₀ j - (((ξ.mB j : ℕ) : ℚ) - 1))

theorem eval_dpolyA (ξ : Config KA KB) (dA₀ : Fin KA → ℚ) (dB₀ : Fin KB → ℚ) (i : Fin KA) :
    MvPolynomial.eval (genPt ξ dA₀ dB₀) (dpolyA ξ i) = dA₀ i := by
  simp [genPt, dpolyA]

theorem eval_dpolyB (ξ : Config KA KB) (dA₀ : Fin KA → ℚ) (dB₀ : Fin KB → ℚ) (j : Fin KB) :
    MvPolynomial.eval (genPt ξ dA₀ dB₀) (dpolyB ξ j) = dB₀ j := by
  simp [genPt, dpolyB]

theorem Pgen_dpoly_ne_zero (hKA : 2 ≤ KA) (hKB : 2 ≤ KB) (ξ : Config KA KB) (ht : 2 ≤ ξ.t) :
    LinearAlgebra.BilinearForm.Pgen (wt0 ξ) (wtA ξ) (wtB ξ) (wtAB ξ) (dpolyA ξ) (dpolyB ξ) ≠
        (0 : genRing KA KB) := by
  obtain ⟨dA₀, dB₀, hne⟩ := exists_Pgen_ne_zero hKA hKB ξ ht
  intro h0
  apply hne
  have hev := LinearAlgebra.BilinearForm.map_Pgen (MvPolynomial.eval (genPt ξ dA₀ dB₀))
    (wt0 ξ) (wtA ξ) (wtB ξ) (wtAB ξ) (dpolyA ξ) (dpolyB ξ)
  rw [h0, map_zero] at hev
  rw [funext (eval_dpolyA ξ dA₀ dB₀), funext (eval_dpolyB ξ dA₀ dB₀)] at hev
  exact hev.symm

theorem twoQ1_gen_ne_zero (hKA : 2 ≤ KA) (hKB : 2 ≤ KB) (ξ : Config KA KB) (ht : 2 ≤ ξ.t) :
    twoQ1 (genThA KA KB) (genThB KA KB) (genPiA KA KB) (genPiB KA KB) ξ ≠ 0 := by
  have hA0 : 0 < KA := by omega
  have hB0 : 0 < KB := by omega
  have hPg : LinearAlgebra.BilinearForm.Pgen (wt0 ξ) (wtA ξ) (wtB ξ) (wtAB ξ)
      (dvalA (genThA KA KB) (genPiA KA KB) ξ)
      (dvalB (genThB KA KB) (genPiB KA KB) ξ) ≠ 0 := by
    have hmap := LinearAlgebra.BilinearForm.map_Pgen (algebraMap (genRing KA KB) (genField KA KB))
      (wt0 ξ) (wtA ξ) (wtB ξ) (wtAB ξ) (dpolyA ξ) (dpolyB ξ)
    have hEA : (fun i => algebraMap (genRing KA KB) (genField KA KB) (dpolyA ξ i))
        = dvalA (genThA KA KB) (genPiA KA KB) ξ :=
      funext fun i => (dvalA_gen hA0 ξ i).symm
    have hEB : (fun j => algebraMap (genRing KA KB) (genField KA KB) (dpolyB ξ j))
        = dvalB (genThB KA KB) (genPiB KA KB) ξ :=
      funext fun j => (dvalB_gen hB0 ξ j).symm
    rw [hEA, hEB] at hmap
    rw [← hmap]
    exact genMap_ne_zero (Pgen_dpoly_ne_zero hKA hKB ξ ht)
  intro hzero
  have hfac := twoQ1_mul_prodAll (sum_genPiA hA0) (sum_genPiB hB0) ξ
    (rising_genThA_ne_zero hA0 ξ.nA) (rising_genThB_ne_zero hB0 ξ.nB)
  rw [hzero, zero_mul] at hfac
  exact mul_ne_zero (mul_ne_zero (qOne_genA_ne_zero hA0 ξ.mA) (qOne_genB_ne_zero hB0 ξ.mB))
    hPg hfac.symm

theorem exists_ne_qHat_of_twoQ1_ne_zero {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}
    (hθA : 0 < θA) (hθB : 0 < θB) {q : Config KA KB → F}
    (hq : IsSolution θA θB ρ πA πB q) (ξ : Config KA KB) (hn : 2 ≤ ξ.n)
    (hsrc : twoQ1 θA θB πA πB ξ ≠ 0) :
    ∃ η : Config KA KB, q η ≠ qHat θA θB πA πB η := by
  by_contra hcon
  simp only [not_exists, ne_eq, not_not] at hcon
  have hfun : q = qHat θA θB πA πB := funext hcon
  have h1 := hq.recursion ξ hn
  rw [hfun] at h1
  have h2 := source_identity (ρ := ρ) (πA := πA) (πB := πB) hθA hθB ξ
  exact hsrc (by linarith [h1, h2])

end Rhone.Probability.BilinearForm
