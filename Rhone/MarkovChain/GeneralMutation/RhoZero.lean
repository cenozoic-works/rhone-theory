/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.GeneralMutation.OneLocusG
public import Rhone.MarkovChain.GeneralMutation.PIM

/-! # One-locus reduction of the two-locus recursion at `ρ = 0` for general mutation -/

@[expose] public section

namespace Rhone.MarkovChain.GeneralMutation

open Finset LinearAlgebra.Recursion

variable {KA KB : ℕ} {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB : F} {νA : Fin KA → F} {νB : Fin KB → F}
variable {PA : Fin KA → Fin KA → F} {PB : Fin KB → Fin KB → F}

def full (m : Fin KA × Fin KB → ℕ) : Config KA KB :=
  ⟨fun _ => 0, fun _ => 0, fun i j => m (i, j)⟩

section Sector

variable (m : Fin KA × Fin KB → ℕ) (i : Fin KA) (j : Fin KB)

@[simp] theorem a_full : (full m).a i = 0 := rfl
@[simp] theorem b_full : (full m).b j = 0 := rfl
@[simp] theorem c_full : (full m).c i j = m (i, j) := rfl
@[simp] theorem sumA_full : (full m).sumA = 0 := by simp [Config.sumA, full]
@[simp] theorem sumB_full : (full m).sumB = 0 := by simp [Config.sumB, full]

theorem t_full : (full m).t = ∑ x, m x := by
  simp only [Config.t, full]
  rw [← Fintype.sum_prod_type]

theorem n_full : (full m).n = ∑ x, m x := by
  simp only [Config.n, sumA_full, sumB_full, t_full]
  omega

theorem nA_full : (full m).nA = ∑ x, m x := by
  simp only [Config.nA, sumA_full, t_full]; omega

theorem nB_full : (full m).nB = ∑ x, m x := by
  simp only [Config.nB, sumB_full, t_full]; omega

theorem full_zero : full (fun _ => 0) = (0 : Config KA KB) := rfl

theorem full_incf : full (incf (fun _ => 0) (i, j)) = Config.eC i j := by
  refine Config.ext rfl rfl ?_
  funext i' j'
  change incf (fun _ => (0 : ℕ)) (i, j) (i', j') = Config.incC (fun _ _ => 0) i j i' j'
  rw [Probability.Denominator.incf_apply, Probability.Denominator.incC_apply]
  by_cases h1 : i' = i <;> by_cases h2 : j' = j <;> simp_all [Prod.ext_iff]

theorem dropC_full : (full m).dropC i j = full (decf m (i, j)) := by
  refine Config.ext rfl rfl ?_
  funext i' j'
  change Config.decC (fun i j => m (i, j)) i j i' j' = decf m (i, j) (i', j')
  rw [Probability.Denominator.decC_apply, Probability.Denominator.decf_apply]
  by_cases h1 : i' = i <;> by_cases h2 : j' = j <;> simp_all [Prod.ext_iff]

theorem mutCA_full (k : Fin KA) :
    mutCA (full m) i j k = full (incf (decf m (i, j)) (k, j)) := by
  refine Config.ext rfl rfl ?_
  funext i' j'
  change Config.incC (Config.decC (fun i j => m (i, j)) i j) k j i' j'
    = incf (decf m (i, j)) (k, j) (i', j')
  rw [Probability.Denominator.incC_apply, Probability.Denominator.decC_apply,
      Probability.Denominator.incf_apply, Probability.Denominator.decf_apply]
  by_cases h1 : i' = i <;> by_cases h2 : j' = j <;> by_cases h3 : i' = k <;>
    simp_all [Prod.ext_iff]

theorem mutCB_full (l : Fin KB) :
    mutCB (full m) i j l = full (incf (decf m (i, j)) (i, l)) := by
  refine Config.ext rfl rfl ?_
  funext i' j'
  change Config.incC (Config.decC (fun i j => m (i, j)) i j) i l i' j'
    = incf (decf m (i, j)) (i, l) (i', j')
  rw [Probability.Denominator.incC_apply, Probability.Denominator.decC_apply,
      Probability.Denominator.incf_apply, Probability.Denominator.decf_apply]
  by_cases h1 : i' = i <;> by_cases h2 : j' = j <;> by_cases h3 : j' = l <;>
    simp_all [Prod.ext_iff]

end Sector

def prodMat (θA θB : F) (PA : Fin KA → Fin KA → F) (PB : Fin KB → Fin KB → F) :
    (Fin KA × Fin KB) → (Fin KA × Fin KB) → F := fun y x =>
  (θA * (if y.2 = x.2 then PA y.1 x.1 else 0) + θB * (if y.1 = x.1 then PB y.2 x.2 else 0))
    / (θA + θB)

def prodNu (νA : Fin KA → F) (νB : Fin KB → F) : Fin KA × Fin KB → F :=
  fun x => νA x.1 * νB x.2

theorem prodNu_pos (hνA : ∀ i, 0 < νA i) (hνB : ∀ j, 0 < νB j) (x : Fin KA × Fin KB) :
    0 < prodNu νA νB x := mul_pos (hνA x.1) (hνB x.2)

theorem prodMat_nonneg (hθA : 0 < θA) (hθB : 0 < θB)
    (hPA : ∀ k i, 0 ≤ PA k i) (hPB : ∀ l j, 0 ≤ PB l j) (y x : Fin KA × Fin KB) :
    0 ≤ prodMat θA θB PA PB y x := by
  have hs : 0 < θA + θB := by linarith
  refine div_nonneg ?_ hs.le
  have h1 : (0 : F) ≤ θA * (if y.2 = x.2 then PA y.1 x.1 else 0) := by
    split_ifs with h
    · exact mul_nonneg hθA.le (hPA _ _)
    · simp
  have h2 : (0 : F) ≤ θB * (if y.1 = x.1 then PB y.2 x.2 else 0) := by
    split_ifs with h
    · exact mul_nonneg hθB.le (hPB _ _)
    · simp
  linarith

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem prodMat_row_sum (hθ : θA + θB ≠ 0) (hPA : ∀ k, ∑ i, PA k i = 1)
    (hPB : ∀ l, ∑ j, PB l j = 1) (y : Fin KA × Fin KB) :
    ∑ x, prodMat θA θB PA PB y x = 1 := by
  rw [Fintype.sum_prod_type]
  have hterm : ∀ (i : Fin KA) (j : Fin KB),
      prodMat θA θB PA PB y (i, j)
        = (θA * (if y.2 = j then PA y.1 i else 0)
            + θB * (if y.1 = i then PB y.2 j else 0)) / (θA + θB) := fun i j => rfl
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hterm i j]
  have h1 : ∀ i : Fin KA, (∑ j, (θA * (if y.2 = j then PA y.1 i else 0)
      + θB * (if y.1 = i then PB y.2 j else 0)) / (θA + θB))
      = (θA * PA y.1 i + θB * (if y.1 = i then 1 else 0)) / (θA + θB) := by
    intro i
    rw [← Finset.sum_div]
    congr 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    congr 2
    · rw [Finset.sum_ite_eq Finset.univ y.2 (fun _ => PA y.1 i)]
      simp
    · by_cases h : y.1 = i
      · simp only [ite_eq_left h]
        rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => rfl, hPB y.2]
      · simp [h]
  rw [Finset.sum_congr rfl fun i _ => h1 i, ← Finset.sum_div, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hPA y.1, Finset.sum_ite_eq Finset.univ y.1 (fun _ => (1:F))]
  simp only [Finset.mem_univ, ite_true]
  field_simp

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem prodMat_stationary (hθ : θA + θB ≠ 0)
    (hstA : ∀ i, ∑ k, νA k * PA k i = νA i) (hstB : ∀ j, ∑ l, νB l * PB l j = νB j)
    (x : Fin KA × Fin KB) :
    ∑ y, prodNu νA νB y * prodMat θA θB PA PB y x = prodNu νA νB x := by
  rw [Fintype.sum_prod_type]
  have hterm : ∀ (k : Fin KA) (l : Fin KB),
      prodNu νA νB (k, l) * prodMat θA θB PA PB (k, l) x
        = (θA * ((if l = x.2 then νA k * PA k x.1 * νB l else 0))
            + θB * ((if k = x.1 then νA k * (νB l * PB l x.2) else 0))) / (θA + θB) := by
    intro k l
    rw [prodMat, prodNu]
    field_simp
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => hterm k l]
  have h1 : ∀ k : Fin KA, (∑ l, (θA * ((if l = x.2 then νA k * PA k x.1 * νB l else 0))
      + θB * ((if k = x.1 then νA k * (νB l * PB l x.2) else 0))) / (θA + θB))
      = (θA * (νA k * PA k x.1 * νB x.2) + θB * (if k = x.1 then νA k * νB x.2 else 0))
        / (θA + θB) := by
    intro k
    rw [← Finset.sum_div]
    congr 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    congr 2
    · exact Finset.sum_ite_eq' Finset.univ x.2 (fun l => νA k * PA k x.1 * νB l) ▸ by simp
    · by_cases h : k = x.1
      · simp only [ite_eq_left h, ← Finset.mul_sum, hstB x.2]
      · simp [h]
  rw [Finset.sum_congr rfl fun k _ => h1 k, ← Finset.sum_div, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]
  have hA : (∑ k, νA k * PA k x.1 * νB x.2) = νA x.1 * νB x.2 := by
    rw [← Finset.sum_mul, hstA x.1]
  have hB : (∑ k, if k = x.1 then νA k * νB x.2 else 0) = νA x.1 * νB x.2 :=
    Finset.sum_ite_eq' Finset.univ x.1 (fun k => νA k * νB x.2) ▸ by simp
  rw [hA, hB, prodNu]
  field_simp

theorem isSolutionOneG_of_rho_zero (hθA : 0 < θA) (hθB : 0 < θB)
    {q : Config KA KB → F} (hq : IsSolutionGen θA θB 0 νA νB PA PB q) :
    IsSolutionOneG (θA + θB) (prodNu νA νB) (prodMat θA θB PA PB) (fun m => q (full m)) where
  empty := by rw [full_zero]; exact hq.empty
  bdry x := by
    obtain ⟨i, j⟩ := x
    rw [full_incf, hq.bdryC]
    rfl
  recursion m hm := by
    have hne : θA + θB ≠ 0 := by positivity
    have hn : 2 ≤ (full m).n := by rw [n_full]; exact hm
    have hrec := hq.recursion (full m) hn
    have hd : diag θA θB (0 : F) (full m)
        = (((∑ x, m x) * ((∑ x, m x) - 1) : ℕ) : F) + (θA + θB) * ((∑ x, m x : ℕ) : F) := by
      simp only [LinearAlgebra.Recursion.diag, n_full, nA_full, nB_full, t_full]
      ring
    have z1 : (∑ i, (((full m).coalA i : ℕ) : F) * q ((full m).dropA i)) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      simp [Config.coalA]
    have z2 : (∑ j, (((full m).coalB j : ℕ) : F) * q ((full m).dropB j)) = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      simp [Config.coalB]
    have z3 : (∑ i, ∑ j, (((full m).coalAB i j : ℕ) : F) * q ((full m).mergeAB i j)) = 0 := by
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      simp [Config.coalAB]
    have z4 : (∑ i, ∑ k, PA k i * (((full m).a i : ℕ) : F) * q (mutA (full m) i k)) = 0 := by
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun k _ => ?_
      simp
    have z5 : (∑ j, ∑ l, PB l j * (((full m).b j : ℕ) : F) * q (mutB (full m) j l)) = 0 := by
      refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun l _ => ?_
      simp
    have hcoal : (∑ i, ∑ j, (((full m).coalC i j : ℕ) : F) * q ((full m).dropC i j))
        = ∑ x, ((m x * (m x - 1) : ℕ) : F) * q (full (decf m x)) := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [dropC_full]
      rfl
    have hmut : (θA + θB) * ∑ x, ∑ y, prodMat θA θB PA PB y x * ((m x : ℕ) : F)
          * q (full (incf (decf m x) y))
        = θA * (∑ i, ∑ j, ∑ k, PA k i * (((full m).c i j : ℕ) : F) * q (mutCA (full m) i j k))
          + θB * (∑ i, ∑ j, ∑ l, PB l j * (((full m).c i j : ℕ) : F)
              * q (mutCB (full m) i j l)) := by
      have hx : ∀ x : Fin KA × Fin KB, (θA + θB) * ∑ y, prodMat θA θB PA PB y x
            * ((m x : ℕ) : F) * q (full (incf (decf m x) y))
          = θA * (∑ k, PA k x.1 * ((m x : ℕ) : F) * q (full (incf (decf m x) (k, x.2))))
            + θB * (∑ l, PB l x.2 * ((m x : ℕ) : F)
                * q (full (incf (decf m x) (x.1, l)))) := by
        intro x
        rw [Finset.mul_sum, Fintype.sum_prod_type]
        have hterm : ∀ (k : Fin KA) (l : Fin KB),
            (θA + θB) * (prodMat θA θB PA PB (k, l) x * ((m x : ℕ) : F)
              * q (full (incf (decf m x) (k, l))))
            = (if l = x.2 then θA * (PA k x.1 * ((m x : ℕ) : F)
                  * q (full (incf (decf m x) (k, l)))) else 0)
              + (if k = x.1 then θB * (PB l x.2 * ((m x : ℕ) : F)
                  * q (full (incf (decf m x) (k, l)))) else 0) := by
          intro k l
          rw [prodMat]
          field_simp
          split_ifs <;> ring
        rw [Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => hterm k l]
        rw [Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) => Finset.sum_add_distrib]
        rw [Finset.sum_add_distrib]
        congr 1
        · rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_ite_eq' Finset.univ x.2 (fun l => θA * (PA k x.1 * ((m x : ℕ) : F)
            * q (full (incf (decf m x) (k, l)))))]
          simp
        · rw [Finset.sum_eq_single_of_mem x.1 (Finset.mem_univ x.1)]
          · rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun l _ => ?_
            simp
          · intro k _ hk
            exact Finset.sum_eq_zero fun l _ => ite_eq_right hk
      rw [Finset.mul_sum, Finset.sum_congr rfl fun x (_ : x ∈ Finset.univ) => hx x,
        Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      congr 1
      · congr 1
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun k _ => ?_
        rw [mutCA_full]
        rfl
      · congr 1
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun l _ => ?_
        rw [mutCB_full]
        rfl
    rw [hd] at hrec
    rw [hrec, rhsGen, z1, z2, z3, z4, z5]
    rw [hcoal]
    rw [hmut]
    ring

theorem eq_of_isSolutionOneG_rho_zero (hθA : 0 < θA) (hθB : 0 < θB)
    (hPA : ∀ k i, 0 ≤ PA k i) (hPB : ∀ l j, 0 ≤ PB l j)
    (hνA : ∀ i, 0 < νA i) (hνB : ∀ j, 0 < νB j)
    (hstA : ∀ i, ∑ k, νA k * PA k i = νA i) (hstB : ∀ j, ∑ l, νB l * PB l j = νB j)
    {q : Config KA KB → F} (hq : IsSolutionGen θA θB 0 νA νB PA PB q)
    {f : (Fin KA × Fin KB → ℕ) → F}
    (hf : IsSolutionOneG (θA + θB) (prodNu νA νB) (prodMat θA θB PA PB) f) :
    f = fun m => q (full m) := by
  have hne : θA + θB ≠ 0 := by positivity
  exact IsSolutionOneG.unique (by linarith) (prodMat_nonneg hθA hθB hPA hPB)
    (prodNu_pos hνA hνB) (prodMat_stationary hne hstA hstB) hf
    (isSolutionOneG_of_rho_zero hθA hθB hq)

theorem isSolutionOneG_q_rho_zero (hθA : 0 < θA) (hθB : 0 < θB)
    (hπA : ∑ i, νA i = 1) (hπB : ∑ j, νB j = 1) :
    IsSolutionOneG (θA + θB) (prodNu νA νB) (prodMat θA θB (pimMat νA) (pimMat νB))
      (fun m => LinearAlgebra.Recursion.q (πA := νA) (πB := νB) hθA hθB le_rfl (full m)) :=
  isSolutionOneG_of_rho_zero hθA hθB
    (IsSolution.isSolutionGen hθA hθB le_rfl hπA hπB
      (LinearAlgebra.Recursion.q_isSolution (πA := νA) (πB := νB) hθA hθB le_rfl))

end Rhone.MarkovChain.GeneralMutation
