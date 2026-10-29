/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.InfiniteAlleles.Boundary

/-! # Allele relabelling: `PIA` is constant on `S_{K_A} × S_{K_B}` classes -/

@[expose] public section

namespace Rhone.Probability.InfiniteAlleles

open Finset LinearAlgebra.Recursion LinearAlgebra.Recursion.Config

variable {KA KB : ℕ}

def relabel (σ : Equiv.Perm (Fin KA)) (τ : Equiv.Perm (Fin KB)) (ξ : Config KA KB) :
    Config KA KB :=
  ⟨fun i => ξ.a (σ i), fun j => ξ.b (τ j), fun i j => ξ.c (σ i) (τ j)⟩

section Equivariance

variable (σ : Equiv.Perm (Fin KA)) (τ : Equiv.Perm (Fin KB)) (ξ : Config KA KB)

@[simp] theorem relabel_a (i : Fin KA) : (relabel σ τ ξ).a i = ξ.a (σ i) := rfl

@[simp] theorem relabel_b (j : Fin KB) : (relabel σ τ ξ).b j = ξ.b (τ j) := rfl

@[simp] theorem relabel_c (i : Fin KA) (j : Fin KB) :
    (relabel σ τ ξ).c i j = ξ.c (σ i) (τ j) := rfl

@[simp] theorem cRow_relabel (i : Fin KA) : (relabel σ τ ξ).cRow i = ξ.cRow (σ i) :=
  Equiv.sum_comp τ (fun j => ξ.c (σ i) j)

@[simp] theorem cCol_relabel (j : Fin KB) : (relabel σ τ ξ).cCol j = ξ.cCol (τ j) :=
  Equiv.sum_comp σ (fun i => ξ.c i (τ j))

@[simp] theorem mA_relabel (i : Fin KA) : (relabel σ τ ξ).mA i = ξ.mA (σ i) := by
  simp [Config.mA]

@[simp] theorem mB_relabel (j : Fin KB) : (relabel σ τ ξ).mB j = ξ.mB (τ j) := by
  simp [Config.mB]

@[simp] theorem sumA_relabel : (relabel σ τ ξ).sumA = ξ.sumA :=
  Equiv.sum_comp σ ξ.a

@[simp] theorem sumB_relabel : (relabel σ τ ξ).sumB = ξ.sumB :=
  Equiv.sum_comp τ ξ.b

@[simp] theorem t_relabel : (relabel σ τ ξ).t = ξ.t := by
  have h : ∀ i : Fin KA, (∑ j, (relabel σ τ ξ).c i j) = ξ.cRow (σ i) := cRow_relabel σ τ ξ
  calc (relabel σ τ ξ).t = ∑ i, ξ.cRow (σ i) := Finset.sum_congr rfl fun i _ => h i
    _ = ∑ i, ξ.cRow i := Equiv.sum_comp σ ξ.cRow
    _ = ξ.t := (ξ.t_eq_sum_cRow).symm

@[simp] theorem nA_relabel : (relabel σ τ ξ).nA = ξ.nA := by
  simp [Rhone.LinearAlgebra.Recursion.Config.nA]

@[simp] theorem nB_relabel : (relabel σ τ ξ).nB = ξ.nB := by
  simp [Rhone.LinearAlgebra.Recursion.Config.nB]

@[simp] theorem n_relabel : (relabel σ τ ξ).n = ξ.n := by
  simp [Rhone.LinearAlgebra.Recursion.Config.n]

theorem decf_comp_perm {ι : Type*} [DecidableEq ι] (f : ι → ℕ)
    (e : Equiv.Perm ι) (i : ι) : decf (fun k => f (e k)) i = fun k => decf f (e i) (e k) := by
  funext k
  by_cases hk : k = i
  · subst hk; simp [decf_self]
  · rw [decf_of_ne _ hk, decf_of_ne _ (fun hc => hk (e.injective hc))]

theorem incf_comp_perm {ι : Type*} [DecidableEq ι] (f : ι → ℕ)
    (e : Equiv.Perm ι) (i : ι) : incf (fun k => f (e k)) i = fun k => incf f (e i) (e k) := by
  funext k
  by_cases hk : k = i
  · subst hk; simp [incf_self]
  · rw [incf_of_ne _ hk, incf_of_ne _ (fun hc => hk (e.injective hc))]

theorem decC_comp_perm (m : Fin KA → Fin KB → ℕ) (i : Fin KA) (j : Fin KB) :
    decC (fun i' j' => m (σ i') (τ j')) i j
      = fun i' j' => decC m (σ i) (τ j) (σ i') (τ j') := by
  funext i' j'
  by_cases hi : i' = i
  · subst hi
    simp only [decC, Function.update_self]
    exact congrFun (decf_comp_perm (m (σ i')) τ j) j'
  · rw [decC, Function.update_of_ne hi, decC, Function.update_of_ne
      (fun hc => hi (σ.injective hc))]

theorem incC_comp_perm (m : Fin KA → Fin KB → ℕ) (i : Fin KA) (j : Fin KB) :
    incC (fun i' j' => m (σ i') (τ j')) i j
      = fun i' j' => incC m (σ i) (τ j) (σ i') (τ j') := by
  funext i' j'
  by_cases hi : i' = i
  · subst hi
    simp only [incC, Function.update_self]
    exact congrFun (incf_comp_perm (m (σ i')) τ j) j'
  · rw [incC, Function.update_of_ne hi, incC, Function.update_of_ne
      (fun hc => hi (σ.injective hc))]

theorem relabel_dropA (i : Fin KA) :
    (relabel σ τ ξ).dropA i = relabel σ τ (ξ.dropA (σ i)) :=
  Config.ext (decf_comp_perm ξ.a σ i) rfl rfl

theorem relabel_dropB (j : Fin KB) :
    (relabel σ τ ξ).dropB j = relabel σ τ (ξ.dropB (τ j)) :=
  Config.ext rfl (decf_comp_perm ξ.b τ j) rfl

theorem relabel_dropC (i : Fin KA) (j : Fin KB) :
    (relabel σ τ ξ).dropC i j = relabel σ τ (ξ.dropC (σ i) (τ j)) :=
  Config.ext rfl rfl (decC_comp_perm σ τ ξ.c i j)

theorem relabel_mergeAB (i : Fin KA) (j : Fin KB) :
    (relabel σ τ ξ).mergeAB i j = relabel σ τ (ξ.mergeAB (σ i) (τ j)) :=
  Config.ext (decf_comp_perm ξ.a σ i) (decf_comp_perm ξ.b τ j) (incC_comp_perm σ τ ξ.c i j)

theorem relabel_killA (i : Fin KA) (j : Fin KB) :
    (relabel σ τ ξ).killA i j = relabel σ τ (ξ.killA (σ i) (τ j)) :=
  Config.ext rfl (incf_comp_perm ξ.b τ j) (decC_comp_perm σ τ ξ.c i j)

theorem relabel_killB (i : Fin KA) (j : Fin KB) :
    (relabel σ τ ξ).killB i j = relabel σ τ (ξ.killB (σ i) (τ j)) :=
  Config.ext (incf_comp_perm ξ.a σ i) rfl (decC_comp_perm σ τ ξ.c i j)

theorem relabel_split (i : Fin KA) (j : Fin KB) :
    (relabel σ τ ξ).split i j = relabel σ τ (ξ.split (σ i) (τ j)) :=
  Config.ext (incf_comp_perm ξ.a σ i) (incf_comp_perm ξ.b τ j) (decC_comp_perm σ τ ξ.c i j)

@[simp] theorem coalA_relabel (i : Fin KA) : (relabel σ τ ξ).coalA i = ξ.coalA (σ i) := by
  simp [Config.coalA]

@[simp] theorem coalB_relabel (j : Fin KB) : (relabel σ τ ξ).coalB j = ξ.coalB (τ j) := by
  simp [Config.coalB]

@[simp] theorem coalC_relabel (i : Fin KA) (j : Fin KB) :
    (relabel σ τ ξ).coalC i j = ξ.coalC (σ i) (τ j) := by
  simp [Config.coalC]

@[simp] theorem coalAB_relabel (i : Fin KA) (j : Fin KB) :
    (relabel σ τ ξ).coalAB i j = ξ.coalAB (σ i) (τ j) := by
  simp [Config.coalAB]

@[simp] theorem dropIndA_relabel (i : Fin KA) :
    dropIndA (relabel σ τ ξ) i = dropIndA ξ (σ i) := by
  simp [dropIndA]

@[simp] theorem dropIndB_relabel (j : Fin KB) :
    dropIndB (relabel σ τ ξ) j = dropIndB ξ (τ j) := by
  simp [dropIndB]

@[simp] theorem killIndA_relabel (i : Fin KA) (j : Fin KB) :
    killIndA (relabel σ τ ξ) i j = killIndA ξ (σ i) (τ j) := by
  simp [killIndA]

@[simp] theorem killIndB_relabel (i : Fin KA) (j : Fin KB) :
    killIndB (relabel σ τ ξ) i j = killIndB ξ (σ i) (τ j) := by
  simp [killIndB]

end Equivariance

section Rec

variable {F : Type*} [CommRing F] (θA θB ρ : F)
variable (σ : Equiv.Perm (Fin KA)) (τ : Equiv.Perm (Fin KB))

@[simp] theorem relabel_zero : relabel σ τ (0 : Config KA KB) = 0 := rfl

theorem relabel_eA (i : Fin KA) :
    relabel σ τ (Config.eA i : Config KA KB) = Config.eA (σ.symm i) := by
  refine Config.ext (funext fun k => ?_) rfl rfl
  change incf (fun _ => (0 : ℕ)) i (σ k) = incf (fun _ => (0 : ℕ)) (σ.symm i) k
  by_cases hk : σ k = i
  · have hk' : k = σ.symm i := by rw [← hk]; simp
    rw [hk, hk', incf_self, incf_self]
  · rw [incf_of_ne _ hk, incf_of_ne _ (fun hc => hk (by rw [hc]; simp))]

theorem relabel_eB (j : Fin KB) :
    relabel σ τ (Config.eB j : Config KA KB) = Config.eB (τ.symm j) := by
  refine Config.ext rfl (funext fun k => ?_) rfl
  change incf (fun _ => (0 : ℕ)) j (τ k) = incf (fun _ => (0 : ℕ)) (τ.symm j) k
  by_cases hk : τ k = j
  · have hk' : k = τ.symm j := by rw [← hk]; simp
    rw [hk, hk', incf_self, incf_self]
  · rw [incf_of_ne _ hk, incf_of_ne _ (fun hc => hk (by rw [hc]; simp))]

theorem diag_relabel (ξ : Config KA KB) :
    diag θA θB ρ (relabel σ τ ξ) = diag θA θB ρ ξ := by
  simp [Rhone.LinearAlgebra.Recursion.diag]

theorem rhsIA_relabel (h : Config KA KB → F) (ξ : Config KA KB) :
    rhsIA θA θB ρ h (relabel σ τ ξ)
      = rhsIA θA θB ρ (fun η => h (relabel σ τ η)) ξ := by
  have e1 : (∑ i, (((relabel σ τ ξ).coalA i : ℕ) : F) * h ((relabel σ τ ξ).dropA i))
      = ∑ i, ((ξ.coalA i : ℕ) : F) * h (relabel σ τ (ξ.dropA i)) := by
    rw [← Equiv.sum_comp σ (fun i => ((ξ.coalA i : ℕ) : F) * h (relabel σ τ (ξ.dropA i)))]
    exact Finset.sum_congr rfl fun i _ => by rw [coalA_relabel, relabel_dropA]
  have e2 : (∑ j, (((relabel σ τ ξ).coalB j : ℕ) : F) * h ((relabel σ τ ξ).dropB j))
      = ∑ j, ((ξ.coalB j : ℕ) : F) * h (relabel σ τ (ξ.dropB j)) := by
    rw [← Equiv.sum_comp τ (fun j => ((ξ.coalB j : ℕ) : F) * h (relabel σ τ (ξ.dropB j)))]
    exact Finset.sum_congr rfl fun j _ => by rw [coalB_relabel, relabel_dropB]
  have e3 : (∑ i, ∑ j, (((relabel σ τ ξ).coalC i j : ℕ) : F) * h ((relabel σ τ ξ).dropC i j))
      = ∑ i, ∑ j, ((ξ.coalC i j : ℕ) : F) * h (relabel σ τ (ξ.dropC i j)) := by
    rw [← Equiv.sum_comp σ
      (fun i => ∑ j, ((ξ.coalC i j : ℕ) : F) * h (relabel σ τ (ξ.dropC i j)))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Equiv.sum_comp τ (fun j => ((ξ.coalC (σ i) j : ℕ) : F)
      * h (relabel σ τ (ξ.dropC (σ i) j)))]
    exact Finset.sum_congr rfl fun j _ => by rw [coalC_relabel, relabel_dropC]
  have e4 : (∑ i, ∑ j, (((relabel σ τ ξ).coalAB i j : ℕ) : F)
        * h ((relabel σ τ ξ).mergeAB i j))
      = ∑ i, ∑ j, ((ξ.coalAB i j : ℕ) : F) * h (relabel σ τ (ξ.mergeAB i j)) := by
    rw [← Equiv.sum_comp σ
      (fun i => ∑ j, ((ξ.coalAB i j : ℕ) : F) * h (relabel σ τ (ξ.mergeAB i j)))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Equiv.sum_comp τ (fun j => ((ξ.coalAB (σ i) j : ℕ) : F)
      * h (relabel σ τ (ξ.mergeAB (σ i) j)))]
    exact Finset.sum_congr rfl fun j _ => by rw [coalAB_relabel, relabel_mergeAB]
  have e5 : (∑ i, (((dropIndA (relabel σ τ ξ) i : ℕ) : F) * h ((relabel σ τ ξ).dropA i)
        + ∑ j, ((killIndA (relabel σ τ ξ) i j : ℕ) : F) * h ((relabel σ τ ξ).killA i j)))
      = ∑ i, (((dropIndA ξ i : ℕ) : F) * h (relabel σ τ (ξ.dropA i))
        + ∑ j, ((killIndA ξ i j : ℕ) : F) * h (relabel σ τ (ξ.killA i j))) := by
    rw [← Equiv.sum_comp σ (fun i => ((dropIndA ξ i : ℕ) : F) * h (relabel σ τ (ξ.dropA i))
      + ∑ j, ((killIndA ξ i j : ℕ) : F) * h (relabel σ τ (ξ.killA i j)))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [dropIndA_relabel, relabel_dropA]
    congr 1
    rw [← Equiv.sum_comp τ (fun j => ((killIndA ξ (σ i) j : ℕ) : F)
      * h (relabel σ τ (ξ.killA (σ i) j)))]
    exact Finset.sum_congr rfl fun j _ => by rw [killIndA_relabel, relabel_killA]
  have e6 : (∑ j, (((dropIndB (relabel σ τ ξ) j : ℕ) : F) * h ((relabel σ τ ξ).dropB j)
        + ∑ i, ((killIndB (relabel σ τ ξ) i j : ℕ) : F) * h ((relabel σ τ ξ).killB i j)))
      = ∑ j, (((dropIndB ξ j : ℕ) : F) * h (relabel σ τ (ξ.dropB j))
        + ∑ i, ((killIndB ξ i j : ℕ) : F) * h (relabel σ τ (ξ.killB i j))) := by
    rw [← Equiv.sum_comp τ (fun j => ((dropIndB ξ j : ℕ) : F) * h (relabel σ τ (ξ.dropB j))
      + ∑ i, ((killIndB ξ i j : ℕ) : F) * h (relabel σ τ (ξ.killB i j)))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dropIndB_relabel, relabel_dropB]
    congr 1
    rw [← Equiv.sum_comp σ (fun i => ((killIndB ξ i (τ j) : ℕ) : F)
      * h (relabel σ τ (ξ.killB i (τ j))))]
    exact Finset.sum_congr rfl fun i _ => by rw [killIndB_relabel, relabel_killB]
  have e7 : (∑ i, ∑ j, (((relabel σ τ ξ).c i j : ℕ) : F) * h ((relabel σ τ ξ).split i j))
      = ∑ i, ∑ j, ((ξ.c i j : ℕ) : F) * h (relabel σ τ (ξ.split i j)) := by
    rw [← Equiv.sum_comp σ
      (fun i => ∑ j, ((ξ.c i j : ℕ) : F) * h (relabel σ τ (ξ.split i j)))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Equiv.sum_comp τ (fun j => ((ξ.c (σ i) j : ℕ) : F)
      * h (relabel σ τ (ξ.split (σ i) j)))]
    exact Finset.sum_congr rfl fun j _ => by rw [relabel_c, relabel_split]
  simp only [rhsIA, e1, e2, e3, e4, e5, e6, e7]

end Rec

section Invariance

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] {θA θB ρ : F}

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem isSolutionIA_relabel (σ : Equiv.Perm (Fin KA)) (τ : Equiv.Perm (Fin KB))
    {q : Config KA KB → F} (h : IsSolutionIA θA θB ρ q) :
    IsSolutionIA θA θB ρ (fun ξ => q (relabel σ τ ξ)) where
  empty := by rw [relabel_zero]; exact h.empty
  bdryA i := by rw [relabel_eA]; exact h.bdryA _
  bdryB j := by rw [relabel_eB]; exact h.bdryB _
  recursion ξ hξ := by
    have hlev : 2 ≤ (relabel σ τ ξ).nA + (relabel σ τ ξ).nB := by
      rw [nA_relabel, nB_relabel]; exact hξ
    rw [← diag_relabel θA θB ρ σ τ ξ, h.recursion _ hlev, rhsIA_relabel]

theorem PIA_relabel (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (σ : Equiv.Perm (Fin KA)) (τ : Equiv.Perm (Fin KB)) (ξ : Config KA KB) :
    PIA hθA hθB hρ (relabel σ τ ξ) = PIA hθA hθB hρ ξ :=
  congrFun (PIA_unique hθA hθB hρ
    (isSolutionIA_relabel σ τ (PIA_isSolutionIA hθA hθB hρ))) ξ

end Invariance

theorem sum_eq_card_mul_of_const {X : Type*} {F : Type*} [Semiring F]
    (S : Finset X) (f : X → F) (x₀ : X) (hconst : ∀ x ∈ S, f x = f x₀) :
    ∑ x ∈ S, f x = (S.card : F) * f x₀ := by
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]

end Rhone.Probability.InfiniteAlleles
