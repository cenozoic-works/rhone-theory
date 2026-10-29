/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.InfiniteAlleles.Shape

/-! # The shape-pair law and the orbit-count factor -/

@[expose] public section

namespace Rhone.Probability.InfiniteAlleles

open Finset LinearAlgebra.Recursion LinearAlgebra.Recursion.Config

variable {n KA KB KA' KB' : ℕ} (S : Sample n)

theorem samePartA_repA (α : Fin n → Fin KA) : SamePartA S α (repA S α) :=
  fun _ hk _ hk' => (repA_eq_iff S α hk hk').symm

theorem samePartB_repB (β : Fin n → Fin KB) : SamePartB S β (repB S β) :=
  fun _ hk _ hk' => (repB_eq_iff S β hk hk').symm

theorem samePartA_symm {α : Fin n → Fin KA} {α' : Fin n → Fin KA'} (h : SamePartA S α α') :
    SamePartA S α' α := fun k hk k' hk' => (h k hk k' hk').symm

theorem samePartB_symm {β : Fin n → Fin KB} {β' : Fin n → Fin KB'} (h : SamePartB S β β') :
    SamePartB S β' β := fun k hk k' hk' => (h k hk k' hk').symm

theorem samePartA_refl (α : Fin n → Fin KA) : SamePartA S α α := fun _ _ _ _ => Iff.rfl

theorem samePartB_refl (β : Fin n → Fin KB) : SamePartB S β β := fun _ _ _ _ => Iff.rfl

theorem samePartA_comp {α : Fin n → Fin KA} {α' : Fin n → Fin KA'} (h : SamePartA S α α')
    (π : Equiv.Perm (Fin n)) (hA : ∀ k, k ∈ S.LA ↔ π k ∈ S.LA) :
    SamePartA S (fun k => α (π k)) fun k => α' (π k) :=
  fun k hk k' hk' => h (π k) ((hA k).mp hk) (π k') ((hA k').mp hk')

theorem samePartB_comp {β : Fin n → Fin KB} {β' : Fin n → Fin KB'} (h : SamePartB S β β')
    (π : Equiv.Perm (Fin n)) (hB : ∀ k, k ∈ S.LB ↔ π k ∈ S.LB) :
    SamePartB S (fun k => β (π k)) fun k => β' (π k) :=
  fun k hk k' hk' => h (π k) ((hB k).mp hk) (π k') ((hB k').mp hk')

theorem repA_idem (hfull : S.LA = Finset.univ) (α : Fin n → Fin KA) :
    repA S (repA S α) = repA S α := by
  funext k
  have hk : k ∈ S.LA := by rw [hfull]; exact Finset.mem_univ k
  exact (repA_congr S α (samePartA_repA S α) hk).symm

theorem repB_idem (hfull : S.LB = Finset.univ) (β : Fin n → Fin KB) :
    repB S (repB S β) = repB S β := by
  funext k
  have hk : k ∈ S.LB := by rw [hfull]; exact Finset.mem_univ k
  exact (repB_congr S β (samePartB_repB S β) hk).symm

def canonA : Finset (Fin n → Fin n) := Finset.univ.filter fun α => repA S α = α

def canonB : Finset (Fin n → Fin n) := Finset.univ.filter fun β => repB S β = β

def shapeFibA (lam : Multiset ℕ) : Finset (Fin n → Fin n) :=
  (canonA S).filter fun α => shapeA S α = lam

def shapeFibB (mu : Multiset ℕ) : Finset (Fin n → Fin n) :=
  (canonB S).filter fun β => shapeB S β = mu

def Nshape (lam : Multiset ℕ) : ℕ := (shapeFibA S lam).card

theorem mem_shapeFibB {mu : Multiset ℕ} {β : Fin n → Fin n} :
    β ∈ shapeFibB S mu ↔ repB S β = β ∧ shapeB S β = mu := by
  simp [shapeFibB, canonB]

theorem mem_shapeFibA {lam : Multiset ℕ} {α : Fin n → Fin n} :
    α ∈ shapeFibA S lam ↔ repA S α = α ∧ shapeA S α = lam := by
  simp [shapeFibA, canonA]

theorem partsA_repA (α : Fin n → Fin KA) : partsA S (repA S α) = partsA S α :=
  ((samePartA_iff_partsA S α).mp (samePartA_repA S α)).symm

theorem partsB_repB (β : Fin n → Fin KB) : partsB S (repB S β) = partsB S β := by
  refine (Finset.image_congr fun k hk => ?_).symm
  exact blkB_congr S β (samePartB_repB S β) hk

theorem repA_mem_canonA (hfull : S.LA = Finset.univ) (α : Fin n → Fin n) :
    repA S α ∈ canonA S :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, repA_idem S hfull α⟩

theorem repB_mem_canonB (hfull : S.LB = Finset.univ) (β : Fin n → Fin n) :
    repB S β ∈ canonB S :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, repB_idem S hfull β⟩

theorem repA_mem_shapeFibA (hfull : S.LA = Finset.univ) (α : Fin n → Fin n) :
    repA S α ∈ shapeFibA S (shapeA S α) :=
  Finset.mem_filter.mpr ⟨repA_mem_canonA S hfull α, (shapeA_congr S α (samePartA_repA S α)).symm⟩

theorem canonA_injOn_partsA (hfull : S.LA = Finset.univ) {α α' : Fin n → Fin n}
    (hα : α ∈ canonA S) (hα' : α' ∈ canonA S) (h : partsA S α = partsA S α') : α = α' := by
  have hcA : repA S α = α := (Finset.mem_filter.mp hα).2
  have hcA' : repA S α' = α' := (Finset.mem_filter.mp hα').2
  funext k
  have hk : k ∈ S.LA := by rw [hfull]; exact Finset.mem_univ k
  have := repA_congr S α ((samePartA_iff_partsA S α).mpr h) hk
  rw [hcA, hcA'] at this
  exact this

theorem canonB_injOn_partsB (hfull : S.LB = Finset.univ) {β β' : Fin n → Fin n}
    (hβ : β ∈ canonB S) (hβ' : β' ∈ canonB S) (h : partsB S β = partsB S β') : β = β' := by
  have hcB : repB S β = β := (Finset.mem_filter.mp hβ).2
  have hcB' : repB S β' = β' := (Finset.mem_filter.mp hβ').2
  have hsame : SamePartB S β β' := by
    refine fun k hk k' hk' => ?_
    have hb : blkB S β k = blkB S β' k := by
      have hmem : blkB S β k ∈ partsB S β' := by
        rw [← h]; exact Finset.mem_image.mpr ⟨k, hk, rfl⟩
      obtain ⟨m, hm, hmk⟩ := Finset.mem_image.mp hmem
      have hkm : k ∈ blkB S β' m := by rw [hmk]; exact mem_blkB_self S β hk
      rw [← hmk, blkB_eq_of S β' (Finset.mem_filter.mp hkm).2]
    constructor
    · intro hh
      have hmem : k' ∈ blkB S β' k := by
        rw [← hb]; exact Finset.mem_filter.mpr ⟨hk', hh.symm⟩
      exact ((Finset.mem_filter.mp hmem).2).symm
    · intro hh
      have hmem : k' ∈ blkB S β k := by
        rw [hb]; exact Finset.mem_filter.mpr ⟨hk', hh.symm⟩
      exact ((Finset.mem_filter.mp hmem).2).symm
  funext k
  have hk : k ∈ S.LB := by rw [hfull]; exact Finset.mem_univ k
  have := repB_congr S β hsame hk
  rw [hcB, hcB'] at this
  exact this

section B2

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] {θA θB ρ : F}

noncomputable def Qshape (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (lam mu : Multiset ℕ) : F :=
  ∑ α ∈ shapeFibA S lam, ∑ β ∈ shapeFibB S mu, Plab hθA hθB hρ S α β

theorem sum_shapeFibB_perm (hfullA : S.LA = Finset.univ) (hfullB : S.LB = Finset.univ)
    (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (mu : Multiset ℕ) (α : Fin n → Fin n)
    (π : Equiv.Perm (Fin n)) :
    (∑ β ∈ shapeFibB S mu, Plab hθA hθB hρ S (fun k => α (π k)) β)
      = ∑ β ∈ shapeFibB S mu, Plab hθA hθB hρ S α β := by
  have hA : ∀ k, k ∈ S.LA ↔ π k ∈ S.LA := by
    intro k; rw [hfullA]; simp
  have hB : ∀ k, k ∈ S.LB ↔ π k ∈ S.LB := by
    intro k; rw [hfullB]; simp
  have hBs : ∀ k, k ∈ S.LB ↔ π.symm k ∈ S.LB := by
    intro k; rw [hfullB]; simp
  have hmem : ∀ (σ' : Equiv.Perm (Fin n)) (hσ' : ∀ k, k ∈ S.LB ↔ σ' k ∈ S.LB)
      (γ : Fin n → Fin n), γ ∈ shapeFibB S mu →
      repB S (fun k => γ (σ' k)) ∈ shapeFibB S mu := by
    intro σ' hσ' γ hγ
    obtain ⟨_, hsh⟩ := (mem_shapeFibB S).mp hγ
    refine (mem_shapeFibB S).mpr ⟨repB_idem S hfullB _, ?_⟩
    rw [← shapeB_congr S (fun k => γ (σ' k)) (samePartB_repB S _), shapeB_perm S γ σ' hσ', hsh]
  have hinv : ∀ (u v : Equiv.Perm (Fin n)), (∀ m, u (v m) = m) →
      (∀ k, k ∈ S.LB ↔ v k ∈ S.LB) → ∀ γ : Fin n → Fin n, repB S γ = γ →
      repB S (fun k => repB S (fun m => γ (u m)) (v k)) = γ := by
    intro u v huv hv γ hcan
    have h1 : SamePartB S (fun k => repB S (fun m => γ (u m)) (v k))
        fun k => (fun m => γ (u m)) (v k) :=
      samePartB_comp S (samePartB_symm S (samePartB_repB S fun m => γ (u m))) v hv
    have h2 : (fun k => (fun m => γ (u m)) (v k)) = γ := funext fun k => congrArg γ (huv k)
    rw [h2] at h1
    funext k
    have hk : k ∈ S.LB := by rw [hfullB]; exact Finset.mem_univ k
    rw [repB_congr S _ h1 hk, hcan]
  refine Finset.sum_nbij' (i := fun β => repB S fun k => β (π.symm k))
    (j := fun γ => repB S fun k => γ (π k)) ?_ ?_ ?_ ?_ ?_
  · exact fun β hβ => hmem π.symm hBs β hβ
  · exact fun γ hγ => hmem π hB γ hγ
  · intro β hβ
    exact hinv π.symm π (fun m => by simp) hB β ((mem_shapeFibB S).mp hβ).1
  · intro γ hγ
    exact hinv π π.symm (fun m => by simp) hBs γ ((mem_shapeFibB S).mp hγ).1
  · intro β _
    have e1 : Plab hθA hθB hρ S (fun k => α (π k)) β
        = Plab hθA hθB hρ S α fun k => β (π.symm k) := by
      have hp := Plab_perm S α (fun m => β (π.symm m)) hθA hθB hρ π hA hB
      simpa using hp
    rw [e1]
    exact Plab_congr_part S α _ hθA hθB hρ (samePartA_refl S α) (samePartB_repB S _)

theorem Qshape_eq_Nshape_mul (hfullA : S.LA = Finset.univ) (hfullB : S.LB = Finset.univ)
    (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (lam mu : Multiset ℕ) {α₀ : Fin n → Fin n}
    (hα₀ : α₀ ∈ shapeFibA S lam) :
    Qshape S hθA hθB hρ lam mu
      = (Nshape S lam : F) * ∑ β ∈ shapeFibB S mu, Plab hθA hθB hρ S α₀ β := by
  refine sum_eq_card_mul_of_const _ _ α₀ fun α hα => ?_
  have hsh : shapeA S α₀ = shapeA S α := by
    rw [((mem_shapeFibA S).mp hα₀).2, ((mem_shapeFibA S).mp hα).2]
  obtain ⟨π, hπ⟩ := exists_perm_of_shapeA_eq S hfullA hsh
  have hstep : ∀ β : Fin n → Fin n,
      Plab hθA hθB hρ S α β = Plab hθA hθB hρ S (fun k => α₀ (π k)) β :=
    fun β => Plab_congr_part S α β hθA hθB hρ (samePartA_symm S hπ) (samePartB_refl S β)
  rw [Finset.sum_congr rfl fun β _ => hstep β]
  exact sum_shapeFibB_perm S hfullA hfullB hθA hθB hρ mu α₀ π

end B2

end Rhone.Probability.InfiniteAlleles
