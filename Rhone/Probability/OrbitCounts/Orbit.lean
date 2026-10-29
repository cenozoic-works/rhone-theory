/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.InfiniteAlleles.ShapePairLaw

/-! # The closed form of the orbit-count factor `N(λ)` -/

@[expose] public section

namespace Rhone.Probability.OrbitCounts

open Finset LinearAlgebra.Recursion InfiniteAlleles

variable {n : ℕ}

section Basic

variable (S : Sample n)

theorem mAcount_eq_fibreCard (hfull : S.LA = Finset.univ) {K : ℕ} (α : Fin n → Fin K) :
    mAcount S α = fibreCard α := by
  funext i
  rw [mAcount, fibreCard, hfull]

theorem mAcount_le {K : ℕ} (α : Fin n → Fin K) (i : Fin K) : mAcount S α i ≤ n := by
  refine le_trans (Finset.card_filter_le _ _) ?_
  simpa using Finset.card_le_univ S.LA

theorem map_mAcount_eq_shapeA {K : ℕ} (α : Fin n → Fin K) (hpos : ∀ i, 0 < mAcount S α i) :
    Multiset.map (mAcount S α) Finset.univ.val = shapeA S α := by
  rw [shapeA]
  refine (Multiset.filter_eq_self.mpr fun x hx => ?_).symm
  obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hx
  exact hpos i

theorem card_used_eq_card_shapeA {K : ℕ} (α : Fin n → Fin K) :
    (Finset.univ.filter fun i => 0 < mAcount S α i).card = Multiset.card (shapeA S α) := by
  rw [shapeA, Multiset.filter_map, Multiset.card_map, ← Finset.filter_val]
  rfl

theorem samePartA_of_repA_eq {K K' : ℕ} {α : Fin n → Fin K} {α' : Fin n → Fin K'}
    (h : repA S α = repA S α') : SamePartA S α α' := by
  intro k hk k' hk'
  rw [← repA_eq_iff S α hk hk', ← repA_eq_iff S α' hk hk', h]

theorem samePartB_of_repB_eq {K K' : ℕ} {β : Fin n → Fin K} {β' : Fin n → Fin K'}
    (h : repB S β = repB S β') : SamePartB S β β' := by
  intro k hk k' hk'
  rw [← repB_eq_iff S β hk hk', ← repB_eq_iff S β' hk hk', h]

theorem exists_surj_typing (hfull : S.LA = Finset.univ) {K : ℕ} (α : Fin n → Fin K)
    {l : ℕ} (hl : Multiset.card (shapeA S α) = l) :
    ∃ γ : Fin n → Fin l, SamePartA S γ α ∧ ∀ j, 0 < mAcount S γ j := by
  classical
  have hcardU : Fintype.card ↥(Finset.univ.filter fun i => 0 < mAcount S α i) = l := by
    rw [Fintype.card_coe, card_used_eq_card_shapeA, hl]
  let e := Fintype.equivFinOfCardEq hcardU
  have hmem : ∀ k : Fin n, α k ∈ Finset.univ.filter fun i => 0 < mAcount S α i := by
    intro k
    have hk : k ∈ S.LA := by rw [hfull]; exact Finset.mem_univ k
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      Finset.card_pos.mpr ⟨k, Finset.mem_filter.mpr ⟨hk, rfl⟩⟩⟩
  refine ⟨fun k => e ⟨α k, hmem k⟩, fun k _ k' _ => ⟨fun h => ?_, fun h => ?_⟩, fun j => ?_⟩
  · exact congrArg Subtype.val (e.injective h)
  · exact congrArg e (Subtype.ext h)
  · obtain ⟨_, hipos⟩ := Finset.mem_filter.mp (e.symm j).2
    obtain ⟨k, hk⟩ := Finset.card_pos.mp hipos
    obtain ⟨hkA, hkα⟩ := Finset.mem_filter.mp hk
    refine Finset.card_pos.mpr ⟨k, Finset.mem_filter.mpr ⟨hkA, ?_⟩⟩
    change e ⟨α k, hmem k⟩ = j
    have hsub : (⟨α k, hmem k⟩ : ↥(Finset.univ.filter fun i => 0 < mAcount S α i)) = e.symm j :=
      Subtype.ext hkα
    rw [hsub, Equiv.apply_symm_apply]

end Basic

section Blocks

variable (S : Sample n) {l : ℕ} (f₀ : Fin n → Fin l)

def sizeVec (j : Fin l) : Fin (n + 1) :=
  ⟨mAcount S f₀ j, Nat.lt_succ_of_le (mAcount_le S f₀ j)⟩

def blockPerms : Finset (Equiv.Perm (Fin l)) :=
  Finset.univ.filter fun σ => sizeVec S f₀ ∘ σ = sizeVec S f₀

theorem mem_blockPerms {σ : Equiv.Perm (Fin l)} :
    σ ∈ blockPerms S f₀ ↔ ∀ j, mAcount S f₀ (σ j) = mAcount S f₀ j := by
  simp only [blockPerms, Finset.mem_filter, Finset.mem_univ, true_and, funext_iff,
    Function.comp_apply, sizeVec, Fin.mk.injEq]

theorem card_blockPerms :
    (blockPerms S f₀).card = ∏ m : Fin (n + 1), Nat.factorial (fibreCard (sizeVec S f₀) m) :=
  card_filter_comp_eq (sizeVec S f₀)

end Blocks

section Fibre

variable (S : Sample n) {l : ℕ} (f₀ : Fin n → Fin l)

theorem mem_sameFibres_iff (hfull : S.LA = Finset.univ) {f : Fin n → Fin l} :
    f ∈ sameFibres f₀ ↔ ∀ j, mAcount S f j = mAcount S f₀ j := by
  rw [mem_sameFibres, mAcount_eq_fibreCard S hfull f, mAcount_eq_fibreCard S hfull f₀]

theorem mAcount_pos_of_mem_sameFibres (hfull : S.LA = Finset.univ)
    (hpos : ∀ j, 0 < mAcount S f₀ j) {f : Fin n → Fin l} (hf : f ∈ sameFibres f₀) (j : Fin l) :
    0 < mAcount S f j := by
  rw [(mem_sameFibres_iff S f₀ hfull).mp hf j]
  exact hpos j

theorem exists_preimage_of_pos {f : Fin n → Fin l} (hpos : ∀ j, 0 < mAcount S f j) (j : Fin l) :
    ∃ k, f k = j := by
  obtain ⟨k, hk⟩ := Finset.card_pos.mp (hpos j)
  exact ⟨k, (Finset.mem_filter.mp hk).2⟩

theorem mAcount_comp_perm (f : Fin n → Fin l) (σ : Equiv.Perm (Fin l)) (j : Fin l) :
    mAcount S (fun k => σ (f k)) j = mAcount S f (σ.symm j) := by
  simp only [mAcount]
  refine congrArg Finset.card (Finset.filter_congr fun k _ => ?_)
  constructor
  · intro hh; rw [← hh, Equiv.symm_apply_apply]
  · intro hh; rw [hh, Equiv.apply_symm_apply]

theorem exists_perm_of_samePartA (hfull : S.LA = Finset.univ) {f g : Fin n → Fin l}
    (hf : ∀ j, ∃ k, f k = j) (hg : ∀ j, ∃ k, g k = j) (h : SamePartA S f g) :
    ∃ σ : Equiv.Perm (Fin l), ∀ k, g k = σ (f k) := by
  classical
  have hall : ∀ k : Fin n, k ∈ S.LA := fun k => by rw [hfull]; exact Finset.mem_univ k
  have hu : ∀ k, g (Classical.choose (hf (f k))) = g k := fun k =>
    (h _ (hall _) k (hall k)).mp (Classical.choose_spec (hf (f k)))
  have hv : ∀ k, f (Classical.choose (hg (g k))) = f k := fun k =>
    (h _ (hall _) k (hall k)).mpr (Classical.choose_spec (hg (g k)))
  refine ⟨⟨fun j => g (Classical.choose (hf j)), fun j => f (Classical.choose (hg j)),
    fun j => ?_, fun j => ?_⟩, fun k => ?_⟩
  · change f (Classical.choose (hg (g (Classical.choose (hf j))))) = j
    rw [hv (Classical.choose (hf j))]
    exact Classical.choose_spec (hf j)
  · change g (Classical.choose (hf (f (Classical.choose (hg j))))) = j
    rw [hu (Classical.choose (hg j))]
    exact Classical.choose_spec (hg j)
  · change g k = g (Classical.choose (hf (f k)))
    exact (hu k).symm

theorem exists_perm_of_samePartB (hfull : S.LB = Finset.univ) {f g : Fin n → Fin l}
    (hf : ∀ j, ∃ k, f k = j) (hg : ∀ j, ∃ k, g k = j) (h : SamePartB S f g) :
    ∃ σ : Equiv.Perm (Fin l), ∀ k, g k = σ (f k) := by
  classical
  have hall : ∀ k : Fin n, k ∈ S.LB := fun k => by rw [hfull]; exact Finset.mem_univ k
  have hu : ∀ k, g (Classical.choose (hf (f k))) = g k := fun k =>
    (h _ (hall _) k (hall k)).mp (Classical.choose_spec (hf (f k)))
  have hv : ∀ k, f (Classical.choose (hg (g k))) = f k := fun k =>
    (h _ (hall _) k (hall k)).mpr (Classical.choose_spec (hg (g k)))
  refine ⟨⟨fun j => g (Classical.choose (hf j)), fun j => f (Classical.choose (hg j)),
    fun j => ?_, fun j => ?_⟩, fun k => ?_⟩
  · change f (Classical.choose (hg (g (Classical.choose (hf j))))) = j
    rw [hv (Classical.choose (hf j))]
    exact Classical.choose_spec (hf j)
  · change g (Classical.choose (hf (f (Classical.choose (hg j))))) = j
    rw [hu (Classical.choose (hg j))]
    exact Classical.choose_spec (hg j)
  · change g k = g (Classical.choose (hf (f k)))
    exact (hu k).symm

theorem card_fibre_eq (hfull : S.LA = Finset.univ) (hpos : ∀ j, 0 < mAcount S f₀ j)
    {β : Fin n → Fin n} {f₁ : Fin n → Fin l} (hf₁ : f₁ ∈ sameFibres f₀) (hrep : repA S f₁ = β) :
    ((sameFibres f₀).filter fun f => repA S f = β).card = (blockPerms S f₀).card := by
  classical
  have hall : ∀ k : Fin n, k ∈ S.LA := fun k => by rw [hfull]; exact Finset.mem_univ k
  have hpos₁ : ∀ j, 0 < mAcount S f₁ j := mAcount_pos_of_mem_sameFibres S f₀ hfull hpos hf₁
  have hsurj₁ : ∀ j, ∃ k, f₁ k = j := exists_preimage_of_pos S hpos₁
  refine (Finset.card_bij (fun σ _ k => σ (f₁ k)) ?_ ?_ ?_).symm
  · intro σ hσ
    have hσ' := (mem_blockPerms S f₀).mp hσ
    refine Finset.mem_filter.mpr ⟨(mem_sameFibres_iff S f₀ hfull).mpr fun j => ?_, ?_⟩
    · rw [mAcount_comp_perm S f₁ σ j, (mem_sameFibres_iff S f₀ hfull).mp hf₁ (σ.symm j),
        ← hσ' (σ.symm j), Equiv.apply_symm_apply]
    · rw [← hrep]
      exact funext fun k => repA_congr S _ (fun _ _ _ _ =>
        ⟨fun hh => σ.injective hh, fun hh => congrArg σ hh⟩) (hall k)
  · intro σ _ σ' _ heq
    refine Equiv.ext fun j => ?_
    obtain ⟨k, hk⟩ := hsurj₁ j
    rw [← hk]
    exact congrFun heq k
  · intro f hf
    obtain ⟨hfX, hfrep⟩ := Finset.mem_filter.mp hf
    have hposf : ∀ j, 0 < mAcount S f j := mAcount_pos_of_mem_sameFibres S f₀ hfull hpos hfX
    have hsurjf : ∀ j, ∃ k, f k = j := exists_preimage_of_pos S hposf
    have hsame : SamePartA S f₁ f := samePartA_of_repA_eq S (by rw [hrep, hfrep])
    obtain ⟨σ, hσ⟩ := exists_perm_of_samePartA S hfull hsurj₁ hsurjf hsame
    have hfeq : f = fun k => σ (f₁ k) := funext hσ
    refine ⟨σ, (mem_blockPerms S f₀).mpr fun j => ?_, funext fun k => (hσ k).symm⟩
    have h1 : ∀ j', mAcount S f₀ (σ.symm j') = mAcount S f₀ j' := by
      intro j'
      calc mAcount S f₀ (σ.symm j') = mAcount S f₁ (σ.symm j') :=
            ((mem_sameFibres_iff S f₀ hfull).mp hf₁ (σ.symm j')).symm
        _ = mAcount S f j' := by rw [hfeq, mAcount_comp_perm S f₁ σ j']
        _ = mAcount S f₀ j' := (mem_sameFibres_iff S f₀ hfull).mp hfX j'
    have h2 := h1 (σ j)
    rw [Equiv.symm_apply_apply] at h2
    exact h2.symm

theorem exists_mem_sameFibres_repA (hfull : S.LA = Finset.univ) (hpos : ∀ j, 0 < mAcount S f₀ j)
    {β : Fin n → Fin n} (hβ : β ∈ shapeFibA S (shapeA S f₀)) :
    ∃ f ∈ sameFibres f₀, repA S f = β := by
  classical
  have hall : ∀ k : Fin n, k ∈ S.LA := fun k => by rw [hfull]; exact Finset.mem_univ k
  obtain ⟨hcan, hsh⟩ := (mem_shapeFibA S).mp hβ
  have hcard : Multiset.card (shapeA S β) = l := by
    rw [hsh, ← map_mAcount_eq_shapeA S f₀ hpos, Multiset.card_map]
    simp
  obtain ⟨γ, hγ, hγpos⟩ := exists_surj_typing S hfull β hcard
  have hmapγ : Multiset.map (mAcount S γ) Finset.univ.val
      = Multiset.map (mAcount S f₀) Finset.univ.val := by
    rw [map_mAcount_eq_shapeA S γ hγpos, map_mAcount_eq_shapeA S f₀ hpos,
      shapeA_congr S γ hγ, hsh]
  obtain ⟨g, hg⟩ := exists_perm_of_fibreCard_eq (f := mAcount S γ) (f₀ := mAcount S f₀)
    fun m => by rw [fibreCard_eq_count, fibreCard_eq_count, hmapγ]
  refine ⟨fun k => g (γ k), (mem_sameFibres_iff S f₀ hfull).mpr fun j => ?_, ?_⟩
  · have hgj : mAcount S f₀ (g (g.symm j)) = mAcount S γ (g.symm j) := congrFun hg (g.symm j)
    rw [Equiv.apply_symm_apply] at hgj
    rw [mAcount_comp_perm S γ g j, ← hgj]
  · have hsame : SamePartA S (fun k => g (γ k)) β := by
      intro k hk k' hk'
      exact Iff.trans ⟨fun hh => g.injective hh, fun hh => congrArg g hh⟩ (hγ k hk k' hk')
    exact (funext fun k => repA_congr S _ hsame (hall k)).trans hcan

theorem card_sameFibres_eq_Nshape_mul (hfull : S.LA = Finset.univ)
    (hpos : ∀ j, 0 < mAcount S f₀ j) :
    (sameFibres f₀).card = Nshape S (shapeA S f₀) * (blockPerms S f₀).card := by
  classical
  have hmaps : ∀ f ∈ sameFibres f₀, repA S f ∈ shapeFibA S (shapeA S f₀) := by
    intro f hf
    refine (mem_shapeFibA S).mpr ⟨repA_idem S hfull f, ?_⟩
    rw [← shapeA_congr S f (samePartA_repA S f)]
    have hmc : mAcount S f = mAcount S f₀ := funext ((mem_sameFibres_iff S f₀ hfull).mp hf)
    rw [shapeA, shapeA, hmc]
  have hconst : ∀ β ∈ shapeFibA S (shapeA S f₀),
      ((sameFibres f₀).filter fun f => repA S f = β).card = (blockPerms S f₀).card := by
    intro β hβ
    obtain ⟨f₁, hf₁, hrep⟩ := exists_mem_sameFibres_repA S f₀ hfull hpos hβ
    exact card_fibre_eq S f₀ hfull hpos hf₁ hrep
  rw [Finset.card_eq_sum_card_fiberwise hmaps, Finset.sum_congr rfl hconst, Finset.sum_const,
    smul_eq_mul, Nshape]

theorem Nshape_mul_of_surj (hfull : S.LA = Finset.univ) (hpos : ∀ j, 0 < mAcount S f₀ j) :
    Nshape S (shapeA S f₀) * (Multiset.map Nat.factorial (shapeA S f₀)).prod
      * ∏ m ∈ (shapeA S f₀).toFinset,
          Nat.factorial (Multiset.count m (shapeA S f₀)) = Nat.factorial n := by
  classical
  have hprod : ∏ j : Fin l, Nat.factorial (mAcount S f₀ j)
      = (Multiset.map Nat.factorial (shapeA S f₀)).prod := by
    rw [← map_mAcount_eq_shapeA S f₀ hpos, Multiset.map_map]
    rfl
  have hfc : ∀ m : Fin (n + 1), fibreCard (sizeVec S f₀) m
      = Multiset.count (m : ℕ) (shapeA S f₀) := by
    intro m
    calc fibreCard (sizeVec S f₀) m
        = Multiset.count m (Multiset.map (sizeVec S f₀) Finset.univ.val) :=
          fibreCard_eq_count (sizeVec S f₀) m
      _ = Multiset.count (m : ℕ)
            (Multiset.map Fin.val (Multiset.map (sizeVec S f₀) Finset.univ.val)) :=
          (Multiset.count_map_eq_count' Fin.val _ Fin.val_injective m).symm
      _ = Multiset.count (m : ℕ) (Multiset.map (mAcount S f₀) Finset.univ.val) := by
          rw [Multiset.map_map]; rfl
      _ = Multiset.count (m : ℕ) (shapeA S f₀) := by rw [map_mAcount_eq_shapeA S f₀ hpos]
  have hblk : (blockPerms S f₀).card
      = ∏ m ∈ (shapeA S f₀).toFinset,
          Nat.factorial (Multiset.count m (shapeA S f₀)) := by
    rw [card_blockPerms, Finset.prod_congr rfl fun m _ => congrArg Nat.factorial (hfc m),
      Fin.prod_univ_eq_prod_range
        (fun m => Nat.factorial (Multiset.count m (shapeA S f₀))) (n + 1)]
    refine (Finset.prod_subset (fun x hx => ?_) fun x _ hx => ?_).symm
    · rw [Multiset.mem_toFinset, ← map_mAcount_eq_shapeA S f₀ hpos] at hx
      obtain ⟨j, _, rfl⟩ := Multiset.mem_map.mp hx
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (mAcount_le S f₀ j))
    · rw [Multiset.mem_toFinset] at hx
      rw [Multiset.count_eq_zero.mpr hx]
      rfl
  have h1 : (sameFibres f₀).card * ∏ j, Nat.factorial (fibreCard f₀ j)
      = Nat.factorial (Fintype.card (Fin n)) := card_sameFibres_mul f₀
  rw [card_sameFibres_eq_Nshape_mul S f₀ hfull hpos, ← mAcount_eq_fibreCard S hfull f₀, hprod,
    Fintype.card_fin] at h1
  rw [← hblk, ← h1]
  ring

end Fibre

section Closed

variable (S : Sample n)

theorem Nshape_mul_factorial (hfull : S.LA = Finset.univ) {lam : Multiset ℕ}
    (hne : (shapeFibA S lam).Nonempty) :
    Nshape S lam * (Multiset.map Nat.factorial lam).prod
      * ∏ m ∈ lam.toFinset, Nat.factorial (Multiset.count m lam) = Nat.factorial n := by
  obtain ⟨β, hβ⟩ := hne
  obtain ⟨_, hsh⟩ := (mem_shapeFibA S).mp hβ
  obtain ⟨γ, hγ, hγpos⟩ := exists_surj_typing S hfull β rfl
  have hlam : shapeA S γ = lam := by rw [shapeA_congr S γ hγ, hsh]
  have h := Nshape_mul_of_surj S γ hfull hγpos
  rwa [hlam] at h

theorem Nshape_cast_eq_div {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (hfull : S.LA = Finset.univ) {lam : Multiset ℕ} (hne : (shapeFibA S lam).Nonempty) :
    (Nshape S lam : F) = (Nat.factorial n : F)
      / (((Multiset.map Nat.factorial lam).prod
          * ∏ m ∈ lam.toFinset, Nat.factorial (Multiset.count m lam) : ℕ) : F) := by
  have h := Nshape_mul_factorial S hfull hne
  have hp1 : (Multiset.map Nat.factorial lam).prod ≠ 0 := by
    refine Multiset.prod_ne_zero fun hz => ?_
    obtain ⟨x, _, hx⟩ := Multiset.mem_map.mp hz
    exact Nat.factorial_ne_zero x hx
  have hp2 : (∏ m ∈ lam.toFinset, Nat.factorial (Multiset.count m lam)) ≠ 0 :=
    (Finset.prod_pos fun m _ => Nat.factorial_pos _).ne'
  have hne0 : (((Multiset.map Nat.factorial lam).prod
      * ∏ m ∈ lam.toFinset, Nat.factorial (Multiset.count m lam) : ℕ) : F) ≠ 0 :=
    Nat.cast_ne_zero.mpr (mul_ne_zero hp1 hp2)
  rw [eq_div_iff hne0]
  have h' : Nshape S lam * ((Multiset.map Nat.factorial lam).prod
      * ∏ m ∈ lam.toFinset, Nat.factorial (Multiset.count m lam)) = Nat.factorial n := by
    rw [← mul_assoc]; exact h
  exact_mod_cast h'

theorem Nshape_eq_div (hfull : S.LA = Finset.univ) {lam : Multiset ℕ}
    (hne : (shapeFibA S lam).Nonempty) :
    (Nshape S lam : ℚ) = (Nat.factorial n : ℚ)
      / (((Multiset.map Nat.factorial lam).prod
          * ∏ m ∈ lam.toFinset, Nat.factorial (Multiset.count m lam) : ℕ) : ℚ) :=
  Nshape_cast_eq_div S hfull hne

theorem Qshape_eq_closed {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {θA θB ρ : F} (hfullA : S.LA = Finset.univ) (hfullB : S.LB = Finset.univ)
    (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (lam mu : Multiset ℕ)
    {α₀ : Fin n → Fin n} (hα₀ : α₀ ∈ shapeFibA S lam) :
    Qshape S hθA hθB hρ lam mu
      = (Nat.factorial n : F)
          / (((Multiset.map Nat.factorial lam).prod
            * ∏ m ∈ lam.toFinset, Nat.factorial (Multiset.count m lam) : ℕ) : F)
        * ∑ β ∈ shapeFibB S mu, Plab hθA hθB hρ S α₀ β := by
  rw [Qshape_eq_Nshape_mul S hfullA hfullB hθA hθB hρ lam mu hα₀,
    Nshape_cast_eq_div S hfullA ⟨α₀, hα₀⟩]

end Closed

end Rhone.Probability.OrbitCounts
