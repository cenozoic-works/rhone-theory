/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib

/-! # Counting maps with prescribed fibre sizes -/

@[expose] public section

namespace Rhone.Probability.InfiniteAlleles

open Finset

variable {α ι : Type*} [Fintype α] [DecidableEq ι]

def fibreCard (f : α → ι) (i : ι) : ℕ := (Finset.univ.filter fun a => f a = i).card

theorem fibreCard_eq_card_subtype (f : α → ι) (i : ι) :
    fibreCard f i = Fintype.card {a // f a = i} := (Fintype.card_subtype _).symm

theorem fibreCard_comp (f : α → ι) (g : Equiv.Perm α) (i : ι) :
    fibreCard (f ∘ g) i = fibreCard f i :=
  Finset.card_equiv g fun a => by simp [Function.comp_apply]

theorem exists_perm_of_fibreCard_eq {f f₀ : α → ι} (h : ∀ i, fibreCard f i = fibreCard f₀ i) :
    ∃ g : Equiv.Perm α, f₀ ∘ g = f := by
  have hcard : ∀ i : ι, Fintype.card {a // f a = i} = Fintype.card {a // f₀ a = i} := by
    intro i
    rw [← fibreCard_eq_card_subtype, ← fibreCard_eq_card_subtype]
    exact h i
  refine ⟨(Equiv.sigmaFiberEquiv f).symm.trans
    ((Equiv.sigmaCongrRight fun i => Fintype.equivOfCardEq (hcard i)).trans
      (Equiv.sigmaFiberEquiv f₀)), funext fun a => ?_⟩
  exact ((Fintype.equivOfCardEq (hcard (f a))) ⟨a, rfl⟩).2

variable [DecidableEq α] [Fintype ι]

def sameFibres (f₀ : α → ι) : Finset (α → ι) :=
  Finset.univ.filter fun f => ∀ i, fibreCard f i = fibreCard f₀ i

theorem mem_sameFibres {f f₀ : α → ι} :
    f ∈ sameFibres f₀ ↔ ∀ i, fibreCard f i = fibreCard f₀ i := by
  simp [sameFibres]

theorem comp_mem_sameFibres (f₀ : α → ι) (g : Equiv.Perm α) : f₀ ∘ g ∈ sameFibres f₀ :=
  mem_sameFibres.mpr fun i => fibreCard_comp f₀ g i

theorem card_filter_comp_eq (f₀ : α → ι) :
    (Finset.univ.filter fun h : Equiv.Perm α => f₀ ∘ h = f₀).card
      = ∏ i, Nat.factorial (fibreCard f₀ i) := by
  rw [← Fintype.card_subtype, DomMulAct.stabilizer_card f₀]
  exact Finset.prod_congr rfl fun i _ => by rw [fibreCard_eq_card_subtype]

theorem card_sameFibres_mul (f₀ : α → ι) :
    (sameFibres f₀).card * ∏ i, Nat.factorial (fibreCard f₀ i)
      = Nat.factorial (Fintype.card α) := by
  have key : (Finset.univ : Finset (Equiv.Perm α)).card
      = ∑ f ∈ sameFibres f₀, (Finset.univ.filter fun g : Equiv.Perm α => f₀ ∘ g = f).card :=
    Finset.card_eq_sum_card_fiberwise fun g _ => comp_mem_sameFibres f₀ g
  have hfib : ∀ f ∈ sameFibres f₀,
      (Finset.univ.filter fun g : Equiv.Perm α => f₀ ∘ g = f).card
        = ∏ i, Nat.factorial (fibreCard f₀ i) := by
    intro f hf
    obtain ⟨g₀, hg₀⟩ := exists_perm_of_fibreCard_eq (mem_sameFibres.mp hf)
    rw [← card_filter_comp_eq f₀]
    refine (Finset.card_equiv (Equiv.mulRight g₀) fun h => ?_).symm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.coe_mulRight]
    constructor
    · intro hh
      funext a
      have h1 : f₀ (h (g₀ a)) = f₀ (g₀ a) := congrFun hh (g₀ a)
      have h2 : f₀ (g₀ a) = f a := congrFun hg₀ a
      exact h1.trans h2
    · intro hh
      funext a
      have h1 : f₀ (h (g₀ (g₀.symm a))) = f (g₀.symm a) := congrFun hh (g₀.symm a)
      have h2 : f₀ (g₀ (g₀.symm a)) = f (g₀.symm a) := congrFun hg₀ (g₀.symm a)
      rw [Equiv.apply_symm_apply] at h1 h2
      exact h1.trans h2.symm
  rw [Finset.card_univ, Fintype.card_perm] at key
  rw [key, Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul]

theorem card_attach_filter {n : ℕ} (T : Finset (Fin n)) (p : Fin n → Prop) [DecidablePred p] :
    (Finset.univ.filter fun x : {k // k ∈ T} => p x.val).card = (T.filter p).card := by
  refine Finset.card_nbij (fun x => x.val) (fun x hx => ?_) (fun x _ y _ h => Subtype.ext h)
    fun k hk => ?_
  · exact Finset.mem_filter.mpr ⟨x.2, (Finset.mem_filter.mp hx).2⟩
  · obtain ⟨hkT, hpk⟩ := Finset.mem_filter.mp hk
    exact ⟨⟨k, hkT⟩, Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpk⟩), rfl⟩

end Rhone.Probability.InfiniteAlleles
