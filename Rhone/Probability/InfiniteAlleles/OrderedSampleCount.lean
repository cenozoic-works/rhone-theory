/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.InfiniteAlleles.Count
public import Rhone.Probability.InfiniteAlleles.Blocks

/-! # The ordered-typed-sample count, and the pull-out step -/

@[expose] public section

namespace Rhone.Probability.InfiniteAlleles

open Finset LinearAlgebra.Recursion LinearAlgebra.Recursion.Config

variable {n KA KB : ℕ} (S : Sample n) (α : Fin n → Fin KA) (β : Fin n → Fin KB)

def resA : {k // k ∈ S.onlyA} → Fin KA := fun x => α x.val

def resB : {k // k ∈ S.onlyB} → Fin KB := fun x => β x.val

def resC : {k // k ∈ S.both} → Fin KA × Fin KB := fun x => (α x.val, β x.val)

theorem fibreCard_resA (i : Fin KA) : fibreCard (resA S α) i = (cfgOf S α β).a i :=
  card_attach_filter S.onlyA fun k => α k = i

theorem fibreCard_resB (j : Fin KB) : fibreCard (resB S β) j = (cfgOf S α β).b j :=
  card_attach_filter S.onlyB fun k => β k = j

theorem fibreCard_resC (p : Fin KA × Fin KB) :
    fibreCard (resC S α β) p = (cfgOf S α β).c p.1 p.2 := by
  have h1 : fibreCard (resC S α β) p
      = (Finset.univ.filter fun x : {k // k ∈ S.both} => α x.val = p.1 ∧ β x.val = p.2).card := by
    refine congrArg Finset.card (Finset.filter_congr fun x _ => ?_)
    exact Prod.ext_iff
  rw [h1, card_attach_filter S.both fun k => α k = p.1 ∧ β k = p.2, cfgOf_c]

theorem mem_sameFibres_resA {g : {k // k ∈ S.onlyA} → Fin KA} :
    g ∈ sameFibres (resA S α) ↔ ∀ i, fibreCard g i = (cfgOf S α β).a i := by
  rw [mem_sameFibres]
  exact forall_congr' fun i => by rw [fibreCard_resA S α β i]

theorem mem_sameFibres_resB {g : {k // k ∈ S.onlyB} → Fin KB} :
    g ∈ sameFibres (resB S β) ↔ ∀ j, fibreCard g j = (cfgOf S α β).b j := by
  rw [mem_sameFibres]
  exact forall_congr' fun j => by rw [fibreCard_resB S α β j]

theorem mem_sameFibres_resC {g : {k // k ∈ S.both} → Fin KA × Fin KB} :
    g ∈ sameFibres (resC S α β) ↔ ∀ p, fibreCard g p = (cfgOf S α β).c p.1 p.2 := by
  rw [mem_sameFibres]
  exact forall_congr' fun p => by rw [fibreCard_resC S α β p]

theorem card_assignA_mul :
    (sameFibres (resA S α)).card * ∏ i, Nat.factorial ((cfgOf S α β).a i)
      = Nat.factorial (cfgOf S α β).sumA := by
  rw [Finset.prod_congr rfl fun i _ => by rw [← fibreCard_resA S α β i],
    card_sameFibres_mul (resA S α), Fintype.card_coe, sumA_cfgOf]

theorem card_assignB_mul :
    (sameFibres (resB S β)).card * ∏ j, Nat.factorial ((cfgOf S α β).b j)
      = Nat.factorial (cfgOf S α β).sumB := by
  rw [Finset.prod_congr rfl fun j _ => by rw [← fibreCard_resB S α β j],
    card_sameFibres_mul (resB S β), Fintype.card_coe, sumB_cfgOf]

theorem card_assignC_mul :
    (sameFibres (resC S α β)).card * ∏ i, ∏ j, Nat.factorial ((cfgOf S α β).c i j)
      = Nat.factorial (cfgOf S α β).t := by
  rw [← Fintype.prod_prod_type (f := fun p : Fin KA × Fin KB =>
      Nat.factorial ((cfgOf S α β).c p.1 p.2)),
    Finset.prod_congr rfl fun p _ => by rw [← fibreCard_resC S α β p],
    card_sameFibres_mul (resC S α β), Fintype.card_coe, t_cfgOf]

theorem card_assign_mul :
    ((sameFibres (resA S α)).card * (sameFibres (resB S β)).card
        * (sameFibres (resC S α β)).card)
      * ((∏ i, Nat.factorial ((cfgOf S α β).a i)) * (∏ j, Nat.factorial ((cfgOf S α β).b j))
        * ∏ i, ∏ j, Nat.factorial ((cfgOf S α β).c i j))
      = Nat.factorial (cfgOf S α β).sumA * Nat.factorial (cfgOf S α β).sumB
        * Nat.factorial (cfgOf S α β).t := by
  rw [← card_assignA_mul S α β, ← card_assignB_mul S α β, ← card_assignC_mul S α β]
  ring

section PullOut

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] {θA θB ρ : F}

theorem sum_PIA_of_relabelClass (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (ξ : Config KA KB) (O : Finset (Config KA KB))
    (hO : ∀ η ∈ O, ∃ (σ : Equiv.Perm (Fin KA)) (τ : Equiv.Perm (Fin KB)),
      η = InfiniteAlleles.relabel σ τ ξ) :
    ∑ η ∈ O, PIA hθA hθB hρ η = (O.card : F) * PIA hθA hθB hρ ξ := by
  refine sum_eq_card_mul_of_const O _ ξ fun η hη => ?_
  obtain ⟨σ, τ, rfl⟩ := hO η hη
  exact PIA_relabel hθA hθB hρ σ τ ξ

theorem sum_Plab_of_relabelClass (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    {ι : Type*} (T : Finset ι) (A : ι → Fin n → Fin KA) (B : ι → Fin n → Fin KB)
    (hT : ∀ x ∈ T, ∃ (σ : Equiv.Perm (Fin KA)) (τ : Equiv.Perm (Fin KB)),
      cfgOf S (A x) (B x) = InfiniteAlleles.relabel σ τ (cfgOf S α β)) :
    ∑ x ∈ T, Plab hθA hθB hρ S (A x) (B x) = (T.card : F) * Plab hθA hθB hρ S α β := by
  have hconst : ∀ x ∈ T, Plab hθA hθB hρ S (A x) (B x) = Plab hθA hθB hρ S α β := by
    intro x hx
    obtain ⟨σ, τ, hx'⟩ := hT x hx
    rw [Plab, hx', PIA_relabel, Plab]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]

end PullOut

end Rhone.Probability.InfiniteAlleles
