/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.SlotDeletion.Assembly

/-! # DL‑2's generating function `G(x,y,z)` as an `MvPolynomial (Fin 3) F` -/

@[expose] public section

universe u

namespace Rhone.Probability.Closure

open Finset LinearAlgebra.Recursion LinearAlgebra.Multilinear Multilinear SlotDeletion

variable {F : Type*} [Field F]

noncomputable def gA (πA : Fin 2 → F) (i : Fin 2) : MvPolynomial (Fin 3) F :=
  MvPolynomial.C (πA i) + MvPolynomial.C (eps F i) * MvPolynomial.X 0

noncomputable def gB (πB : Fin 2 → F) (j : Fin 2) : MvPolynomial (Fin 3) F :=
  MvPolynomial.C (πB j) + MvPolynomial.C (eps F j) * MvPolynomial.X 1

noncomputable def gAB (πA πB : Fin 2 → F) (i j : Fin 2) : MvPolynomial (Fin 3) F :=
  MvPolynomial.C (πA i * πB j)
    + MvPolynomial.C (eps F i * πB j) * MvPolynomial.X 0
    + MvPolynomial.C (πA i * eps F j) * MvPolynomial.X 1
    + MvPolynomial.C (eps F i * eps F j)
        * (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2)

variable {SA SB : Type u} [DecidableEq SA] [DecidableEq SB]

noncomputable def wtA (πA : Fin 2 → F) (α : SA → Fin 2) (AA S : Finset SA) : F :=
  (∏ u ∈ AA \ S, πA (α u)) * ∏ u ∈ S, eps F (α u)

noncomputable def wtB (πB : Fin 2 → F) (β : SB → Fin 2) (BB T : Finset SB) : F :=
  (∏ v ∈ BB \ T, πB (β v)) * ∏ v ∈ T, eps F (β v)

theorem wtA_insert_notMem {πA : Fin 2 → F} {α : SA → Fin 2} {AA S : Finset SA} {u₀ : SA}
    (hu : u₀ ∉ AA) (hS : S ⊆ AA) :
    wtA πA α (insert u₀ AA) S = πA (α u₀) * wtA πA α AA S := by
  have hu0S : u₀ ∉ S := fun h => hu (hS h)
  have hsd : insert u₀ AA \ S = insert u₀ (AA \ S) := by
    ext w
    simp only [Finset.mem_sdiff, Finset.mem_insert]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact Or.inl h1
      · exact Or.inr ⟨h1, h2⟩
    · rintro (rfl | ⟨h1, h2⟩)
      · exact ⟨Or.inl rfl, hu0S⟩
      · exact ⟨Or.inr h1, h2⟩
  rw [wtA, wtA, hsd, Finset.prod_insert (fun h => hu (Finset.mem_sdiff.mp h).1)]
  ring

theorem wtA_insert_mem {πA : Fin 2 → F} {α : SA → Fin 2} {AA S : Finset SA} {u₀ : SA}
    (hu : u₀ ∉ AA) (hS : S ⊆ AA) :
    wtA πA α (insert u₀ AA) (insert u₀ S) = eps F (α u₀) * wtA πA α AA S := by
  have hu0S : u₀ ∉ S := fun h => hu (hS h)
  have hsd : insert u₀ AA \ insert u₀ S = AA \ S := by
    ext w
    simp only [Finset.mem_sdiff, Finset.mem_insert, not_or]
    constructor
    · rintro ⟨h1 | h1, h2, h3⟩
      · exact absurd h1 h2
      · exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩
      exact ⟨Or.inr h1, fun h => hu (h ▸ h1), h2⟩
  rw [wtA, wtA, hsd, Finset.prod_insert hu0S]
  ring

theorem wtB_insert_notMem {πB : Fin 2 → F} {β : SB → Fin 2} {BB T : Finset SB} {v₀ : SB}
    (hv : v₀ ∉ BB) (hT : T ⊆ BB) :
    wtB πB β (insert v₀ BB) T = πB (β v₀) * wtB πB β BB T := by
  have hv0T : v₀ ∉ T := fun h => hv (hT h)
  have hsd : insert v₀ BB \ T = insert v₀ (BB \ T) := by
    ext w
    simp only [Finset.mem_sdiff, Finset.mem_insert]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact Or.inl h1
      · exact Or.inr ⟨h1, h2⟩
    · rintro (rfl | ⟨h1, h2⟩)
      · exact ⟨Or.inl rfl, hv0T⟩
      · exact ⟨Or.inr h1, h2⟩
  rw [wtB, wtB, hsd, Finset.prod_insert (fun h => hv (Finset.mem_sdiff.mp h).1)]
  ring

theorem wtB_insert_mem {πB : Fin 2 → F} {β : SB → Fin 2} {BB T : Finset SB} {v₀ : SB}
    (hv : v₀ ∉ BB) (hT : T ⊆ BB) :
    wtB πB β (insert v₀ BB) (insert v₀ T) = eps F (β v₀) * wtB πB β BB T := by
  have hv0T : v₀ ∉ T := fun h => hv (hT h)
  have hsd : insert v₀ BB \ insert v₀ T = BB \ T := by
    ext w
    simp only [Finset.mem_sdiff, Finset.mem_insert, not_or]
    constructor
    · rintro ⟨h1 | h1, h2, h3⟩
      · exact absurd h1 h2
      · exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩
      exact ⟨Or.inr h1, fun h => hv (h ▸ h1), h2⟩
  rw [wtB, wtB, hsd, Finset.prod_insert hv0T]
  ring

noncomputable def term (πA πB : Fin 2 → F) (α : SA → Fin 2) (β : SB → Fin 2)
    (AA : Finset SA) (BB : Finset SB) (M : Finset (SA × SB)) (S : Finset SA) (T : Finset SB) :
    MvPolynomial (Fin 3) F :=
  MvPolynomial.C (wtA πA α AA S * wtB πB β BB T)
    * (MvPolynomial.X 0 ^ S.card * MvPolynomial.X 1 ^ T.card
      * MvPolynomial.X 2 ^ (pairsIn M S T).card)

noncomputable def Gslots (πA πB : Fin 2 → F) (α : SA → Fin 2) (β : SB → Fin 2)
    (FA : Finset SA) (FB : Finset SB) (M : Finset (SA × SB)) : MvPolynomial (Fin 3) F :=
  (∏ u ∈ FA, gA πA (α u)) * (∏ v ∈ FB, gB πB (β v))
    * ∏ p ∈ M, gAB πA πB (α p.1) (β p.2)

theorem prod_gA_eq (πA : Fin 2 → F) (α : SA → Fin 2) (FA : Finset SA) :
    (∏ u ∈ FA, gA πA (α u))
      = ∑ S ∈ FA.powerset, MvPolynomial.C (wtA πA α FA S) * MvPolynomial.X 0 ^ S.card := by
  have hcomm : (∏ u ∈ FA, gA πA (α u))
      = ∏ u ∈ FA, (MvPolynomial.C (eps F (α u)) * MvPolynomial.X 0
          + MvPolynomial.C (πA (α u))) :=
    Finset.prod_congr rfl fun u _ => by rw [gA, add_comm]
  rw [hcomm, Finset.prod_add]
  refine Finset.sum_congr rfl fun S hS => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const, ← map_prod, ← map_prod, wtA, map_mul]
  ring

theorem prod_gB_eq (πB : Fin 2 → F) (β : SB → Fin 2) (FB : Finset SB) :
    (∏ v ∈ FB, gB πB (β v))
      = ∑ T ∈ FB.powerset, MvPolynomial.C (wtB πB β FB T) * MvPolynomial.X 1 ^ T.card := by
  have hcomm : (∏ v ∈ FB, gB πB (β v))
      = ∏ v ∈ FB, (MvPolynomial.C (eps F (β v)) * MvPolynomial.X 1
          + MvPolynomial.C (πB (β v))) :=
    Finset.prod_congr rfl fun v _ => by rw [gB, add_comm]
  rw [hcomm, Finset.prod_add]
  refine Finset.sum_congr rfl fun T hT => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_const, ← map_prod, ← map_prod, wtB, map_mul]
  ring

theorem Gslots_empty (πA πB : Fin 2 → F) (α : SA → Fin 2) (β : SB → Fin 2)
    (FA : Finset SA) (FB : Finset SB) :
    Gslots πA πB α β FA FB ∅
      = ∑ S ∈ FA.powerset, ∑ T ∈ FB.powerset, term πA πB α β FA FB ∅ S T := by
  rw [Gslots, Finset.prod_empty, mul_one, prod_gA_eq, prod_gB_eq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun T _ => ?_
  have hp : (pairsIn (∅ : Finset (SA × SB)) S T).card = 0 := by
    simp [pairsIn]
  rw [term, hp, pow_zero, map_mul]
  ring

theorem pairsIn_congr {M : Finset (SA × SB)} {S S' : Finset SA} {T T' : Finset SB}
    (hS : ∀ p ∈ M, (p.1 ∈ S ↔ p.1 ∈ S')) (hT : ∀ p ∈ M, (p.2 ∈ T ↔ p.2 ∈ T')) :
    pairsIn M S T = pairsIn M S' T' := by
  rw [pairsIn, pairsIn]
  exact Finset.filter_congr fun p hp => by rw [hS p hp, hT p hp]

theorem pairsIn_insert_of_not {a : SA × SB} {M : Finset (SA × SB)} {S : Finset SA}
    {T : Finset SB} (h : ¬ (a.1 ∈ S ∧ a.2 ∈ T)) :
    pairsIn (insert a M) S T = pairsIn M S T := by
  rw [pairsIn, pairsIn, Finset.filter_insert, ite_eq_right h]

theorem pairsIn_insert_of_mem {a : SA × SB} {M : Finset (SA × SB)} {S : Finset SA}
    {T : Finset SB} (h : a.1 ∈ S ∧ a.2 ∈ T) :
    pairsIn (insert a M) S T = insert a (pairsIn M S T) := by
  rw [pairsIn, pairsIn, Finset.filter_insert, ite_eq_left h]

theorem notMem_pairsIn {a : SA × SB} {M : Finset (SA × SB)} {S : Finset SA} {T : Finset SB}
    (ha : a ∉ M) : a ∉ pairsIn M S T := fun h => ha (Finset.mem_filter.mp h).1

omit [DecidableEq SA] [DecidableEq SB] in
theorem ne_fst_of_notMem {AA : Finset SA} {M : Finset (SA × SB)} {u₀ : SA} (hu : u₀ ∉ AA)
    (hMA : ∀ p ∈ M, p.1 ∈ AA) {p : SA × SB} (hp : p ∈ M) : p.1 ≠ u₀ :=
  fun h => hu (h ▸ hMA p hp)

omit [DecidableEq SA] [DecidableEq SB] in
theorem ne_snd_of_notMem {BB : Finset SB} {M : Finset (SA × SB)} {v₀ : SB} (hv : v₀ ∉ BB)
    (hMB : ∀ p ∈ M, p.2 ∈ BB) {p : SA × SB} (hp : p ∈ M) : p.2 ≠ v₀ :=
  fun h => hv (h ▸ hMB p hp)

section Four

variable {πA πB : Fin 2 → F} {α : SA → Fin 2} {β : SB → Fin 2}
variable {AA : Finset SA} {BB : Finset SB} {M : Finset (SA × SB)} {a : SA × SB}
variable {S : Finset SA} {T : Finset SB}
variable (hu : a.1 ∉ AA) (hv : a.2 ∉ BB) (hS : S ⊆ AA) (hT : T ⊆ BB)
variable (hMA : ∀ p ∈ M, p.1 ∈ AA) (hMB : ∀ p ∈ M, p.2 ∈ BB)
include hu hv hS hT

theorem term_case_none :
    term πA πB α β (insert a.1 AA) (insert a.2 BB) (insert a M) S T
      = MvPolynomial.C (πA (α a.1) * πB (β a.2)) * term πA πB α β AA BB M S T := by
  have hu0S : a.1 ∉ S := fun h => hu (hS h)
  have hp : pairsIn (insert a M) S T = pairsIn M S T :=
    pairsIn_insert_of_not (fun h => hu0S h.1)
  rw [term, term, hp, wtA_insert_notMem hu hS, wtB_insert_notMem hv hT,
    show (πA (α a.1) * wtA πA α AA S) * (πB (β a.2) * wtB πB β BB T)
      = (πA (α a.1) * πB (β a.2)) * (wtA πA α AA S * wtB πB β BB T) from by ring, map_mul]
  ring

include hMB in
theorem term_case_right :
    term πA πB α β (insert a.1 AA) (insert a.2 BB) (insert a M) S (insert a.2 T)
      = MvPolynomial.C (πA (α a.1) * eps F (β a.2)) * MvPolynomial.X 1
        * term πA πB α β AA BB M S T := by
  have hu0S : a.1 ∉ S := fun h => hu (hS h)
  have hv0T : a.2 ∉ T := fun h => hv (hT h)
  have hp : pairsIn (insert a M) S (insert a.2 T) = pairsIn M S T := by
    rw [pairsIn_insert_of_not (fun h => hu0S h.1)]
    exact pairsIn_congr (fun p _ => Iff.rfl)
      (fun p hp => by simp [Finset.mem_insert, ne_snd_of_notMem hv hMB hp])
  rw [term, term, hp, wtA_insert_notMem hu hS, wtB_insert_mem hv hT,
    Finset.card_insert_of_notMem hv0T,
    show (πA (α a.1) * wtA πA α AA S) * (eps F (β a.2) * wtB πB β BB T)
      = (πA (α a.1) * eps F (β a.2)) * (wtA πA α AA S * wtB πB β BB T) from by ring, map_mul,
    pow_succ]
  ring

include hMA in
theorem term_case_left :
    term πA πB α β (insert a.1 AA) (insert a.2 BB) (insert a M) (insert a.1 S) T
      = MvPolynomial.C (eps F (α a.1) * πB (β a.2)) * MvPolynomial.X 0
        * term πA πB α β AA BB M S T := by
  have hu0S : a.1 ∉ S := fun h => hu (hS h)
  have hv0T : a.2 ∉ T := fun h => hv (hT h)
  have hp : pairsIn (insert a M) (insert a.1 S) T = pairsIn M S T := by
    rw [pairsIn_insert_of_not (fun h => hv0T h.2)]
    exact pairsIn_congr (fun p hp => by simp [Finset.mem_insert, ne_fst_of_notMem hu hMA hp])
      (fun p _ => Iff.rfl)
  rw [term, term, hp, wtA_insert_mem hu hS, wtB_insert_notMem hv hT,
    Finset.card_insert_of_notMem hu0S,
    show (eps F (α a.1) * wtA πA α AA S) * (πB (β a.2) * wtB πB β BB T)
      = (eps F (α a.1) * πB (β a.2)) * (wtA πA α AA S * wtB πB β BB T) from by ring, map_mul,
    pow_succ]
  ring

include hMA hMB in
theorem term_case_both (ha : a ∉ M) :
    term πA πB α β (insert a.1 AA) (insert a.2 BB) (insert a M) (insert a.1 S) (insert a.2 T)
      = MvPolynomial.C (eps F (α a.1) * eps F (β a.2))
        * (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2)
        * term πA πB α β AA BB M S T := by
  have hu0S : a.1 ∉ S := fun h => hu (hS h)
  have hv0T : a.2 ∉ T := fun h => hv (hT h)
  have hp : pairsIn (insert a M) (insert a.1 S) (insert a.2 T) = insert a (pairsIn M S T) := by
    rw [pairsIn_insert_of_mem ⟨Finset.mem_insert_self _ _, Finset.mem_insert_self _ _⟩]
    congr 1
    exact pairsIn_congr (fun p hp => by simp [Finset.mem_insert, ne_fst_of_notMem hu hMA hp])
      (fun p hp => by simp [Finset.mem_insert, ne_snd_of_notMem hv hMB hp])
  rw [term, term, hp, Finset.card_insert_of_notMem (notMem_pairsIn ha),
    wtA_insert_mem hu hS, wtB_insert_mem hv hT,
    Finset.card_insert_of_notMem hu0S, Finset.card_insert_of_notMem hv0T,
    show (eps F (α a.1) * wtA πA α AA S) * (eps F (β a.2) * wtB πB β BB T)
      = (eps F (α a.1) * eps F (β a.2)) * (wtA πA α AA S * wtB πB β BB T) from by ring, map_mul,
    pow_succ, pow_succ, pow_succ]
  ring

end Four

theorem Gslots_eq_sum (πA πB : Fin 2 → F) (α : SA → Fin 2) (β : SB → Fin 2)
    (FA : Finset SA) (FB : Finset SB) :
    ∀ M : Finset (SA × SB), IsMatching M → (∀ p ∈ M, p.1 ∉ FA) → (∀ p ∈ M, p.2 ∉ FB) →
      Gslots πA πB α β FA FB M
        = ∑ S ∈ (FA ∪ domA M).powerset, ∑ T ∈ (FB ∪ domB M).powerset,
            term πA πB α β (FA ∪ domA M) (FB ∪ domB M) M S T := by
  intro M
  induction M using Finset.induction_on with
  | empty =>
    intro _ _ _
    simpa [domA, domB] using Gslots_empty πA πB α β FA FB
  | @insert a s ha ih =>
    intro hM hA hB
    have hM' : IsMatching s :=
      ⟨fun p hp p' hp' h => hM.fst p (Finset.mem_insert_of_mem hp) p'
          (Finset.mem_insert_of_mem hp') h,
       fun p hp p' hp' h => hM.snd p (Finset.mem_insert_of_mem hp) p'
          (Finset.mem_insert_of_mem hp') h⟩
    have hA' : ∀ p ∈ s, p.1 ∉ FA := fun p hp => hA p (Finset.mem_insert_of_mem hp)
    have hB' : ∀ p ∈ s, p.2 ∉ FB := fun p hp => hB p (Finset.mem_insert_of_mem hp)
    have haFA : a.1 ∉ FA := hA a (Finset.mem_insert_self a s)
    have haFB : a.2 ∉ FB := hB a (Finset.mem_insert_self a s)
    have hadom : a.1 ∉ domA s := by
      intro hcon
      obtain ⟨v, hv⟩ := mem_domA.mp hcon
      have hae := hM.fst a (Finset.mem_insert_self a s) (a.1, v)
        (Finset.mem_insert_of_mem hv) rfl
      exact ha (by rw [hae]; exact hv)
    have hbdom : a.2 ∉ domB s := by
      intro hcon
      obtain ⟨u, hu'⟩ := mem_domB.mp hcon
      have hae := hM.snd a (Finset.mem_insert_self a s) (u, a.2)
        (Finset.mem_insert_of_mem hu') rfl
      exact ha (by rw [hae]; exact hu')
    set AA := FA ∪ domA s with hAAdef
    set BB := FB ∪ domB s with hBBdef
    have hu : a.1 ∉ AA := by
      rw [hAAdef, Finset.mem_union]
      exact fun h => h.elim haFA hadom
    have hv : a.2 ∉ BB := by
      rw [hBBdef, Finset.mem_union]
      exact fun h => h.elim haFB hbdom
    have hMA : ∀ p ∈ s, p.1 ∈ AA := fun p hp =>
      Finset.mem_union_right _ (mem_domA_of_mem hp)
    have hMB : ∀ p ∈ s, p.2 ∈ BB := fun p hp =>
      Finset.mem_union_right _ (mem_domB_of_mem hp)
    have hAAins : FA ∪ domA (insert a s) = insert a.1 AA := by
      rw [domA, Finset.image_insert, ← domA, hAAdef, Finset.union_insert]
    have hBBins : FB ∪ domB (insert a s) = insert a.2 BB := by
      rw [domB, Finset.image_insert, ← domB, hBBdef, Finset.union_insert]
    have hins : Gslots πA πB α β FA FB (insert a s)
        = Gslots πA πB α β FA FB s * gAB πA πB (α a.1) (β a.2) := by
      rw [Gslots, Gslots, Finset.prod_insert ha]
      ring
    have inner : ∀ S : Finset SA,
        (∑ T ∈ (insert a.2 BB).powerset,
            term πA πB α β (insert a.1 AA) (insert a.2 BB) (insert a s) S T)
          = (∑ T ∈ BB.powerset,
              term πA πB α β (insert a.1 AA) (insert a.2 BB) (insert a s) S T)
            + ∑ T ∈ BB.powerset,
              term πA πB α β (insert a.1 AA) (insert a.2 BB) (insert a s) S (insert a.2 T) :=
      fun S => Finset.sum_powerset_insert hv _
    have g1 : (∑ S ∈ AA.powerset, ∑ T ∈ BB.powerset,
          term πA πB α β (insert a.1 AA) (insert a.2 BB) (insert a s) S T)
        = MvPolynomial.C (πA (α a.1) * πB (β a.2))
          * ∑ S ∈ AA.powerset, ∑ T ∈ BB.powerset, term πA πB α β AA BB s S T := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun S hS => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun T hT =>
        term_case_none hu hv (Finset.mem_powerset.mp hS) (Finset.mem_powerset.mp hT)
    have g2 : (∑ S ∈ AA.powerset, ∑ T ∈ BB.powerset,
          term πA πB α β (insert a.1 AA) (insert a.2 BB) (insert a s) S (insert a.2 T))
        = MvPolynomial.C (πA (α a.1) * eps F (β a.2)) * MvPolynomial.X 1
          * ∑ S ∈ AA.powerset, ∑ T ∈ BB.powerset, term πA πB α β AA BB s S T := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun S hS => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun T hT =>
        term_case_right hu hv (Finset.mem_powerset.mp hS) (Finset.mem_powerset.mp hT) hMB
    have g3 : (∑ S ∈ AA.powerset, ∑ T ∈ BB.powerset,
          term πA πB α β (insert a.1 AA) (insert a.2 BB) (insert a s) (insert a.1 S) T)
        = MvPolynomial.C (eps F (α a.1) * πB (β a.2)) * MvPolynomial.X 0
          * ∑ S ∈ AA.powerset, ∑ T ∈ BB.powerset, term πA πB α β AA BB s S T := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun S hS => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun T hT =>
        term_case_left hu hv (Finset.mem_powerset.mp hS) (Finset.mem_powerset.mp hT) hMA
    have g4 : (∑ S ∈ AA.powerset, ∑ T ∈ BB.powerset,
          term πA πB α β (insert a.1 AA) (insert a.2 BB) (insert a s)
            (insert a.1 S) (insert a.2 T))
        = MvPolynomial.C (eps F (α a.1) * eps F (β a.2))
            * (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2)
          * ∑ S ∈ AA.powerset, ∑ T ∈ BB.powerset, term πA πB α β AA BB s S T := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun S hS => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun T hT =>
        term_case_both hu hv (Finset.mem_powerset.mp hS) (Finset.mem_powerset.mp hT) hMA hMB ha
    rw [hins, ih hM' hA' hB', hAAins, hBBins, Finset.sum_powerset_insert hu]
    simp only [inner]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, g1, g2, g3, g4, gAB]
    ring

section Cfg

variable [Fintype SA] [Fintype SB]

omit [DecidableEq SA] [Fintype SA] [Fintype SB] in
theorem prod_gA_fiber (πA : Fin 2 → F) (α : SA → Fin 2) (FA : Finset SA) :
    (∏ u ∈ FA, gA πA (α u))
      = ∏ i : Fin 2, gA πA i ^ (FA.filter fun u => α u = i).card := by
  rw [← Finset.prod_fiberwise_of_maps_to (g := α) (fun u _ => Finset.mem_univ (α u))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.prod_congr rfl (fun u hu => by rw [(Finset.mem_filter.mp hu).2]),
    Finset.prod_const]

omit [DecidableEq SB] [Fintype SA] [Fintype SB] in
theorem prod_gB_fiber (πB : Fin 2 → F) (β : SB → Fin 2) (FB : Finset SB) :
    (∏ v ∈ FB, gB πB (β v))
      = ∏ j : Fin 2, gB πB j ^ (FB.filter fun v => β v = j).card := by
  rw [← Finset.prod_fiberwise_of_maps_to (g := β) (fun v _ => Finset.mem_univ (β v))]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Finset.prod_congr rfl (fun v hv => by rw [(Finset.mem_filter.mp hv).2]),
    Finset.prod_const]

omit [DecidableEq SA] [DecidableEq SB] [Fintype SA] [Fintype SB] in
theorem prod_gAB_fiber (πA πB : Fin 2 → F) (α : SA → Fin 2) (β : SB → Fin 2)
    (M : Finset (SA × SB)) :
    (∏ p ∈ M, gAB πA πB (α p.1) (β p.2))
      = ∏ i : Fin 2, ∏ j : Fin 2,
          gAB πA πB i j ^ (M.filter fun p => α p.1 = i ∧ β p.2 = j).card := by
  rw [← Finset.prod_fiberwise_of_maps_to (g := fun p : SA × SB => (α p.1, β p.2))
    (fun p _ => Finset.mem_univ _), Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  have hfil : (M.filter fun p : SA × SB => (α p.1, β p.2) = (i, j))
      = M.filter fun p => α p.1 = i ∧ β p.2 = j :=
    Finset.filter_congr fun p _ => by simp [Prod.ext_iff]
  rw [hfil, Finset.prod_congr rfl (fun p hp => by
      obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp hp).2
      rw [h1, h2]), Finset.prod_const]

noncomputable def Gcfg (πA πB : Fin 2 → F) (ξ : Config 2 2) : MvPolynomial (Fin 3) F :=
  (∏ i, gA πA i ^ ξ.a i) * (∏ j, gB πB j ^ ξ.b j) * ∏ i, ∏ j, gAB πA πB i j ^ ξ.c i j

theorem Gcfg_eq_Gslots (πA πB : Fin 2 → F) (α : SA → Fin 2) (β : SB → Fin 2)
    (M : Finset (SA × SB)) :
    Gcfg πA πB (xi M α β) = Gslots πA πB α β (freeA M) (freeB M) M := by
  rw [Gcfg, Gslots, prod_gA_fiber, prod_gB_fiber, prod_gAB_fiber]
  rfl

theorem Gcfg_eq_sum (πA πB : Fin 2 → F) (α : SA → Fin 2) (β : SB → Fin 2)
    {M : Finset (SA × SB)} (hM : IsMatching M) :
    Gcfg πA πB (xi M α β)
      = ∑ S : Finset SA, ∑ T : Finset SB,
          MvPolynomial.C ((∏ u ∈ Sᶜ, πA (α u)) * (∏ v ∈ Tᶜ, πB (β v))
              * (∏ u ∈ S, eps F (α u)) * ∏ v ∈ T, eps F (β v))
            * (MvPolynomial.X 0 ^ S.card * MvPolynomial.X 1 ^ T.card
              * MvPolynomial.X 2 ^ (pairsIn M S T).card) := by
  have hUA : freeA M ∪ domA M = (Finset.univ : Finset SA) :=
    Finset.sdiff_union_of_subset (Finset.subset_univ _)
  have hUB : freeB M ∪ domB M = (Finset.univ : Finset SB) :=
    Finset.sdiff_union_of_subset (Finset.subset_univ _)
  rw [Gcfg_eq_Gslots, Gslots_eq_sum πA πB α β (freeA M) (freeB M) M hM
    (fun p hp => notMem_freeA_of_mem hp) (fun p hp => notMem_freeB_of_mem hp), hUA, hUB,
    Finset.powerset_univ]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.powerset_univ]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [term, wtA, wtB, ← Finset.compl_eq_univ_sdiff, ← Finset.compl_eq_univ_sdiff]
  congr 2
  ring

end Cfg

end Rhone.Probability.Closure
