/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.Multilinear.Lump

/-! # Deleting a slot that carries the test vector `1` -/

@[expose] public section

universe u

namespace Rhone.Probability.SlotDeletion

open Finset LinearAlgebra.Recursion Denominator LinearAlgebra.Multilinear Multilinear

variable {KA KB : ℕ}

section Split

variable {ι : Type*} [DecidableEq ι] {K : ℕ}

def extAt (u₀ : ι) (γ : {x : ι // x ≠ u₀} → Fin K) (i : Fin K) : ι → Fin K :=
  fun x => if h : x = u₀ then i else γ ⟨x, h⟩

@[simp] theorem extAt_self (u₀ : ι) (γ : {x : ι // x ≠ u₀} → Fin K) (i : Fin K) :
    extAt u₀ γ i u₀ = i := by simp [extAt]

theorem extAt_of_ne {u₀ : ι} (γ : {x : ι // x ≠ u₀} → Fin K) (i : Fin K) {x : ι}
    (h : x ≠ u₀) : extAt u₀ γ i x = γ ⟨x, h⟩ := by simp [extAt, h]

theorem extAt_subtype {u₀ : ι} (γ : {x : ι // x ≠ u₀} → Fin K) (i : Fin K)
    (x : {x : ι // x ≠ u₀}) : extAt u₀ γ i (x : ι) = γ x := by
  rw [extAt_of_ne γ i x.2]

theorem extAt_update {u₀ : ι} (γ : {x : ι // x ≠ u₀} → Fin K) (i i' : Fin K) :
    extAt u₀ γ i = Function.update (extAt u₀ γ i') u₀ i := by
  funext x
  by_cases h : x = u₀
  · subst h; simp
  · rw [Function.update_of_ne h, extAt_of_ne γ i h, extAt_of_ne γ i' h]

def piSplit (u₀ : ι) : (({x : ι // x ≠ u₀} → Fin K) × Fin K) ≃ (ι → Fin K) where
  toFun p := extAt u₀ p.1 p.2
  invFun α := (fun x => α (x : ι), α u₀)
  left_inv p := by
    refine Prod.ext (funext fun x => ?_) (extAt_self _ _ _)
    exact extAt_subtype p.1 p.2 x
  right_inv α := by
    funext x
    by_cases h : x = u₀
    · subst h; exact extAt_self _ _ _
    · exact extAt_of_ne _ _ h

variable [Fintype ι]

theorem sum_pi_split {F : Type*} [AddCommMonoid F] (u₀ : ι) (G : (ι → Fin K) → F) :
    (∑ α : ι → Fin K, G α)
      = ∑ γ : {x : ι // x ≠ u₀} → Fin K, ∑ i : Fin K, G (extAt u₀ γ i) := by
  rw [← Equiv.sum_comp (piSplit u₀) G, Fintype.sum_prod_type]
  rfl

theorem prod_extAt {F : Type*} [CommMonoid F] (u₀ : ι) (s : ι → Fin K → F)
    (γ : {x : ι // x ≠ u₀} → Fin K) (i : Fin K) :
    (∏ x, s x (extAt u₀ γ i x)) = s u₀ i * ∏ x : {x : ι // x ≠ u₀}, s (x : ι) (γ x) := by
  have hsub : ∀ x : ι, x ∈ univ.erase u₀ ↔ x ≠ u₀ := by
    intro x; simp [Finset.mem_erase]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ u₀), extAt_self]
  congr 1
  rw [Finset.prod_subtype (p := fun x => x ≠ u₀) (univ.erase u₀) hsub
    (fun x => s x (extAt u₀ γ i x))]
  exact Finset.prod_congr rfl fun x _ => by rw [extAt_subtype]

end Split

section Restr

variable {SA SB : Type*} [Fintype SA] [DecidableEq SA] [Fintype SB] [DecidableEq SB]

def restrA (u₀ : SA) (M : Finset (SA × SB)) : Finset ({x : SA // x ≠ u₀} × SB) :=
  univ.filter fun p => ((p.1 : SA), p.2) ∈ M

def restrB (v₀ : SB) (M : Finset (SA × SB)) : Finset (SA × {y : SB // y ≠ v₀}) :=
  univ.filter fun p => (p.1, (p.2 : SB)) ∈ M

variable {M : Finset (SA × SB)} {u₀ : SA} {v₀ : SB}

@[simp] theorem mem_restrA {p : {x : SA // x ≠ u₀} × SB} :
    p ∈ restrA u₀ M ↔ ((p.1 : SA), p.2) ∈ M := by simp [restrA]

@[simp] theorem mem_restrB {p : SA × {y : SB // y ≠ v₀}} :
    p ∈ restrB v₀ M ↔ (p.1, (p.2 : SB)) ∈ M := by simp [restrB]

theorem isMatching_restrA (hM : IsMatching M) : IsMatching (restrA u₀ M) where
  fst p hp p' hp' h := by
    rw [mem_restrA] at hp hp'
    have he := hM.fst _ hp _ hp' (congrArg Subtype.val h)
    simp only [Prod.mk.injEq] at he
    exact Prod.ext h he.2
  snd p hp p' hp' h := by
    rw [mem_restrA] at hp hp'
    have he := hM.snd _ hp _ hp' h
    have h1 : (p.1 : SA) = (p'.1 : SA) := congrArg Prod.fst he
    exact Prod.ext (Subtype.ext h1) h

theorem isMatching_restrB (hM : IsMatching M) : IsMatching (restrB v₀ M) where
  fst p hp p' hp' h := by
    rw [mem_restrB] at hp hp'
    have he := hM.fst _ hp _ hp' h
    have h2 : (p.2 : SB) = (p'.2 : SB) := congrArg Prod.snd he
    exact Prod.ext h (Subtype.ext h2)
  snd p hp p' hp' h := by
    rw [mem_restrB] at hp hp'
    have he := hM.snd _ hp _ hp' (congrArg Subtype.val h)
    simp only [Prod.mk.injEq] at he
    exact Prod.ext he.1 h

theorem mem_freeA_restrA {x : {x : SA // x ≠ u₀}} :
    x ∈ freeA (restrA u₀ M) ↔ (x : SA) ∈ freeA M := by
  simp only [mem_freeA, mem_restrA]

theorem freeB_restrA (hu₀ : u₀ ∈ freeA M) : freeB (restrA u₀ M) = freeB M := by
  ext v
  simp only [mem_freeB, mem_restrA]
  constructor
  · intro h x
    by_cases hx : x = u₀
    · subst hx; exact mem_freeA.mp hu₀ v
    · exact h ⟨x, hx⟩
  · intro h x
    exact h (x : SA)

theorem mem_freeB_restrB {y : {y : SB // y ≠ v₀}} :
    y ∈ freeB (restrB v₀ M) ↔ (y : SB) ∈ freeB M := by
  simp only [mem_freeB, mem_restrB]

theorem freeA_restrB (hv₀ : v₀ ∈ freeB M) : freeA (restrB v₀ M) = freeA M := by
  ext u
  simp only [mem_freeA, mem_restrB]
  constructor
  · intro h y
    by_cases hy : y = v₀
    · subst hy; exact mem_freeB.mp hv₀ u
    · exact h ⟨y, hy⟩
  · intro h y
    exact h (y : SB)

theorem card_filter_restrA (hu₀ : u₀ ∈ freeA M) (P : SA × SB → Prop) [DecidablePred P] :
    ((restrA u₀ M).filter fun p => P ((p.1 : SA), p.2)).card = (M.filter P).card := by
  refine Finset.card_bij (fun p _ => ((p.1 : SA), p.2)) ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨mem_restrA.mp hp.1, hp.2⟩
  · intro p _ p' _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Subtype.ext h.1) h.2
  · intro r hr
    rw [Finset.mem_filter] at hr
    have hne : r.1 ≠ u₀ := fun hc => mem_freeA.mp hu₀ r.2 (hc ▸ hr.1)
    exact ⟨(⟨r.1, hne⟩, r.2), Finset.mem_filter.mpr ⟨mem_restrA.mpr hr.1, hr.2⟩, rfl⟩

theorem card_filter_restrB (hv₀ : v₀ ∈ freeB M) (P : SA × SB → Prop) [DecidablePred P] :
    ((restrB v₀ M).filter fun p => P (p.1, (p.2 : SB))).card = (M.filter P).card := by
  refine Finset.card_bij (fun p _ => (p.1, (p.2 : SB))) ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨mem_restrB.mp hp.1, hp.2⟩
  · intro p _ p' _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 (Subtype.ext h.2)
  · intro r hr
    rw [Finset.mem_filter] at hr
    have hne : r.2 ≠ v₀ := fun hc => mem_freeB.mp hv₀ r.1 (hc ▸ hr.1)
    exact ⟨(r.1, ⟨r.2, hne⟩), Finset.mem_filter.mpr ⟨mem_restrB.mpr hr.1, hr.2⟩, rfl⟩

theorem card_filter_freeA_restrA (P : SA → Prop) [DecidablePred P] :
    ((freeA (restrA u₀ M)).filter fun x : {x : SA // x ≠ u₀} => P x.1).card
      = (((freeA M).erase u₀).filter P).card := by
  refine Finset.card_bij (fun (x : {x : SA // x ≠ u₀}) _ => x.1) ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨Finset.mem_erase.mpr ⟨x.2, mem_freeA_restrA.mp hx.1⟩, hx.2⟩
  · intro x _ x' _ h
    exact Subtype.ext h
  · intro y hy
    rw [Finset.mem_filter, Finset.mem_erase] at hy
    exact ⟨⟨y, hy.1.1⟩, Finset.mem_filter.mpr ⟨mem_freeA_restrA.mpr hy.1.2, hy.2⟩, rfl⟩

theorem card_filter_freeB_restrB (P : SB → Prop) [DecidablePred P] :
    ((freeB (restrB v₀ M)).filter fun y : {y : SB // y ≠ v₀} => P y.1).card
      = (((freeB M).erase v₀).filter P).card := by
  refine Finset.card_bij (fun (y : {y : SB // y ≠ v₀}) _ => y.1) ?_ ?_ ?_
  · intro y hy
    rw [Finset.mem_filter] at hy ⊢
    exact ⟨Finset.mem_erase.mpr ⟨y.2, mem_freeB_restrB.mp hy.1⟩, hy.2⟩
  · intro y _ y' _ h
    exact Subtype.ext h
  · intro z hz
    rw [Finset.mem_filter, Finset.mem_erase] at hz
    exact ⟨⟨z, hz.1.1⟩, Finset.mem_filter.mpr ⟨mem_freeB_restrB.mpr hz.1.2, hz.2⟩, rfl⟩

theorem card_restrA (hu₀ : u₀ ∈ freeA M) : (restrA u₀ M).card = M.card := by
  have h := card_filter_restrA (M := M) hu₀ (fun _ => True)
  simpa using h

theorem card_restrB (hv₀ : v₀ ∈ freeB M) : (restrB v₀ M).card = M.card := by
  have h := card_filter_restrB (M := M) hv₀ (fun _ => True)
  simpa using h

theorem card_sub_ne (u₀ : SA) : Fintype.card {x : SA // x ≠ u₀} + 1 = Fintype.card SA := by
  have h : Fintype.card {x : SA // x ≠ u₀} = (univ.erase u₀).card := by
    rw [← Fintype.card_coe]
    exact Fintype.card_congr
      (Equiv.subtypeEquivRight fun x => by simp [Finset.mem_erase])
  rw [h, Finset.card_erase_of_mem (Finset.mem_univ u₀), Finset.card_univ]
  have h1 : 1 ≤ Fintype.card SA := Fintype.card_pos_iff.mpr ⟨u₀⟩
  omega

theorem xi_restrA (hu₀ : u₀ ∈ freeA M) (γ : {x : SA // x ≠ u₀} → Fin KA) (i : Fin KA)
    (β : SB → Fin KB) :
    xi M (extAt u₀ γ i) β = addA (xi (restrA u₀ M) γ β) i := by
  refine Config.ext (funext fun i' => ?_) (funext fun j' => ?_)
    (funext fun i' => funext fun j' => ?_)
  · have e := card_filter_erase_add hu₀ (fun x => extAt u₀ γ i x = i')
    have b := card_filter_freeA_restrA (M := M) (u₀ := u₀) (fun x => extAt u₀ γ i x = i')
    rw [Finset.filter_congr (fun x (_ : x ∈ freeA (restrA u₀ M)) =>
      by rw [extAt_subtype γ i x] : _)] at b
    simp only [xi_a, addA, incf_apply, extAt_self] at e ⊢
    rw [b]
    rcases eq_or_ne i i' with rfl | hne
    · simp only at e ⊢
      omega
    · rw [ite_eq_right hne] at e
      rw [ite_eq_right (Ne.symm hne)]
      omega
  · simp only [xi_b, addA, freeB_restrA hu₀]
  · have b := card_filter_restrA (M := M) hu₀
      (fun r => extAt u₀ γ i r.1 = i' ∧ β r.2 = j')
    rw [Finset.filter_congr (fun p (_ : p ∈ restrA u₀ M) =>
      by rw [extAt_subtype γ i p.1] : _)] at b
    simp only [xi_c, addA]
    exact b.symm

theorem xi_restrB (hv₀ : v₀ ∈ freeB M) (α : SA → Fin KA) (δ : {y : SB // y ≠ v₀} → Fin KB)
    (j : Fin KB) :
    xi M α (extAt v₀ δ j) = addB (xi (restrB v₀ M) α δ) j := by
  refine Config.ext (funext fun i' => ?_) (funext fun j' => ?_)
    (funext fun i' => funext fun j' => ?_)
  · simp only [xi_a, addB, freeA_restrB hv₀]
  · have e := card_filter_erase_add hv₀ (fun y => extAt v₀ δ j y = j')
    have b := card_filter_freeB_restrB (M := M) (v₀ := v₀) (fun y => extAt v₀ δ j y = j')
    rw [Finset.filter_congr (fun y (_ : y ∈ freeB (restrB v₀ M)) =>
      by rw [extAt_subtype δ j y] : _)] at b
    simp only [xi_b, addB, incf_apply, extAt_self] at e ⊢
    rw [b]
    rcases eq_or_ne j j' with rfl | hne
    · simp only at e ⊢
      omega
    · rw [ite_eq_right hne] at e
      rw [ite_eq_right (Ne.symm hne)]
      omega
  · have b := card_filter_restrB (M := M) hv₀
      (fun r => α r.1 = i' ∧ extAt v₀ δ j r.2 = j')
    rw [Finset.filter_congr (fun p (_ : p ∈ restrB v₀ M) =>
      by rw [extAt_subtype δ j p.2] : _)] at b
    simp only [xi_c, addB]
    exact b.symm

end Restr

section Delete

variable {SA SB : Type*} [Fintype SA] [DecidableEq SA] [Fintype SB] [DecidableEq SB]
variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}
variable (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
variable {q : Config KA KB → F} (hq : IsSolution θA θB ρ πA πB q)
include hθA hθB hρ hq

theorem Q_restrA (hπA : ∑ i, πA i = 1) {M : Finset (SA × SB)} {u₀ : SA} (hu₀ : u₀ ∈ freeA M)
    (s : SA → Fin KA → F) (hs : s u₀ = 1) (w : SB → Fin KB → F) :
    Q q M s w = Q q (restrA u₀ M) (fun x => s (x : SA)) w := by
  simp only [Q]
  rw [sum_pi_split u₀]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun β _ => ?_
  have hw : ∀ i : Fin KA,
      (∏ x, s x (extAt u₀ γ i x)) * (∏ v, w v (β v)) * q (xi M (extAt u₀ γ i) β)
        = (∏ x : {x : SA // x ≠ u₀}, s (x : SA) (γ x)) * (∏ v, w v (β v))
            * q (addA (xi (restrA u₀ M) γ β) i) := by
    intro i
    rw [prod_extAt, hs, xi_restrA hu₀]
    simp
  rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) => hw i, ← Finset.mul_sum,
    marginalise_A hθA hθB hρ hπA hq]

theorem Q_restrB (hπB : ∑ j, πB j = 1) {M : Finset (SA × SB)} {v₀ : SB} (hv₀ : v₀ ∈ freeB M)
    (s : SA → Fin KA → F) (w : SB → Fin KB → F) (hw : w v₀ = 1) :
    Q q M s w = Q q (restrB v₀ M) s (fun y => w (y : SB)) := by
  simp only [Q]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [sum_pi_split v₀]
  refine Finset.sum_congr rfl fun δ _ => ?_
  have hterm : ∀ j : Fin KB,
      (∏ u, s u (α u)) * (∏ y, w y (extAt v₀ δ j y)) * q (xi M α (extAt v₀ δ j))
        = (∏ u, s u (α u)) * (∏ y : {y : SB // y ≠ v₀}, w (y : SB) (δ y))
            * q (addB (xi (restrB v₀ M) α δ) j) := by
    intro j
    rw [prod_extAt, hw, xi_restrB hv₀]
    simp
  rw [Finset.sum_congr rfl fun j (_ : j ∈ univ) => hterm j, ← Finset.mul_sum,
    marginalise_B hθA hθB hρ hπB hq]

end Delete

section Erase

variable {SA SB : Type*} [Fintype SA] [DecidableEq SA] [Fintype SB] [DecidableEq SB]

theorem dropA_split (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) :
    (ξ.split i j).dropA i = addB (ξ.dropC i j) j := by
  refine Config.ext ?_ ?_ ?_ <;>
    simp [Config.split, Config.dropA, Config.dropC, addB, decf_incf_self]

theorem dropB_split (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) :
    (ξ.split i j).dropB j = addA (ξ.dropC i j) i := by
  refine Config.ext ?_ ?_ ?_ <;>
    simp [Config.split, Config.dropB, Config.dropC, addA, decf_incf_self]

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}
variable (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
variable {q : Config KA KB → F} (hq : IsSolution θA θB ρ πA πB q)
include hθA hθB hρ hq

theorem sum_xi_extAt_erase (hπA : ∑ i, πA i = 1) {M : Finset (SA × SB)} (hM : IsMatching M)
    {p : SA × SB} (hp : p ∈ M) (γ : {x : SA // x ≠ p.1} → Fin KA) (β : SB → Fin KB) :
    (∑ i, q (xi M (extAt p.1 γ i) β)) = ∑ i, q (xi (M.erase p) (extAt p.1 γ i) β) := by
  rcases isEmpty_or_nonempty (Fin KA) with hE | ⟨⟨i₀⟩⟩
  · simp [Finset.univ_eq_empty]
  · have hfree : p.1 ∈ freeA (M.erase p) := by
      rw [mem_freeA]
      intro v hv
      rcases Finset.mem_erase.mp hv with ⟨hne, hmem⟩
      exact hne (hM.fst _ hmem _ hp rfl)
    set α₀ := extAt p.1 γ i₀ with hα₀
    have hval : α₀ p.1 = i₀ := extAt_self _ _ _
    have hL : ∀ i : Fin KA, xi M (extAt p.1 γ i) β
        = addC ((xi M α₀ β).dropC (α₀ p.1) (β p.2)) i (β p.2) := by
      intro i
      rw [extAt_update γ i i₀, ← hα₀]
      exact xi_update_domA α₀ β hM hp i
    have hR : ∀ i : Fin KA, xi (M.erase p) (extAt p.1 γ i) β
        = addA ((xi (M.erase p) α₀ β).dropA (α₀ p.1)) i := by
      intro i
      rw [extAt_update γ i i₀, ← hα₀]
      exact xi_update_freeA α₀ β hfree i
    rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) => congrArg q (hL i),
      Finset.sum_congr rfl fun i (_ : i ∈ univ) => congrArg q (hR i),
      marginalise_C hθA hθB hρ hπA hq, marginalise_A hθA hθB hρ hπA hq,
      xi_erase α₀ β hM hp, hval, dropA_split]

theorem sum_xi_extAt_eraseB (hπB : ∑ j, πB j = 1) {M : Finset (SA × SB)} (hM : IsMatching M)
    {p : SA × SB} (hp : p ∈ M) (α : SA → Fin KA) (δ : {y : SB // y ≠ p.2} → Fin KB) :
    (∑ j, q (xi M α (extAt p.2 δ j))) = ∑ j, q (xi (M.erase p) α (extAt p.2 δ j)) := by
  rcases isEmpty_or_nonempty (Fin KB) with hE | ⟨⟨j₀⟩⟩
  · simp [Finset.univ_eq_empty]
  · have hfree : p.2 ∈ freeB (M.erase p) := by
      rw [mem_freeB]
      intro v hv
      rcases Finset.mem_erase.mp hv with ⟨hne, hmem⟩
      exact hne (hM.snd _ hmem _ hp rfl)
    set β₀ := extAt p.2 δ j₀ with hβ₀
    have hval : β₀ p.2 = j₀ := extAt_self _ _ _
    have hL : ∀ j : Fin KB, xi M α (extAt p.2 δ j)
        = addC ((xi M α β₀).dropC (α p.1) (β₀ p.2)) (α p.1) j := by
      intro j
      rw [extAt_update δ j j₀, ← hβ₀]
      exact xi_update_domB α β₀ hM hp j
    have hR : ∀ j : Fin KB, xi (M.erase p) α (extAt p.2 δ j)
        = addB ((xi (M.erase p) α β₀).dropB (β₀ p.2)) j := by
      intro j
      rw [extAt_update δ j j₀, ← hβ₀]
      exact xi_update_freeB α β₀ hfree j
    rw [Finset.sum_congr rfl fun j (_ : j ∈ univ) => congrArg q (hL j),
      Finset.sum_congr rfl fun j (_ : j ∈ univ) => congrArg q (hR j),
      marginalise_C' hθA hθB hρ hπB hq, marginalise_B hθA hθB hρ hπB hq,
      xi_erase α β₀ hM hp, hval, dropB_split]

theorem Q_eraseA (hπA : ∑ i, πA i = 1) {M : Finset (SA × SB)} (hM : IsMatching M)
    {p : SA × SB} (hp : p ∈ M) (s : SA → Fin KA → F) (hs : s p.1 = 1)
    (w : SB → Fin KB → F) :
    Q q M s w = Q q (M.erase p) s w := by
  simp only [Q]
  rw [sum_pi_split p.1, sum_pi_split p.1]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun β _ => ?_
  have hL : ∀ i : Fin KA,
      (∏ x, s x (extAt p.1 γ i x)) * (∏ v, w v (β v)) * q (xi M (extAt p.1 γ i) β)
        = (∏ x : {x : SA // x ≠ p.1}, s (x : SA) (γ x)) * (∏ v, w v (β v))
            * q (xi M (extAt p.1 γ i) β) := by
    intro i; rw [prod_extAt, hs]; simp
  have hR : ∀ i : Fin KA,
      (∏ x, s x (extAt p.1 γ i x)) * (∏ v, w v (β v)) * q (xi (M.erase p) (extAt p.1 γ i) β)
        = (∏ x : {x : SA // x ≠ p.1}, s (x : SA) (γ x)) * (∏ v, w v (β v))
            * q (xi (M.erase p) (extAt p.1 γ i) β) := by
    intro i; rw [prod_extAt, hs]; simp
  rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) => hL i,
    Finset.sum_congr rfl fun i (_ : i ∈ univ) => hR i, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_xi_extAt_erase hθA hθB hρ hq hπA hM hp]

theorem Q_eraseB (hπB : ∑ j, πB j = 1) {M : Finset (SA × SB)} (hM : IsMatching M)
    {p : SA × SB} (hp : p ∈ M) (s : SA → Fin KA → F) (w : SB → Fin KB → F)
    (hw : w p.2 = 1) :
    Q q M s w = Q q (M.erase p) s w := by
  simp only [Q]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [sum_pi_split p.2, sum_pi_split p.2]
  refine Finset.sum_congr rfl fun δ _ => ?_
  have hL : ∀ j : Fin KB,
      (∏ u, s u (α u)) * (∏ y, w y (extAt p.2 δ j y)) * q (xi M α (extAt p.2 δ j))
        = (∏ u, s u (α u)) * (∏ y : {y : SB // y ≠ p.2}, w (y : SB) (δ y))
            * q (xi M α (extAt p.2 δ j)) := by
    intro j; rw [prod_extAt, hw]; simp
  have hR : ∀ j : Fin KB,
      (∏ u, s u (α u)) * (∏ y, w y (extAt p.2 δ j y))
          * q (xi (M.erase p) α (extAt p.2 δ j))
        = (∏ u, s u (α u)) * (∏ y : {y : SB // y ≠ p.2}, w (y : SB) (δ y))
            * q (xi (M.erase p) α (extAt p.2 δ j)) := by
    intro j; rw [prod_extAt, hw]; simp
  rw [Finset.sum_congr rfl fun j (_ : j ∈ univ) => hL j,
    Finset.sum_congr rfl fun j (_ : j ∈ univ) => hR j, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_xi_extAt_eraseB hθA hθB hρ hq hπB hM hp]

end Erase

end Rhone.Probability.SlotDeletion
