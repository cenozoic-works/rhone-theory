/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.Multilinear.Centre

/-! # §4.1 — `Φ^{i,1} ≡ 0`, directly from the product form -/

@[expose] public section

namespace Rhone.Probability.Multilinear

open Finset LinearAlgebra.Recursion Denominator

variable {KA KB : ℕ} {SA SB : Type*}
variable [Fintype SA] [DecidableEq SA] [Fintype SB] [DecidableEq SB]

section Marginal

variable (M : Finset (SA × SB)) (α : SA → Fin KA) (β : SB → Fin KB)

def mAof (α : SA → Fin KA) (i : Fin KA) : ℕ := ((univ : Finset SA).filter fun u => α u = i).card

def mBof (β : SB → Fin KB) (j : Fin KB) : ℕ := ((univ : Finset SB).filter fun v => β v = j).card

omit [Fintype SB] [DecidableEq SB] in
theorem card_filter_split (P : SA → Prop) [DecidablePred P] :
    (((freeA M).filter P).card + ((domA M).filter P).card)
      = ((univ : Finset SA).filter P).card := by
  have h1 : ((univ : Finset SA).filter P).filter (fun u => u ∈ domA M) = (domA M).filter P := by
    ext u; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; tauto
  have h2 : ((univ : Finset SA).filter P).filter (fun u => u ∉ domA M) = (freeA M).filter P := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, freeA, Finset.mem_sdiff]
    tauto
  have h3 := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset SA).filter P) (p := fun u => u ∈ domA M)
  rw [h1, h2] at h3
  omega

omit [Fintype SA] [DecidableEq SA] in
theorem card_filter_splitB (P : SB → Prop) [DecidablePred P] :
    (((freeB M).filter P).card + ((domB M).filter P).card)
      = ((univ : Finset SB).filter P).card := by
  have h1 : ((univ : Finset SB).filter P).filter (fun v => v ∈ domB M) = (domB M).filter P := by
    ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; tauto
  have h2 : ((univ : Finset SB).filter P).filter (fun v => v ∉ domB M) = (freeB M).filter P := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, freeB, Finset.mem_sdiff]
    tauto
  have h3 := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset SB).filter P) (p := fun v => v ∈ domB M)
  rw [h1, h2] at h3
  omega

theorem mA_xi (hM : IsMatching M) : (xi M α β).mA = mAof α := by
  funext i
  have hinj : Set.InjOn Prod.fst (M.filter fun p => α p.1 = i) := fun p hp p' hp' he =>
    hM.fst p (Finset.mem_filter.mp hp).1 p' (Finset.mem_filter.mp hp').1 he
  have h1 : ((domA M).filter fun u => α u = i).card = (M.filter fun p => α p.1 = i).card := by
    rw [domA, Finset.filter_image, Finset.card_image_of_injOn hinj]
  rw [Config.mA, cRow_xi, xi_a, ← h1, card_filter_split, mAof]

theorem mB_xi (hM : IsMatching M) : (xi M α β).mB = mBof β := by
  funext j
  have hinj : Set.InjOn Prod.snd (M.filter fun p => β p.2 = j) := fun p hp p' hp' he =>
    hM.snd p (Finset.mem_filter.mp hp).1 p' (Finset.mem_filter.mp hp').1 he
  have h1 : ((domB M).filter fun v => β v = j).card = (M.filter fun p => β p.2 = j).card := by
    rw [domB, Finset.filter_image, Finset.card_image_of_injOn hinj]
  rw [Config.mB, cCol_xi, xi_b, ← h1, card_filter_splitB, mBof]

end Marginal

section Factor

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}
variable (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
variable {q : Config KA KB → F} (hq : IsSolution θA θB ρ πA πB q)
variable (M : Finset (SA × SB))
include hθA hθB hρ hq

theorem Q_factor (hM : IsMatching M)
    (hmin : Fintype.card SA ≤ 1 ∨ Fintype.card SB ≤ 1)
    (s : SA → Fin KA → F) (w : SB → Fin KB → F) :
    Q q M s w = (∑ α : SA → Fin KA, (∏ u, s u (α u)) * qOne θA πA (mAof α))
      * ∑ β : SB → Fin KB, (∏ v, w v (β v)) * qOne θB πB (mBof β) := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  have hmin' : (xi M α β).nA ≤ 1 ∨ (xi M α β).nB ≤ 1 := by
    rcases hmin with h | h
    · exact Or.inl (by rw [nA_xi M α β hM]; exact h)
    · exact Or.inr (by rw [nB_xi M α β hM]; exact h)
  rw [eq_qHat_of_min_le_one hθA hθB hρ hq (xi M α β) hmin', qHat, mA_xi M α β hM,
    mB_xi M α β hM]
  ring

theorem Q_eq_zero_of_one_B_slot (hM : IsMatching M) (hcard : Fintype.card SB = 1)
    (s : SA → Fin KA → F) (w : SB → Fin KB → F) (hcen : ∀ v, mean πB (w v) = 0) :
    Q q M s w = 0 := by
  obtain ⟨v₀, hv₀⟩ := Fintype.card_eq_one_iff.mp hcard
  have huniv : (univ : Finset SB) = {v₀} :=
    Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_univ _, fun x _ => hv₀ x⟩
  have hB : (∑ β : SB → Fin KB, (∏ v, w v (β v)) * qOne θB πB (mBof β)) = 0 := by
    have hterm : ∀ β : SB → Fin KB,
        (∏ v, w v (β v)) * qOne θB πB (mBof β) = w v₀ (β v₀) * πB (β v₀) := by
      intro β
      have hprod : (∏ v, w v (β v)) = w v₀ (β v₀) :=
        Finset.prod_eq_single_of_mem v₀ (Finset.mem_univ _) fun v _ hv => absurd (hv₀ v) hv
      have hm : mBof β = incf (fun _ => 0) (β v₀) := by
        funext j
        rw [mBof, huniv, incf_apply, Finset.filter_singleton]
        by_cases h : β v₀ = j
        · rw [ite_eq_left h, Finset.card_singleton, ite_eq_left h.symm]
        · rw [ite_eq_right h, Finset.card_empty, ite_eq_right fun hc => h hc.symm]
      rw [hprod, hm, qOne_eA hθB.ne']
    rw [Finset.sum_congr rfl fun β _ => hterm β]
    let e : (SB → Fin KB) ≃ Fin KB :=
      { toFun := fun β => β v₀
        invFun := fun j _ => j
        left_inv := fun β => funext fun v => by rw [hv₀ v]
        right_inv := fun _ => rfl }
    rw [Fintype.sum_equiv e (fun β => w v₀ (β v₀) * πB (β v₀)) (fun j => w v₀ j * πB j)
      fun _ => rfl]
    have := hcen v₀
    rw [mean] at this
    rw [Finset.sum_congr rfl fun j (_ : j ∈ univ) => mul_comm (w v₀ j) (πB j), this]
  rw [Q_factor hθA hθB hρ hq M hM (Or.inr (le_of_eq hcard)) s w, hB, mul_zero]

end Factor

end Rhone.Probability.Multilinear
