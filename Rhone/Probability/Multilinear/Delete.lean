/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.Multilinear.Basic

/-! # Slot deletion in the `Q` form: a test vector `1` deletes its slot -/

@[expose] public section

namespace Rhone.Probability.Multilinear

open Finset LinearAlgebra.Recursion Denominator

variable {KA KB : ℕ} {SA SB : Type*}
variable [Fintype SA] [DecidableEq SA] [Fintype SB] [DecidableEq SB]

section Weight

variable {F : Type*} [CommRing F]

theorem sum_weight_update {ι : Type*} [Fintype ι] [DecidableEq ι] {K : ℕ}
    (α : ι → Fin K) (u₀ : ι) (g : (ι → Fin K) → F) :
    (∑ α' : ι → Fin K,
        (∏ u ∈ univ.erase u₀, (Pi.single (α u) (1 : F) : Fin K → F) (α' u)) * g α')
      = ∑ i : Fin K, g (Function.update α u₀ i) := by
  have hw : ∀ α' : ι → Fin K,
      (∏ u ∈ univ.erase u₀, (Pi.single (α u) (1 : F) : Fin K → F) (α' u)) * g α'
        = if (∀ u ∈ univ.erase u₀, α' u = α u) then g α' else 0 := by
    intro α'
    by_cases h : ∀ u ∈ univ.erase u₀, α' u = α u
    · rw [ite_eq_left h, Finset.prod_eq_one (fun u hu => by rw [h u hu]; simp), one_mul]
    · rw [ite_eq_right h]
      push Not at h
      obtain ⟨u, hu, hne⟩ := h
      rw [Finset.prod_eq_zero hu (Pi.single_eq_of_ne hne 1), zero_mul]
  have himg : univ.filter (fun α' : ι → Fin K => ∀ u ∈ univ.erase u₀, α' u = α u)
      = univ.image (fun i : Fin K => Function.update α u₀ i) := by
    ext α'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      refine ⟨α' u₀, funext fun u => ?_⟩
      by_cases hu : u = u₀
      · subst hu; simp
      · rw [Function.update_of_ne hu]
        exact (h u (Finset.mem_erase.mpr ⟨hu, Finset.mem_univ u⟩)).symm
    · rintro ⟨i, rfl⟩ u hu
      rw [Function.update_of_ne (Finset.mem_erase.mp hu).1]
  simp only [hw]
  rw [← Finset.sum_filter, himg, Finset.sum_image]
  intro i _ i' _ hii
  have := congrFun hii u₀
  simpa using this

end Weight

section Basis

variable {F : Type*} [CommRing F] (q : Config KA KB → F) (M : Finset (SA × SB))

theorem Q_apply_basisB (s : SA → Fin KA → F) (β : SB → Fin KB) :
    Q q M s (fun v => Pi.single (β v) 1)
      = ∑ α : SA → Fin KA, (∏ u, s u (α u)) * q (xi M α β) := by
  simp only [Q, LinearAlgebra.Multilinear.prod_single_apply]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.sum_eq_single β (fun b _ hb => by simp [hb]) fun hb => absurd (Finset.mem_univ β) hb]
  simp

theorem Q_apply_basisA (α : SA → Fin KA) (w : SB → Fin KB → F) :
    Q q M (fun u => Pi.single (α u) 1) w
      = ∑ β : SB → Fin KB, (∏ v, w v (β v)) * q (xi M α β) := by
  simp only [Q, LinearAlgebra.Multilinear.prod_single_apply]
  rw [Finset.sum_eq_single α (fun a _ ha => by simp [ha]) fun ha => absurd (Finset.mem_univ α) ha]
  refine Finset.sum_congr rfl fun β _ => ?_
  simp

variable (α : SA → Fin KA) (β : SB → Fin KB)

theorem Q_updateA_one_basis (u₀ : SA) :
    Q q M (Function.update (fun u => (Pi.single (α u) 1 : Fin KA → F)) u₀ 1)
        (fun v => Pi.single (β v) 1)
      = ∑ i, q (xi M (Function.update α u₀ i) β) := by
  rw [Q_apply_basisB]
  have h : ∀ α' : SA → Fin KA,
      (∏ u, Function.update (fun u => (Pi.single (α u) 1 : Fin KA → F)) u₀ 1 u (α' u))
        = ∏ u ∈ univ.erase u₀, (Pi.single (α u) (1 : F) : Fin KA → F) (α' u) := by
    intro α'; rw [prod_update]; simp
  simp only [h]
  exact sum_weight_update α u₀ _

theorem Q_updateB_one_basis (v₀ : SB) :
    Q q M (fun u => Pi.single (α u) 1)
        (Function.update (fun v => (Pi.single (β v) 1 : Fin KB → F)) v₀ 1)
      = ∑ j, q (xi M α (Function.update β v₀ j)) := by
  rw [Q_apply_basisA]
  have h : ∀ β' : SB → Fin KB,
      (∏ v, Function.update (fun v => (Pi.single (β v) 1 : Fin KB → F)) v₀ 1 v (β' v))
        = ∏ v ∈ univ.erase v₀, (Pi.single (β v) (1 : F) : Fin KB → F) (β' v) := by
    intro β'; rw [prod_update]; simp
  simp only [h]
  exact sum_weight_update β v₀ _

theorem Q_updateAB_one_basis (u₀ : SA) (v₀ : SB) :
    Q q M (Function.update (fun u => (Pi.single (α u) 1 : Fin KA → F)) u₀ 1)
        (Function.update (fun v => (Pi.single (β v) 1 : Fin KB → F)) v₀ 1)
      = ∑ i, ∑ j, q (xi M (Function.update α u₀ i) (Function.update β v₀ j)) := by
  have hA : ∀ α' : SA → Fin KA,
      (∏ u, Function.update (fun u => (Pi.single (α u) 1 : Fin KA → F)) u₀ 1 u (α' u))
        = ∏ u ∈ univ.erase u₀, (Pi.single (α u) (1 : F) : Fin KA → F) (α' u) := by
    intro α'; rw [prod_update]; simp
  have hB : ∀ β' : SB → Fin KB,
      (∏ v, Function.update (fun v => (Pi.single (β v) 1 : Fin KB → F)) v₀ 1 v (β' v))
        = ∏ v ∈ univ.erase v₀, (Pi.single (β v) (1 : F) : Fin KB → F) (β' v) := by
    intro β'; rw [prod_update]; simp
  simp only [Q, hA, hB]
  rw [← sum_weight_update α u₀
    (fun α' => ∑ j, q (xi M α' (Function.update β v₀ j)))]
  refine Finset.sum_congr rfl fun α' _ => ?_
  rw [Finset.mul_sum, ← sum_weight_update β v₀
    (fun β' => (∏ u ∈ univ.erase u₀, (Pi.single (α u) (1 : F) : Fin KA → F) (α' u))
      * q (xi M α' β'))]
  exact Finset.sum_congr rfl fun β' _ => by ring

end Basis

section Lemma1

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}
variable (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
variable {q : Config KA KB → F} (hq : IsSolution θA θB ρ πA πB q)
variable (M : Finset (SA × SB)) (α : SA → Fin KA) (β : SB → Fin KB)
include hθA hθB hρ hq

theorem Q_kill_freeA (hπA : ∑ i, πA i = 1) {u₀ : SA} (hu₀ : u₀ ∈ freeA M) :
    Q q M (Function.update (fun u => (Pi.single (α u) 1 : Fin KA → F)) u₀ 1)
        (fun v => Pi.single (β v) 1)
      = q ((xi M α β).dropA (α u₀)) := by
  rw [Q_updateA_one_basis]
  simp only [xi_update_freeA α β hu₀]
  exact marginalise_A hθA hθB hρ hπA hq _

theorem Q_kill_domA (hπA : ∑ i, πA i = 1) (hM : IsMatching M) {p : SA × SB} (hp : p ∈ M) :
    Q q M (Function.update (fun u => (Pi.single (α u) 1 : Fin KA → F)) p.1 1)
        (fun v => Pi.single (β v) 1)
      = q ((xi M α β).killA (α p.1) (β p.2)) := by
  rw [Q_updateA_one_basis]
  simp only [xi_update_domA α β hM hp]
  exact marginalise_C hθA hθB hρ hπA hq _ (β p.2)

theorem Q_kill_freeB (hπB : ∑ j, πB j = 1) {v₀ : SB} (hv₀ : v₀ ∈ freeB M) :
    Q q M (fun u => Pi.single (α u) 1)
        (Function.update (fun v => (Pi.single (β v) 1 : Fin KB → F)) v₀ 1)
      = q ((xi M α β).dropB (β v₀)) := by
  rw [Q_updateB_one_basis]
  simp only [xi_update_freeB α β hv₀]
  exact marginalise_B hθA hθB hρ hπB hq _

theorem Q_kill_domB (hπB : ∑ j, πB j = 1) (hM : IsMatching M) {p : SA × SB} (hp : p ∈ M) :
    Q q M (fun u => Pi.single (α u) 1)
        (Function.update (fun v => (Pi.single (β v) 1 : Fin KB → F)) p.2 1)
      = q ((xi M α β).killB (α p.1) (β p.2)) := by
  rw [Q_updateB_one_basis]
  simp only [xi_update_domB α β hM hp]
  exact marginalise_C' hθA hθB hρ hπB hq _ (α p.1)

theorem Q_kill_pair (hπA : ∑ i, πA i = 1) (hπB : ∑ j, πB j = 1) (hM : IsMatching M)
    {p : SA × SB} (hp : p ∈ M) :
    Q q M (Function.update (fun u => (Pi.single (α u) 1 : Fin KA → F)) p.1 1)
        (Function.update (fun v => (Pi.single (β v) 1 : Fin KB → F)) p.2 1)
      = q ((xi M α β).dropC (α p.1) (β p.2)) := by
  rw [Q_updateAB_one_basis]
  simp only [xi_update_pair α β hM hp]
  rw [Finset.sum_comm,
    Finset.sum_congr rfl fun j _ => marginalise_C hθA hθB hρ hπA hq _ j]
  exact marginalise_B hθA hθB hρ hπB hq _

end Lemma1

end Rhone.Probability.Multilinear
