/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Polynomial.Basic

/-! # From a transitive automorphism action to irreducibility -/

@[expose] public section

namespace Rhone.Algebra.GaloisIrreducibility

open Polynomial

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

theorem rootSet_subset_of_transitive {f g : F[X]} (hf0 : f ≠ 0) (hg : g ∣ f)
    (hgd : g.natDegree ≠ 0) (hsp : (f.map (algebraMap F E)).Splits)
    (htrans : ∀ x ∈ f.rootSet E, ∀ y ∈ f.rootSet E, ∃ σ : E ≃ₐ[F] E, σ x = y) :
    f.rootSet E ⊆ g.rootSet E := by
  have hinj : Function.Injective (algebraMap F E) := (algebraMap F E).injective
  have hfm0 : f.map (algebraMap F E) ≠ 0 := Polynomial.map_ne_zero_iff hinj |>.mpr hf0
  have hgm : g.map (algebraMap F E) ∣ f.map (algebraMap F E) := Polynomial.map_dvd _ hg
  have hgsp : (g.map (algebraMap F E)).Splits := hsp.of_dvd hfm0 hgm
  have hgdm : (g.map (algebraMap F E)).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective hinj]
    exact fun h => hgd (Polynomial.natDegree_eq_zero_iff_degree_le_zero.mpr (le_of_eq h))
  obtain ⟨x₀, hx₀⟩ := hgsp.exists_eval_eq_zero hgdm
  have hg0 : g ≠ 0 := fun h => hgd (by simp [h])
  have hax₀ : aeval x₀ g = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map]
    exact hx₀
  have hx₀f : x₀ ∈ f.rootSet E := by
    obtain ⟨c, rfl⟩ := hg
    refine Polynomial.mem_rootSet'.mpr ⟨hfm0, ?_⟩
    rw [map_mul, hax₀, zero_mul]
  intro y hy
  obtain ⟨σ, hσ⟩ := htrans x₀ hx₀f y hy
  have hgm0 : g.map (algebraMap F E) ≠ 0 := Polynomial.map_ne_zero_iff hinj |>.mpr hg0
  refine Polynomial.mem_rootSet'.mpr ⟨hgm0, ?_⟩
  rw [← hσ]
  simpa [hax₀] using Polynomial.aeval_algHom_apply σ.toAlgHom x₀ g

theorem irreducible_of_transitive {f : F[X]} (hsep : f.Separable)
    (hsp : (f.map (algebraMap F E)).Splits) (hdeg : f.natDegree ≠ 0)
    (htrans : ∀ x ∈ f.rootSet E, ∀ y ∈ f.rootSet E, ∃ σ : E ≃ₐ[F] E, σ x = y) :
    Irreducible f := by
  have hf0 : f ≠ 0 := fun h => hdeg (by simp [h])
  have hcard : (f.rootSet E).ncard = f.natDegree := by
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
    exact card_rootSet_eq_natDegree hsep hsp
  refine ⟨fun hu => hdeg (Polynomial.natDegree_eq_zero_of_isUnit hu), fun a b hab => ?_⟩
  by_contra hcon
  have ha : ¬ IsUnit a := fun h => hcon (Or.inl h)
  have hb : ¬ IsUnit b := fun h => hcon (Or.inr h)
  have ha0 : a ≠ 0 := by rintro rfl; exact hf0 (by simp [hab])
  have hb0 : b ≠ 0 := by rintro rfl; exact hf0 (by simp [hab])
  have had : a.natDegree ≠ 0 := by
    intro h
    obtain ⟨c, rfl⟩ := Polynomial.natDegree_eq_zero.mp h
    exact ha (isUnit_C.mpr (isUnit_iff_ne_zero.mpr (fun hc => ha0 (by simp [hc]))))
  have hbd : b.natDegree ≠ 0 := by
    intro h
    obtain ⟨c, rfl⟩ := Polynomial.natDegree_eq_zero.mp h
    exact hb (isUnit_C.mpr (isUnit_iff_ne_zero.mpr (fun hc => hb0 (by simp [hc]))))
  have hsub : f.rootSet E ⊆ a.rootSet E :=
    rootSet_subset_of_transitive hf0 ⟨b, hab⟩ had hsp htrans
  have h1 : f.natDegree ≤ a.natDegree := by
    rw [← hcard]
    exact le_trans (Set.ncard_le_ncard hsub (Polynomial.rootSet_finite a E))
      (Polynomial.ncard_rootSet_le a E)
  rw [hab, Polynomial.natDegree_mul ha0 hb0] at h1
  omega

end Rhone.Algebra.GaloisIrreducibility
