/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.PolynomialEncodingProof

/-! # Exact coefficients of the executable polynomial map -/

@[expose] public section
namespace Rhone.Computation.PolynomialEncoding

private theorem listCoefficient_of_absent (terms : List (Key × Rat)) (key : Key)
    (h : key ∉ terms.map Prod.fst) : listCoefficient terms key = 0 := by
  apply List.sum_eq_zero
  intro v hv
  obtain ⟨term, ht, rfl⟩ := List.mem_map.mp hv
  exact ite_eq_right (fun he => h (List.mem_map.mpr ⟨term, ht, he⟩))

private theorem listCoefficient_of_mem (terms : List (Key × Rat))
    (hn : (terms.map Prod.fst).Nodup) (key : Key) (v : Rat)
    (hm : (key, v) ∈ terms) : listCoefficient terms key = v := by
  induction terms with
  | nil => simp at hm
  | cons term terms ih =>
    obtain ⟨ha, ht⟩ := List.nodup_cons.mp hn
    rcases List.mem_cons.mp hm with he | hm
    · subst term
      have hz := listCoefficient_of_absent terms key ha
      change (if key = key then v else 0) + listCoefficient terms key = v
      simp [hz]
    · have he : term.1 ≠ key := by
        intro he
        apply ha
        rw [he]
        exact List.mem_map.mpr ⟨(key, v), hm, rfl⟩
      change (if term.1 = key then term.2 else 0) + listCoefficient terms key = v
      rw [ite_eq_right he, zero_add]
      exact ih ht hm

theorem hashMap_keys_nodup (m : Std.HashMap Key Rat) :
    (m.toArray.toList.map Prod.fst).Nodup := by
  simpa only [Std.HashMap.toList_toArray, Std.HashMap.map_fst_toList_eq_keys]
    using m.nodup_keys

theorem coeff_reflect_hashMap (m : Std.HashMap Key Rat) (key : Key) :
    (reflect m.toArray).coeff (exponent key) = m.getD key 0 := by
  rw [coeff_reflect, Std.HashMap.toList_toArray]
  have hn : (m.toList.map Prod.fst).Nodup := by
    simpa only [Std.HashMap.map_fst_toList_eq_keys] using m.nodup_keys
  cases hg : m[key]? with
  | none =>
    have ha : key ∉ m.toList.map Prod.fst := by
      intro hm
      obtain ⟨⟨k, v⟩, hm, hk⟩ := List.mem_map.mp hm
      change k = key at hk
      subst k
      have hs := Std.HashMap.mem_toList_iff_getElem?_eq_some.mp hm
      rw [hg] at hs
      contradiction
    rw [listCoefficient_of_absent _ _ ha]
    simp [Std.HashMap.getD_eq_getD_getElem?, hg]
  | some v =>
    rw [listCoefficient_of_mem _ hn key v
      (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hg)]
    simp [Std.HashMap.getD_eq_getD_getElem?, hg]

theorem reflect_hashMap_update (m : Std.HashMap Key Rat) (key : Key) (delta : Rat) :
    reflect ((if m.getD key 0 + delta == 0 then m.erase key
      else m.insert key (m.getD key 0 + delta)).toArray) =
      reflect m.toArray + MvPolynomial.monomial (exponent key) delta := by
  apply MvPolynomial.ext
  intro d
  obtain ⟨query, rfl⟩ := exponent_surjective d
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_reflect_hashMap,
    MvPolynomial.coeff_monomial]
  by_cases hz : m.getD key 0 + delta = 0
  · simp only [hz, beq_self_eq_true, ite_true, coeff_reflect_hashMap]
    rw [Std.HashMap.getD_erase]
    by_cases hk : key = query
    · subst query
      simpa using hz.symm
    · have hd : exponent key ≠ exponent query := fun h => hk (exponent_injective h)
      simp [hk, hd]
  · simp only [beq_iff_eq, hz, ite_false, coeff_reflect_hashMap]
    rw [Std.HashMap.getD_insert]
    by_cases hk : key = query
    · subst query
      simp
    · have hd : exponent key ≠ exponent query := fun h => hk (exponent_injective h)
      simp [hk, hd]

end Rhone.Computation.PolynomialEncoding
