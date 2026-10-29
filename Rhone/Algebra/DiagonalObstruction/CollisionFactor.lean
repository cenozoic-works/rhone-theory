/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.DiagonalObstruction.SpectralPolynomial
public import Mathlib.RingTheory.Polynomial.IsIntegral
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! # Integral factors and labels on the zero-recombination fibre -/

@[expose] public section

namespace Rhone.Algebra.DiagonalObstruction

open Polynomial

attribute [local instance] Polynomial.algebra

theorem monic_factor_coeff_integral
    (p : Polynomial (Polynomial ℤ)) (q : Polynomial (Polynomial ℚ))
    (hp : p.Monic) (hq : q.Monic)
    (hd : q ∣ p.map (algebraMap (Polynomial ℤ) (Polynomial ℚ))) (i j : ℕ) :
    IsIntegral ℤ ((q.coeff i).coeff j) :=
  (Polynomial.isIntegral_coeff_of_dvd p q hp hq hd i).coeff j

theorem exists_monic_integer_lift
    (p : Polynomial (Polynomial ℤ)) (q : Polynomial (Polynomial ℚ))
    (hp : p.Monic) (hq : q.Monic)
    (hd : q ∣ p.map (algebraMap (Polynomial ℤ) (Polynomial ℚ))) :
    ∃ qz : Polynomial (Polynomial ℤ),
      qz.map (algebraMap (Polynomial ℤ) (Polynomial ℚ)) = q ∧
      qz.natDegree = q.natDegree ∧ qz.Monic := by
  apply Polynomial.lifts_and_natDegree_eq_and_monic _ hq
  apply (Polynomial.lifts_iff_coeff_lifts _).2
  intro i
  change q.coeff i ∈ Polynomial.lifts (algebraMap ℤ ℚ)
  apply (Polynomial.lifts_iff_coeff_lifts _).2
  intro j
  exact IsIntegrallyClosed.isIntegral_iff.mp (monic_factor_coeff_integral p q hp hq hd i j)

theorem exists_monic_integer_factor
    (p : Polynomial (Polynomial ℤ)) (q : Polynomial (Polynomial ℚ))
    (hp : p.Monic) (hq : q.Monic)
    (hd : q ∣ p.map (algebraMap (Polynomial ℤ) (Polynomial ℚ))) :
    ∃ qz : Polynomial (Polynomial ℤ),
      qz.map (algebraMap (Polynomial ℤ) (Polynomial ℚ)) = q ∧
      qz.natDegree = q.natDegree ∧ qz.Monic ∧ qz ∣ p := by
  obtain ⟨qz, hmap, hdeg, hmon⟩ := exists_monic_integer_lift p q hp hq hd
  obtain ⟨r, hr⟩ := hd
  have hrmon : r.Monic := hq.of_mul_monic_left (hr ▸ hp.map _)
  have hrdvd : r ∣ p.map (algebraMap (Polynomial ℤ) (Polynomial ℚ)) := by
    rw [hr]
    exact dvd_mul_left _ _
  obtain ⟨rz, hrmap, _, _⟩ := exists_monic_integer_lift p r hp hrmon hrdvd
  refine ⟨qz, hmap, hdeg, hmon, rz, ?_⟩
  apply Polynomial.map_injective (algebraMap (Polynomial ℤ) (Polynomial ℚ))
    (Polynomial.map_injective (algebraMap ℤ ℚ) (Int.cast_injective))
  simpa only [Polynomial.map_mul, hmap, hrmap] using hr

noncomputable def factorLabels (m : ℕ) (f : Polynomial (Polynomial ℤ)) : Finset ℕ :=
  (Finset.range (m + 1)).filter fun t =>
    (f.map (Polynomial.evalRingHom (0 : ℤ))).eval (coalDiag m t) = 0

@[simp] theorem mem_factorLabels (m t : ℕ) (f : Polynomial (Polynomial ℤ)) :
    t ∈ factorLabels m f ↔ t ≤ m ∧
      (f.map (Polynomial.evalRingHom (0 : ℤ))).eval (coalDiag m t) = 0 := by
  simp [factorLabels]

theorem zero_mem_factorLabels (m : ℕ) (f : Polynomial (Polynomial ℤ))
    (h : (f.map (Polynomial.evalRingHom (0 : ℤ))).eval (coalDiag m 0) = 0) :
    0 ∈ factorLabels m f := by
  simp [h]

theorem coalDiag_injOn_range {m : ℕ} (hm : 1 ≤ m) :
    Set.InjOn (coalDiag m) (Finset.range (m + 1)) := by
  intro i hi j hj h
  by_contra hne
  exact coalDiag_ne hm (by simpa using hi) (by simpa using hj) hne h

theorem spectralPolynomial_zero_roots {m : ℕ} (hm : 1 ≤ m) :
    ((spectralPolynomial m).map (Polynomial.evalRingHom (0 : ℤ))).roots =
      ((Finset.range (m + 1)).image (coalDiag m)).val := by
  have hprod : (spectralPolynomial m).map (Polynomial.evalRingHom (0 : ℤ)) =
      ∏ r ∈ (Finset.range (m + 1)).image (coalDiag m), (X - C r) := by
    rw [spectralPolynomial_zero_fiber, Finset.prod_image (coalDiag_injOn_range hm)]
    exact Fin.prod_univ_eq_prod_range (fun t => (X : ℤ[X]) - C (coalDiag m t)) (m + 1)
  rw [hprod, Polynomial.roots_prod_X_sub_C]

theorem factor_zero_roots {m : ℕ} (hm : 1 ≤ m)
    (f : Polynomial (Polynomial ℤ)) (hf : f.Monic) (hd : f ∣ spectralPolynomial m) :
    (f.map (Polynomial.evalRingHom (0 : ℤ))).roots =
      ((factorLabels m f).image (coalDiag m)).val := by
  have hmono := hf.map (Polynomial.evalRingHom (0 : ℤ))
  have hle := Polynomial.roots.le_of_dvd
    ((spectralPolynomial_monic m).map (Polynomial.evalRingHom (0 : ℤ))).ne_zero
    (Polynomial.map_dvd (Polynomial.evalRingHom (0 : ℤ)) hd)
  rw [spectralPolynomial_zero_roots hm] at hle
  have hnd : (f.map (Polynomial.evalRingHom (0 : ℤ))).roots.Nodup :=
    Multiset.nodup_of_le hle (Finset.nodup _)
  apply (Multiset.Nodup.ext hnd (Finset.nodup _)).2
  intro r
  constructor
  · intro hr
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp (Multiset.mem_of_le hle hr)
    change coalDiag m t ∈ (factorLabels m f).image (coalDiag m)
    apply Finset.mem_image.mpr
    refine ⟨t, (mem_factorLabels m t f).2 ⟨by simpa using ht, ?_⟩, rfl⟩
    exact (Polynomial.mem_roots hmono.ne_zero).mp hr
  · intro hr
    change r ∈ (factorLabels m f).image (coalDiag m) at hr
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hr
    exact (Polynomial.mem_roots hmono.ne_zero).2 ((mem_factorLabels m t f).mp ht).2

theorem factor_zero_fiber_eq_prod {m : ℕ} (hm : 1 ≤ m)
    (f : Polynomial (Polynomial ℤ)) (hf : f.Monic) (hd : f ∣ spectralPolynomial m) :
    f.map (Polynomial.evalRingHom (0 : ℤ)) =
      ∏ t ∈ factorLabels m f, (X - C (coalDiag m t)) := by
  have hs : ((spectralPolynomial m).map (Polynomial.evalRingHom (0 : ℤ))).Splits := by
    rw [spectralPolynomial_zero_fiber]
    exact Polynomial.Splits.prod fun _ _ => Polynomial.Splits.X_sub_C _
  have hfs := hs.of_dvd
    ((spectralPolynomial_monic m).map (Polynomial.evalRingHom (0 : ℤ))).ne_zero
    (Polynomial.map_dvd (Polynomial.evalRingHom (0 : ℤ)) hd)
  rw [hfs.eq_prod_roots_of_monic (hf.map _), factor_zero_roots hm f hf hd]
  change (∏ r ∈ (factorLabels m f).image (coalDiag m), (X - C r)) = _
  apply Finset.prod_image
  intro i hi j hj h
  apply coalDiag_injOn_range hm _ _ h
  · simpa using ((mem_factorLabels m i f).mp hi).1
  · simpa using ((mem_factorLabels m j f).mp hj).1

theorem factorLabels_card {m : ℕ} (hm : 1 ≤ m)
    (f : Polynomial (Polynomial ℤ)) (hf : f.Monic) (hd : f ∣ spectralPolynomial m) :
    (factorLabels m f).card = f.natDegree := by
  have hdeg := congrArg Polynomial.natDegree (factor_zero_fiber_eq_prod hm f hf hd)
  rw [hf.natDegree_map, Polynomial.natDegree_prod_of_monic _ _
    (fun t _ => Polynomial.monic_X_sub_C (coalDiag m t))] at hdeg
  simpa only [Polynomial.natDegree_X_sub_C, Finset.sum_const, nsmul_eq_mul,
    Nat.cast_id, mul_one]
    using hdeg.symm

theorem factor_zero_fiber_derivative {m i : ℕ} (hm : 1 ≤ m)
    (f : Polynomial (Polynomial ℤ)) (hf : f.Monic) (hd : f ∣ spectralPolynomial m)
    (hi : i ∈ factorLabels m f) :
    (f.map (Polynomial.evalRingHom (0 : ℤ))).derivative.eval (coalDiag m i) =
      ∏ t ∈ (factorLabels m f).erase i, (coalDiag m i - coalDiag m t) := by
  rw [factor_zero_fiber_eq_prod hm f hf hd, ← Finset.mul_prod_erase _ _ hi]
  simp [Polynomial.derivative_mul, Polynomial.eval_prod]

private theorem exists_irreducible_in_kernel
    {A B : Type*} [CommRing A] [IsDomain A] [WfDvdMonoid A]
    [CommRing B] [IsDomain B] (φ : A →+* B) (p : A)
    (hp : p ≠ 0) (hzero : φ p = 0) :
    ∃ g : A, Irreducible g ∧ g ∣ p ∧ φ g = 0 := by
  have h : ∀ p : A, p ≠ 0 → φ p = 0 →
      ∃ g : A, Irreducible g ∧ g ∣ p ∧ φ g = 0 := by
    intro p
    induction p using WfDvdMonoid.induction_on_irreducible with
    | zero => intro hp; exact (hp rfl).elim
    | unit u hu => intro _ hz; exact ((hu.map φ).ne_zero hz).elim
    | mul a i ha hi ih =>
      intro _ hz
      rcases mul_eq_zero.mp (by simpa only [map_mul] using hz) with hi0 | ha0
      · exact ⟨i, hi, dvd_mul_right _ _, hi0⟩
      · obtain ⟨g, hg, hgd, hg0⟩ := ih ha ha0
        exact ⟨g, hg, hgd.trans (dvd_mul_left _ _), hg0⟩
  exact h p hp hzero

theorem integer_factor_zero_fiber_map (f : Polynomial (Polynomial ℤ)) :
    (f.map (algebraMap (Polynomial ℤ) (Polynomial ℚ))).map
      (Polynomial.evalRingHom (0 : ℚ)) =
    (f.map (Polynomial.evalRingHom (0 : ℤ))).map (algebraMap ℤ ℚ) := by
  rw [Polynomial.map_map, Polynomial.map_map]
  congr 1
  ext <;> simp [Polynomial.algebraMap_def]

theorem exists_monic_rational_factor_zero (m : ℕ) :
    ∃ q : Polynomial (Polynomial ℚ), q.Monic ∧ Irreducible q ∧
      q ∣ (spectralPolynomial m).map (algebraMap (Polynomial ℤ) (Polynomial ℚ)) ∧
      (q.map (Polynomial.evalRingHom (0 : ℚ))).eval (coalDiag m 0 : ℚ) = 0 := by
  let p := (spectralPolynomial m).map (algebraMap (Polynomial ℤ) (Polynomial ℚ))
  let φ : Polynomial (Polynomial ℚ) →+* ℚ :=
    (Polynomial.evalRingHom (coalDiag m 0 : ℚ)).comp
      (Polynomial.mapRingHom (Polynomial.evalRingHom (0 : ℚ)))
  have hp : p.Monic := (spectralPolynomial_monic m).map _
  have hzero : φ p = 0 := by
    change (((spectralPolynomial m).map (algebraMap (Polynomial ℤ) (Polynomial ℚ))).map
      (Polynomial.evalRingHom (0 : ℚ))).eval (coalDiag m 0 : ℚ) = 0
    rw [integer_factor_zero_fiber_map, spectralPolynomial_zero_fiber]
    simp only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rw [Fin.prod_univ_succ]
    simp
  obtain ⟨g, hirr, hgdiv, hgzero⟩ := exists_irreducible_in_kernel φ p hp.ne_zero hzero
  have hlc := hp.isUnit_leadingCoeff_of_dvd hgdiv
  let q := C (↑hlc.unit⁻¹ : Polynomial ℚ) * g
  have hq : q.Monic := by
    change (C (↑hlc.unit⁻¹ : Polynomial ℚ) * g).leadingCoeff = 1
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
    have hu : (↑hlc.unit⁻¹ : Polynomial ℚ) * ↑hlc.unit = 1 := by simp
    simpa only [hlc.unit_spec] using hu
  have hassoc : Associated g q := by
    exact associated_unit_mul_right _ _ (Polynomial.isUnit_C.mpr (Units.isUnit _))
  refine ⟨q, hq, hassoc.irreducible hirr, hassoc.dvd_iff_dvd_left.mp hgdiv, ?_⟩
  change φ q = 0
  change φ (C (↑hlc.unit⁻¹ : Polynomial ℚ) * g) = 0
  rw [map_mul, hgzero, mul_zero]

theorem exists_monic_integer_factor_zero (m : ℕ) :
    ∃ f : Polynomial (Polynomial ℤ), f.Monic ∧ f ∣ spectralPolynomial m ∧
      Irreducible (f.map (algebraMap (Polynomial ℤ) (Polynomial ℚ))) ∧
      0 ∈ factorLabels m f := by
  obtain ⟨q, hq, hirr, hd, hz⟩ := exists_monic_rational_factor_zero m
  obtain ⟨f, hfmap, _, hfmon, hfdiv⟩ := exists_monic_integer_factor
    (spectralPolynomial m) q (spectralPolynomial_monic m) hq hd
  refine ⟨f, hfmon, hfdiv, ?_, zero_mem_factorLabels m f ?_⟩
  · simpa only [hfmap] using hirr
  · rw [← hfmap, integer_factor_zero_fiber_map] at hz
    change ((f.map (Polynomial.evalRingHom (0 : ℤ))).map (algebraMap ℤ ℚ)).eval
      ((algebraMap ℤ ℚ) (coalDiag m 0)) = 0 at hz
    rw [Polynomial.eval_map_apply] at hz
    have hz' := hz
    exact (Int.cast_injective : Function.Injective (algebraMap ℤ ℚ)) (by simpa using hz')

end Rhone.Algebra.DiagonalObstruction
