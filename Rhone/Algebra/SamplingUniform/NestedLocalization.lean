/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.SamplingUniform.TranscendentalIrreducibility
public import Mathlib.Algebra.MvPolynomial.Equiv

/-! # Successively localize the independent lambda and two frequency variables -/

@[expose] public section

namespace Rhone.Algebra.SamplingUniform

open Polynomial

variable {K : Type*} [Field K]

noncomputable def swapLocal : K[X][X] →+* (RatFunc K)[X] :=
  (Polynomial.mapRingHom (algebraMap K[X] (RatFunc K))).comp
    (Polynomial.Bivariate.swap (R := K)).toRingHom

@[simp] theorem swapLocal_C (f : K[X]) :
    swapLocal (Polynomial.C f) = f.map (RatFunc.C : K →+* RatFunc K) := by
  change (Polynomial.Bivariate.swap (Polynomial.C f)).map _ = _
  rw [Polynomial.Bivariate.swap_C, Polynomial.map_map]
  congr 1

theorem swapLocal_dvd_iff (f : K[X]) (hf : f ≠ 0) (P : K[X][X]) :
    f.map (RatFunc.C : K →+* RatFunc K) ∣ swapLocal P ↔ Polynomial.C f ∣ P := by
  change f.map RatFunc.C ∣ (Polynomial.Bivariate.swap P).map _ ↔ _
  rw [map_ratFunc_C_dvd_iff_swap f hf, Polynomial.Bivariate.swap_swap_apply]

noncomputable def frequencyEquiv (R : Type*) [CommRing R] :
    MvPolynomial (Fin 2) R ≃ₐ[R] R[X][X] :=
  (MvPolynomial.finSuccEquiv R 1).trans
    (Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv R (Fin 1)))

@[simp] theorem frequencyEquiv_C {R : Type*} [CommRing R] (a : R) :
    frequencyEquiv R (MvPolynomial.C a) = Polynomial.C (Polynomial.C a) := by
  simp [frequencyEquiv, MvPolynomial.finSuccEquiv_apply]

@[simp] theorem frequencyEquiv_X_zero {R : Type*} [CommRing R] :
    frequencyEquiv R (MvPolynomial.X (0 : Fin 2)) = Polynomial.X := by
  simp [frequencyEquiv, MvPolynomial.finSuccEquiv_X_zero]

@[simp] theorem frequencyEquiv_X_one {R : Type*} [CommRing R] :
    frequencyEquiv R (MvPolynomial.X (1 : Fin 2)) = Polynomial.C Polynomial.X := by
  change Polynomial.map _
    ((MvPolynomial.finSuccEquiv R 1) (MvPolynomial.X (0 : Fin 1).succ)) = _
  rw [MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C]
  congr 1
  simp [MvPolynomial.uniqueAlgEquiv]

@[simp] theorem swapLocal_X :
    swapLocal (Polynomial.X : K[X][X]) = Polynomial.C RatFunc.X := by
  change (Polynomial.Bivariate.swap (Polynomial.X : K[X][X])).map _ = _
  rw [Polynomial.Bivariate.swap_Y, Polynomial.map_C]
  rfl

noncomputable def nestedConstant : K →+* RatFunc (RatFunc (RatFunc K)) :=
  RatFunc.C.comp (RatFunc.C.comp RatFunc.C)

noncomputable def nestedLocalization :
    MvPolynomial (Fin 2) K[X][X] →+* (RatFunc (RatFunc (RatFunc K)))[X] :=
  (swapLocal (K := RatFunc (RatFunc K))).comp
    ((Polynomial.mapRingHom (swapLocal (K := RatFunc K))).comp
      ((frequencyEquiv ((RatFunc K)[X])).toRingHom.comp (MvPolynomial.map swapLocal)))

theorem mv_swapLocal_dvd_iff {σ : Type*} (f : K[X]) (hf : f ≠ 0)
    (N : MvPolynomial σ K[X][X]) :
    MvPolynomial.C (f.map (RatFunc.C : K →+* RatFunc K)) ∣
        MvPolynomial.map swapLocal N ↔ MvPolynomial.C (Polynomial.C f) ∣ N := by
  rw [MvPolynomial.C_dvd_iff_dvd_coeff, MvPolynomial.C_dvd_iff_dvd_coeff]
  simp only [MvPolynomial.coeff_map, swapLocal_dvd_iff f hf]

theorem poly_swapLocal_dvd_iff (f : K[X]) (hf : f ≠ 0) (N : K[X][X][X]) :
    Polynomial.C (f.map (RatFunc.C : K →+* RatFunc K)) ∣
        N.map swapLocal ↔ Polynomial.C (Polynomial.C f) ∣ N := by
  rw [Polynomial.C_dvd_iff_dvd_coeff, Polynomial.C_dvd_iff_dvd_coeff]
  simp only [Polynomial.coeff_map, swapLocal_dvd_iff f hf]

@[simp] theorem nestedLocalization_C (f : K[X]) :
    nestedLocalization (MvPolynomial.C (Polynomial.C f)) = f.map nestedConstant := by
  simp [nestedLocalization, nestedConstant, Polynomial.map_map]

theorem nestedLocalization_dvd_iff (f : K[X]) (hf : f ≠ 0)
    (N : MvPolynomial (Fin 2) K[X][X]) :
    f.map nestedConstant ∣ nestedLocalization N ↔
      MvPolynomial.C (Polynomial.C f) ∣ N := by
  let f₁ := f.map (RatFunc.C : K →+* RatFunc K)
  let f₂ := f₁.map (RatFunc.C : RatFunc K →+* RatFunc (RatFunc K))
  have hf₁ : f₁ ≠ 0 := Polynomial.map_ne_zero hf
  have hf₂ : f₂ ≠ 0 := Polynomial.map_ne_zero hf₁
  have hmap : f.map nestedConstant = f₂.map RatFunc.C := by
    simp [f₂, f₁, nestedConstant, Polynomial.map_map]
  rw [hmap]
  change f₂.map RatFunc.C ∣ swapLocal
    ((frequencyEquiv ((RatFunc K)[X]) (MvPolynomial.map swapLocal N)).map swapLocal) ↔ _
  rw [swapLocal_dvd_iff f₂ hf₂, poly_swapLocal_dvd_iff f₁ hf₁]
  have he : Polynomial.C (Polynomial.C f₁) ∣
      frequencyEquiv ((RatFunc K)[X]) (MvPolynomial.map swapLocal N) ↔
      MvPolynomial.C f₁ ∣ MvPolynomial.map swapLocal N := by
    rw [← frequencyEquiv_C]
    exact map_dvd_iff (frequencyEquiv ((RatFunc K)[X]))
  rw [he, mv_swapLocal_dvd_iff f hf]

@[simp] theorem nestedLocalization_theta :
    nestedLocalization (MvPolynomial.C (Polynomial.C (Polynomial.X : K[X]))) =
      Polynomial.X := by
  rw [nestedLocalization_C, Polynomial.map_X]

@[simp] theorem nestedLocalization_lambda :
    nestedLocalization (MvPolynomial.C (Polynomial.X : K[X][X])) =
      Polynomial.C (RatFunc.C (RatFunc.C (RatFunc.X : RatFunc K))) := by
  simp [nestedLocalization, Polynomial.map_C]

@[simp] theorem nestedLocalization_p :
    nestedLocalization (MvPolynomial.X (0 : Fin 2)) =
      Polynomial.C (RatFunc.X : RatFunc (RatFunc (RatFunc K))) := by
  simp [nestedLocalization]

@[simp] theorem nestedLocalization_r :
    nestedLocalization (MvPolynomial.X (1 : Fin 2)) =
      Polynomial.C (RatFunc.C (RatFunc.X : RatFunc (RatFunc K))) := by
  simp [nestedLocalization, Polynomial.map_C]

@[simp] theorem nestedLocalization_scalar (a : K) :
    nestedLocalization (MvPolynomial.C (Polynomial.C (Polynomial.C a))) =
      Polynomial.C (nestedConstant a) := by
  rw [nestedLocalization_C, Polynomial.map_C]

theorem nestedLocalization_eval₂ {S : Type*} [CommRing S]
    (φ : RatFunc (RatFunc (RatFunc K)) →+* S) (θ : S)
    (N : MvPolynomial (Fin 2) K[X][X]) :
    (nestedLocalization N).eval₂ φ θ =
      MvPolynomial.eval₂
        (Polynomial.eval₂RingHom
          (Polynomial.eval₂RingHom (φ.comp nestedConstant) θ)
          (φ (RatFunc.C (RatFunc.C (RatFunc.X : RatFunc K)))))
        ![φ (RatFunc.X : RatFunc (RatFunc (RatFunc K))),
          φ (RatFunc.C (RatFunc.X : RatFunc (RatFunc K)))] N := by
  have hh : (Polynomial.eval₂RingHom φ θ).comp nestedLocalization =
      MvPolynomial.eval₂Hom
        (Polynomial.eval₂RingHom
          (Polynomial.eval₂RingHom (φ.comp nestedConstant) θ)
          (φ (RatFunc.C (RatFunc.C (RatFunc.X : RatFunc K)))))
        ![φ (RatFunc.X : RatFunc (RatFunc (RatFunc K))),
          φ (RatFunc.C (RatFunc.X : RatFunc (RatFunc K)))] := by
    apply MvPolynomial.ringHom_ext
    · intro a
      have hc : ((Polynomial.eval₂RingHom φ θ).comp nestedLocalization).comp
          MvPolynomial.C =
          Polynomial.eval₂RingHom
            (Polynomial.eval₂RingHom (φ.comp nestedConstant) θ)
            (φ (RatFunc.C (RatFunc.C (RatFunc.X : RatFunc K)))) := by
        ext a
        · simp
        · simp
        · simp
      simpa only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C] using
        RingHom.congr_fun hc a
    · intro i
      fin_cases i <;> simp
  exact RingHom.congr_fun hh N

theorem irreducible_map_nestedConstant (f : K[X]) (hf : Irreducible f) :
    Irreducible (f.map nestedConstant) := by
  have h₁ := irreducible_map_ratFunc_C f hf
  have h₂ := irreducible_map_ratFunc_C _ h₁
  have h₃ := irreducible_map_ratFunc_C _ h₂
  simpa only [Polynomial.map_map, nestedConstant] using h₃

@[simp] theorem natDegree_map_nestedConstant (f : K[X]) :
    (f.map nestedConstant).natDegree = f.natDegree :=
  Polynomial.natDegree_map_eq_of_injective (RingHom.injective (nestedConstant (K := K))) f

end Rhone.Algebra.SamplingUniform
