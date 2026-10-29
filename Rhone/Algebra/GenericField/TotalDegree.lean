/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.GenericField.Tower
public import Rhone.Algebra.NoDegreeOneFormula
public import Rhone.Algebra.NoDegreeTwoFormula

/-! # The total-degree bridge: the paper's Definition 2.2 implies the Lean one -/

@[expose] public section

namespace Rhone.Algebra.GenericField

open Polynomial

theorem natDegree_eval₂_le {S R : Type*} [CommSemiring S] [CommSemiring R]
    (c : S →+* Polynomial R) (hc : ∀ a : S, (c a).natDegree = 0)
    (g : Fin 3 → Polynomial R) (hg : ∀ i, (g i).natDegree ≤ 1)
    (f : MvPolynomial (Fin 3) S) :
    (MvPolynomial.eval₂ c g f).natDegree ≤ f.totalDegree := by
  rw [MvPolynomial.eval₂_eq]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
  intro d hd
  refine le_trans Polynomial.natDegree_mul_le ?_
  rw [hc, zero_add]
  refine le_trans (Polynomial.natDegree_prod_le d.support (fun i => g i ^ d i)) ?_
  refine le_trans (Finset.sum_le_sum (fun i _ => ?_)) (MvPolynomial.le_totalDegree hd)
  exact le_trans Polynomial.natDegree_pow_le (by simpa using Nat.mul_le_mul_left (d i) (hg i))

variable (K : Type*) [Field K]

noncomputable def coeffHom : K →+* P K :=
  (Polynomial.C).comp ((algebraMap (Fv K) (Fuv K)).comp (algebraMap K (Fv K)))

noncomputable def genRho : Fin 3 → P K :=
  ![C ((uu K + vv K) / 2), C ((uu K - vv K) / 2), X]

noncomputable def evP : MvPolynomial (Fin 3) K →+* P K :=
  MvPolynomial.eval₂Hom (coeffHom K) (genRho K)

noncomputable def evL : MvPolynomial (Fin 3) K →+* L K :=
  (algebraMap (P K) (L K)).comp (evP K)

theorem evL_apply (m : MvPolynomial (Fin 3) K) :
    evL K m = algebraMap (P K) (L K) (evP K m) := rfl

theorem genRho_natDegree_le (i : Fin 3) : (genRho K i).natDegree ≤ 1 := by
  fin_cases i <;> simp [genRho]

theorem natDegree_evP_le (m : MvPolynomial (Fin 3) K) :
    (evP K m).natDegree ≤ m.totalDegree := by
  rw [evP, MvPolynomial.coe_eval₂Hom]
  exact natDegree_eval₂_le _ (fun a => by simp [coeffHom]) _ (genRho_natDegree_le K) m

theorem evL_X_zero : evL K (MvPolynomial.X 0) = thA K := by
  simp [evL, evP, genRho, thA, RatFunc.algebraMap_C]

theorem evL_X_one : evL K (MvPolynomial.X 1) = thB K := by
  simp [evL, evP, genRho, thB, RatFunc.algebraMap_C]

theorem evL_X_two : evL K (MvPolynomial.X 2) = rhoL K := by
  simp [evL, evP, genRho, rhoL, RatFunc.algebraMap_X]

inductive TotalDAdm (D : ℕ) : Expr (Fuv K) → Prop
  | const (q : ℚ) : TotalDAdm D (.const q)
  | coeff (x : Fuv K) : TotalDAdm D (.coeff x)
  | thA : TotalDAdm D .thA
  | thB : TotalDAdm D .thB
  | rho : TotalDAdm D .rho
  | add {x y : Expr (Fuv K)} : TotalDAdm D x → TotalDAdm D y → TotalDAdm D (.add x y)
  | mul {x y : Expr (Fuv K)} : TotalDAdm D x → TotalDAdm D y → TotalDAdm D (.mul x y)
  | div {x g : Expr (Fuv K)} (hx : TotalDAdm D x) (hg : TotalDAdm D g)
      (m : MvPolynomial (Fin 3) K) (hm : m.totalDegree ≤ D) (hne : evL K m ≠ 0)
      (hval : Expr.eval (_root_.Rhone.Algebra.GenericField.thA K)
          (_root_.Rhone.Algebra.GenericField.thB K)
        (_root_.Rhone.Algebra.GenericField.rhoL K) g = evL K m) :
      TotalDAdm D (.div x g)

variable {K}

theorem TotalDAdm.toDAdm {D : ℕ} {e : Expr (Fuv K)} (h : TotalDAdm K D e) :
    DAdm (_root_.Rhone.Algebra.GenericField.thA K) (_root_.Rhone.Algebra.GenericField.thB K)
      (_root_.Rhone.Algebra.GenericField.rhoL K) D e := by
  induction h with
  | const q => exact .const q
  | coeff x => exact .coeff x
  | thA => exact .thA
  | thB => exact .thB
  | rho => exact .rho
  | add _ _ ihx ihy => exact .add ihx ihy
  | mul _ _ ihx ihy => exact .mul ihx ihy
  | div _ _ m hm hne hval ihx ihg =>
      refine .div ihx ihg (evP K m) ?_ (le_trans (natDegree_evP_le K m) hm) hval
      intro h0
      exact hne (by rw [evL_apply, h0, map_zero])

theorem totalDAdm_div_rho {D : ℕ} (hD : 1 ≤ D) {x : Expr (Fuv K)} (hx : TotalDAdm K D x) :
    TotalDAdm K D (.div x .rho) :=
  .div hx .rho (MvPolynomial.X 2) (by simpa using hD)
    (by rw [evL_X_two]; exact RatFunc.X_ne_zero) (by rw [evL_X_two]; rfl)

theorem no_degree_one_formula_total :
    ¬ ∃ e : Expr (Fuv ℚ), TotalDAdm ℚ 1 e
        ∧ Expr.eval (thA ℚ) (thB ℚ) (rhoL ℚ) e = _root_.Rhone.Algebra.q22 := by
  rintro ⟨e, he, hval⟩
  exact _root_.Rhone.Algebra.no_degree_one_formula ⟨e, he.toDAdm, hval⟩

theorem two_le_degree_of_formula_total {D : ℕ} {e : Expr (Fuv ℚ)} (he : TotalDAdm ℚ D e)
    (hval : Expr.eval (thA ℚ) (thB ℚ) (rhoL ℚ) e = _root_.Rhone.Algebra.q22) : 2 ≤ D :=
  _root_.Rhone.Algebra.two_le_degree_of_formula he.toDAdm hval

noncomputable def coeffHomU : ℚ →+* _root_.Rhone.Algebra.P :=
  (Polynomial.C).comp ((algebraMap _root_.Rhone.Algebra.Fv _root_.Rhone.Algebra.Fuv).comp
    (algebraMap ℚ _root_.Rhone.Algebra.Fv))

noncomputable def genU : Fin 3 → _root_.Rhone.Algebra.P :=
  ![C (2 : _root_.Rhone.Algebra.Fuv)⁻¹ * (X + C _root_.Rhone.Algebra.vv),
    C (2 : _root_.Rhone.Algebra.Fuv)⁻¹ * (X - C _root_.Rhone.Algebra.vv),
    C _root_.Rhone.Algebra.rhoM]

noncomputable def evPU : MvPolynomial (Fin 3) ℚ →+* _root_.Rhone.Algebra.P :=
  MvPolynomial.eval₂Hom coeffHomU genU

noncomputable def evLU : MvPolynomial (Fin 3) ℚ →+* _root_.Rhone.Algebra.L :=
  (algebraMap _root_.Rhone.Algebra.P _root_.Rhone.Algebra.L).comp evPU

theorem evLU_apply (m : MvPolynomial (Fin 3) ℚ) :
    evLU m = algebraMap _root_.Rhone.Algebra.P _root_.Rhone.Algebra.L (evPU m) := rfl

theorem genU_natDegree_le (i : Fin 3) : (genU i).natDegree ≤ 1 := by
  fin_cases i
  · exact le_trans Polynomial.natDegree_mul_le (by simp)
  · exact le_trans Polynomial.natDegree_mul_le (by simp)
  · simp [genU]

theorem natDegree_evPU_le (m : MvPolynomial (Fin 3) ℚ) :
    (evPU m).natDegree ≤ m.totalDegree := by
  rw [evPU, MvPolynomial.coe_eval₂Hom]
  exact natDegree_eval₂_le _ (fun a => by simp [coeffHomU]) _ genU_natDegree_le m

theorem evLU_X_zero : evLU (MvPolynomial.X 0) = _root_.Rhone.Algebra.thAu := by
  simp [evLU, evPU, genU, _root_.Rhone.Algebra.thAu]

theorem evLU_X_one : evLU (MvPolynomial.X 1) = _root_.Rhone.Algebra.thBu := by
  simp [evLU, evPU, genU, _root_.Rhone.Algebra.thBu]

theorem evLU_X_two : evLU (MvPolynomial.X 2) = _root_.Rhone.Algebra.rhoU := by
  simp [evLU, evPU, genU, _root_.Rhone.Algebra.rhoU, RatFunc.algebraMap_C]

inductive TotalDAdmU (D : ℕ) : Expr _root_.Rhone.Algebra.Fuv → Prop
  | const (q : ℚ) : TotalDAdmU D (.const q)
  | coeff (x : _root_.Rhone.Algebra.Fuv) : TotalDAdmU D (.coeff x)
  | thA : TotalDAdmU D .thA
  | thB : TotalDAdmU D .thB
  | rho : TotalDAdmU D .rho
  | add {x y : Expr _root_.Rhone.Algebra.Fuv} : TotalDAdmU D x → TotalDAdmU D y →
      TotalDAdmU D (.add x y)
  | mul {x y : Expr _root_.Rhone.Algebra.Fuv} : TotalDAdmU D x → TotalDAdmU D y →
      TotalDAdmU D (.mul x y)
  | div {x g : Expr _root_.Rhone.Algebra.Fuv} (hx : TotalDAdmU D x) (hg : TotalDAdmU D g)
      (m : MvPolynomial (Fin 3) ℚ) (hm : m.totalDegree ≤ D) (hne : evLU m ≠ 0)
      (hval : Expr.eval _root_.Rhone.Algebra.thAu _root_.Rhone.Algebra.thBu
          _root_.Rhone.Algebra.rhoU g
        = evLU m) :
      TotalDAdmU D (.div x g)

theorem TotalDAdmU.toDAdm {D : ℕ} {e : Expr _root_.Rhone.Algebra.Fuv} (h : TotalDAdmU D e) :
    DAdm _root_.Rhone.Algebra.thAu _root_.Rhone.Algebra.thBu _root_.Rhone.Algebra.rhoU D e := by
  induction h with
  | const q => exact .const q
  | coeff x => exact .coeff x
  | thA => exact .thA
  | thB => exact .thB
  | rho => exact .rho
  | add _ _ ihx ihy => exact .add ihx ihy
  | mul _ _ ihx ihy => exact .mul ihx ihy
  | div _ _ m hm hne hval ihx ihg =>
      refine .div ihx ihg (evPU m) ?_ (le_trans (natDegree_evPU_le m) hm) hval
      intro h0
      exact hne (by rw [evLU_apply, h0, map_zero])

theorem no_degree_two_formula_total :
    ¬ ∃ e : Expr _root_.Rhone.Algebra.Fuv, TotalDAdmU 2 e
        ∧ Expr.eval _root_.Rhone.Algebra.thAu _root_.Rhone.Algebra.thBu _root_.Rhone.Algebra.rhoU e
          = _root_.Rhone.Algebra.q22u := by
  rintro ⟨e, he, hval⟩
  exact _root_.Rhone.Algebra.no_degree_two_formula ⟨e, he.toDAdm, hval⟩

theorem three_le_degree_of_formula_total {D : ℕ} {e : Expr _root_.Rhone.Algebra.Fuv}
    (he : TotalDAdmU D e)
    (hval : Expr.eval _root_.Rhone.Algebra.thAu _root_.Rhone.Algebra.thBu _root_.Rhone.Algebra.rhoU
        e
      = _root_.Rhone.Algebra.q22u) : 3 ≤ D :=
  _root_.Rhone.Algebra.three_le_degree_of_formula he.toDAdm hval

end Rhone.Algebra.GenericField
