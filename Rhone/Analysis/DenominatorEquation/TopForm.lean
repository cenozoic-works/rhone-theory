/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Analysis.DenominatorEquation.Basic
public import Rhone.LinearAlgebra.DenominatorEquation.Stirling
public import Rhone.LinearAlgebra.Tridiag.RhoDegree

/-! # Top `(θ, ρ)`-form of `E_{i,j}` and its Stirling-coefficient scaling -/

@[expose] public section

namespace Rhone.Analysis.DenominatorEquation

open Matrix Polynomial LinearAlgebra.Tridiag RecombinationExpansion
    LinearAlgebra.RecombinationExpansion

variable {A : Type*} [CommRing A]

theorem TS_map {B : Type*} [CommRing B] (f : A →+* B) (i j : ℕ) (s ρ : A) :
    (TS A i j s ρ).map f = TS B i j (f s) (f ρ) := by
  ext p q
  simp only [Matrix.map_apply, TS, trid_apply, tridEntry, dcoefS, bcoef, ccoef, apply_ite f]
  split_ifs <;> push_cast <;> simp [map_ofNat]

theorem ES_map {B : Type*} [CommRing B] (f : A →+* B) (i j : ℕ) (s ρ : A) :
    f (ES A i j s ρ) = ES B i j (f s) (f ρ) := by
  rw [ES, ES, ← TS_map f, RingHom.map_det]
  rfl

section Scaled

variable (i j : ℕ) (s ρ : A)

theorem dcoefS_scaled (t : ℕ) :
    dcoefS (Polynomial A) i j (C s * X) (C ρ * X) t
      = C ((((i + j - t) * (i + j - t - 1) : ℕ)) : A) + C (s + ρ * (t : A)) * X := by
  rw [dcoefS]
  simp only [map_add, map_mul, map_natCast]
  ring

theorem bc_scaled (t : ℕ) :
    bcoef (Polynomial A) i j t * ccoef (Polynomial A) (C ρ * X) t
      = C (2 * ρ * ((t : A) + 1) * ((((i - t) * (j - t) : ℕ)) : A)) * X := by
  rw [bcoef_mul_ccoef]
  simp only [map_add, map_mul, map_natCast, map_one, map_ofNat]
  ring

private theorem scaled_aux :
    (ES (Polynomial A) i j (C s * X) (C ρ * X)).natDegree ≤ min i j + 1 ∧
      (ES (Polynomial A) i j (C s * X) (C ρ * X)).coeff (min i j + 1)
        = ∏ t ∈ Finset.range (min i j + 1), (s + ρ * (t : A)) := by
  have h := degree_and_coeff_of_tridFrom (dcoefS (Polynomial A) i j (C s * X) (C ρ * X))
    (bcoef (Polynomial A) i j) (ccoef (Polynomial A) (C ρ * X))
    (fun t => (((i + j - t) * (i + j - t - 1) : ℕ) : A)) (fun t => s + ρ * (t : A))
    (fun t => 2 * ρ * ((t : A) + 1) * ((((i - t) * (j - t) : ℕ)) : A))
    (dcoefS_scaled i j s ρ) (bc_scaled i j ρ) (min i j + 1) 0
  rw [tridFrom_zero] at h
  rw [ES, TS]
  refine ⟨h.1, ?_⟩
  rw [h.2]
  exact Finset.prod_congr rfl fun t _ => by rw [Nat.zero_add]

theorem ES_scaled_natDegree_le :
    (ES (Polynomial A) i j (C s * X) (C ρ * X)).natDegree ≤ min i j + 1 :=
  (scaled_aux i j s ρ).1

theorem ES_scaled_coeff_top :
    (ES (Polynomial A) i j (C s * X) (C ρ * X)).coeff (min i j + 1)
      = ∏ t ∈ Finset.range (min i j + 1), (s + ρ * (t : A)) :=
  (scaled_aux i j s ρ).2

end Scaled

section ScaledE

variable (i j : ℕ) (θA θB ρ : A)

private theorem s_scaled_eq :
    (C θA * X : Polynomial A) * ((i : ℕ) : Polynomial A)
        + (C θB * X : Polynomial A) * ((j : ℕ) : Polynomial A)
      = C (θA * (i : A) + θB * (j : A)) * X := by
  simp only [map_add, map_mul, map_natCast]
  ring

theorem E_scaled_natDegree_le :
    (E (Polynomial A) i j (C θA * X) (C θB * X) (C ρ * X)).natDegree ≤ min i j + 1 := by
  rw [← ES_eq_E, s_scaled_eq]
  exact ES_scaled_natDegree_le i j _ ρ

theorem E_scaled_coeff_top :
    (E (Polynomial A) i j (C θA * X) (C θB * X) (C ρ * X)).coeff (min i j + 1)
      = ∏ t ∈ Finset.range (min i j + 1), (θA * (i : A) + θB * (j : A) + ρ * (t : A)) := by
  rw [← ES_eq_E, s_scaled_eq]
  exact ES_scaled_coeff_top i j _ ρ

end ScaledE

section Bigraded

noncomputable def Ebi (A : Type*) [CommRing A] (i j : ℕ) : Polynomial (Polynomial A) :=
  ES (Polynomial (Polynomial A)) i j (C X) X

noncomputable def Pbi (A : Type*) [CommRing A] (i j r : ℕ) : Polynomial (Polynomial A) :=
  cont (dcoefS (Polynomial (Polynomial A)) i j (C X) X) (bcoef (Polynomial (Polynomial A)) i j)
    (ccoef (Polynomial (Polynomial A)) X) r

theorem Ebi_eq_Pbi (i j : ℕ) : Ebi A i j = Pbi A i j (min i j + 1) := ES_eq_cont i j (C X) X

theorem Ebi_eval (i j : ℕ) (θA θB ρ : A) :
    Polynomial.eval ρ ((Ebi A i j).map (Polynomial.evalRingHom (θA * (i : A) + θB * (j : A))))
      = E A i j θA θB ρ := by
  have h := ES_map ((Polynomial.evalRingHom ρ).comp
    (Polynomial.mapRingHom (Polynomial.evalRingHom (θA * (i : A) + θB * (j : A)))))
    i j (C X : Polynomial (Polynomial A)) X
  simp only [RingHom.coe_comp, Function.comp_apply, coe_mapRingHom, coe_evalRingHom,
    Polynomial.map_C, eval_C, eval_X, Polynomial.map_X] at h
  rw [Ebi, h, ES_eq_E]

theorem dcoefS_bi (i j t : ℕ) :
    dcoefS (Polynomial (Polynomial A)) i j (C X) X t
      = C (C ((((i + j - t) * (i + j - t - 1) : ℕ)) : A) + X) + C (C ((t : ℕ) : A)) * X := by
  rw [dcoefS]
  simp only [map_add, map_natCast]
  ring

theorem bc_bi (i j t : ℕ) :
    bcoef (Polynomial (Polynomial A)) i j t * ccoef (Polynomial (Polynomial A)) X t
      = C (C ((2 * ((t : ℕ) + 1) * ((i - t) * (j - t)) : ℕ) : A)) * X := by
  rw [bcoef_mul_ccoef]
  simp only [map_natCast]
  push_cast
  ring

variable (α β g : A) (q p : Polynomial (Polynomial A))

private theorem coeff_shift_zero (w : Polynomial A) :
    ((C α + X) * w).coeff 0 = α * w.coeff 0 := by
  rw [mul_coeff_zero, coeff_add, coeff_C_zero, coeff_X_zero, add_zero]

private theorem coeff_shift_succ (w : Polynomial A) (e : ℕ) :
    ((C α + X) * w).coeff (e + 1) = α * w.coeff (e + 1) + w.coeff e := by
  rw [add_mul, coeff_add, coeff_C_mul, coeff_X_mul]

private theorem step_expand_zero :
    ((C (C α + X) + C (C β) * X) * q - C (C g) * X * p).coeff 0 = (C α + X) * q.coeff 0 := by
  rw [coeff_sub, add_mul, coeff_add, coeff_C_mul, mul_assoc, coeff_C_mul, mul_assoc, coeff_C_mul,
    mul_coeff_zero, mul_coeff_zero, coeff_X_zero, zero_mul, zero_mul, mul_zero, mul_zero,
    add_zero, sub_zero]

private theorem step_expand_succ (k : ℕ) :
    ((C (C α + X) + C (C β) * X) * q - C (C g) * X * p).coeff (k + 1)
      = (C α + X) * q.coeff (k + 1) + C β * q.coeff k - C g * p.coeff k := by
  rw [coeff_sub, add_mul, coeff_add, coeff_C_mul, mul_assoc, coeff_C_mul, mul_assoc, coeff_C_mul,
    coeff_X_mul, coeff_X_mul]

theorem step_coeff_zero_zero :
    (((C (C α + X) + C (C β) * X) * q - C (C g) * X * p).coeff 0).coeff 0
      = α * ((q.coeff 0).coeff 0) := by
  rw [step_expand_zero, coeff_shift_zero]

theorem step_coeff_zero_succ (e : ℕ) :
    (((C (C α + X) + C (C β) * X) * q - C (C g) * X * p).coeff 0).coeff (e + 1)
      = α * ((q.coeff 0).coeff (e + 1)) + (q.coeff 0).coeff e := by
  rw [step_expand_zero, coeff_shift_succ]

theorem step_coeff_succ_zero (k : ℕ) :
    (((C (C α + X) + C (C β) * X) * q - C (C g) * X * p).coeff (k + 1)).coeff 0
      = α * ((q.coeff (k + 1)).coeff 0) + β * ((q.coeff k).coeff 0)
        - g * ((p.coeff k).coeff 0) := by
  rw [step_expand_succ, coeff_sub, coeff_add, coeff_C_mul, coeff_C_mul, coeff_shift_zero]

theorem step_coeff_succ_succ (k e : ℕ) :
    (((C (C α + X) + C (C β) * X) * q - C (C g) * X * p).coeff (k + 1)).coeff (e + 1)
      = α * ((q.coeff (k + 1)).coeff (e + 1)) + (q.coeff (k + 1)).coeff e
        + β * ((q.coeff k).coeff (e + 1)) - g * ((p.coeff k).coeff (e + 1)) := by
  rw [step_expand_succ, coeff_sub, coeff_add, coeff_C_mul, coeff_C_mul, coeff_shift_succ]

end Bigraded

section Induction

variable (A)

theorem Pbi_zero (i j : ℕ) : Pbi A i j 0 = 1 := rfl

theorem Pbi_one (i j : ℕ) :
    Pbi A i j 1 = dcoefS (Polynomial (Polynomial A)) i j (C X) X 0 := rfl

theorem Pbi_step (i j r : ℕ) :
    Pbi A i j (r + 2)
      = dcoefS (Polynomial (Polynomial A)) i j (C X) X (r + 1) * Pbi A i j (r + 1)
        - bcoef (Polynomial (Polynomial A)) i j r * ccoef (Polynomial (Polynomial A)) X r
            * Pbi A i j r := rfl

theorem Pbi_coeff (i j : ℕ) : ∀ r : ℕ,
    (∀ k e : ℕ, r < k + e → ((Pbi A i j r).coeff k).coeff e = 0) ∧
      (∀ k : ℕ, k ≤ r → ((Pbi A i j r).coeff k).coeff (r - k) =
          (LinearAlgebra.DenominatorEquation.stirling1 r (r - k) : A)) := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    match r with
    | 0 =>
      rw [Pbi_zero]
      refine ⟨fun k e hke => ?_, fun k hk => ?_⟩
      · rcases Nat.eq_zero_or_pos k with rfl | hk
        · rw [coeff_one, ite_eq_left rfl, coeff_one, ite_eq_right (by omega)]
        · rw [coeff_one, ite_eq_right (by omega), coeff_zero]
      · obtain rfl : k = 0 := by omega
        rw [coeff_one, ite_eq_left rfl, coeff_one, ite_eq_left rfl]
        simp
    | 1 =>
      have h1 : Pbi A i j 1 = C (C ((((i + j) * (i + j - 1) : ℕ)) : A) + X) := by
        rw [Pbi_one, dcoefS_bi]
        simp
      rw [h1]
      refine ⟨fun k e hke => ?_, fun k hk => ?_⟩
      · rcases Nat.eq_zero_or_pos k with rfl | hk
        · rw [coeff_C, ite_eq_left rfl, coeff_add, coeff_C, coeff_X, ite_eq_right (by omega),
            ite_eq_right (by omega)]
          ring
        · rw [coeff_C, ite_eq_right (by omega), coeff_zero]
      · rcases k with _ | k
        · rw [coeff_C, ite_eq_left rfl]
          simp
        · obtain rfl : k = 0 := by omega
          rw [coeff_C, ite_eq_right (by omega), coeff_zero]
          simp
    | (r + 2) =>
      obtain ⟨ih1a, ih1b⟩ := ih (r + 1) (by omega)
      obtain ⟨ih0a, -⟩ := ih r (by omega)
      rw [Pbi_step, dcoefS_bi, bc_bi]
      refine ⟨fun k e hke => ?_, fun k hk => ?_⟩
      · rcases k with _ | k
        · rcases e with _ | e
          · omega
          · rw [step_coeff_zero_succ, ih1a 0 (e + 1) (by omega), ih1a 0 e (by omega)]
            ring
        · rcases e with _ | e
          · rw [step_coeff_succ_zero, ih1a (k + 1) 0 (by omega), ih1a k 0 (by omega),
              ih0a k 0 (by omega)]
            ring
          · rw [step_coeff_succ_succ, ih1a (k + 1) (e + 1) (by omega), ih1a (k + 1) e (by omega),
              ih1a k (e + 1) (by omega), ih0a k (e + 1) (by omega)]
            ring
      · rcases k with _ | k
        · have hb0 := ih1b 0 (by omega)
          rw [Nat.sub_zero] at hb0
          have hrhs : LinearAlgebra.DenominatorEquation.stirling1 (r + 2) (r + 2 - 0) = 1 := by
            rw [Nat.sub_zero]
            exact LinearAlgebra.DenominatorEquation.stirling1_self (r + 2)
          rw [hrhs, show r + 2 - 0 = r + 1 + 1 from by omega, step_coeff_zero_succ,
            ih1a 0 (r + 1 + 1) (by omega), hb0, LinearAlgebra.DenominatorEquation.stirling1_self]
          simp
        · rcases Nat.lt_or_ge r k with hkr | hkr
          · have hk' : k = r + 1 := by omega
            subst hk'
            have hb := ih1b (r + 1) (by omega)
            rw [show r + 1 - (r + 1) = 0 from
                by omega, LinearAlgebra.DenominatorEquation.stirling1_succ_zero] at hb
            rw [show r + 2 - (r + 1 + 1) = 0 from by omega, step_coeff_succ_zero,
              ih1a (r + 1 + 1) 0 (by omega), hb, ih0a (r + 1) 0 (by omega),
              LinearAlgebra.DenominatorEquation.stirling1_succ_zero]
            simp
          · have hb1 := ih1b (k + 1) (by omega)
            rw [show r + 1 - (k + 1) = r - k from by omega] at hb1
            have hb2 := ih1b k (by omega)
            rw [show r + 1 - k = (r - k) + 1 from by omega] at hb2
            have hrec : LinearAlgebra.DenominatorEquation.stirling1 (r + 2) ((r - k) + 1)
                = LinearAlgebra.DenominatorEquation.stirling1 (r + 1) (r - k) + (r + 1) *
                    LinearAlgebra.DenominatorEquation.stirling1 (r + 1) ((r - k) + 1) :=
              LinearAlgebra.DenominatorEquation.stirling1_succ_succ (r + 1) (r - k)
            rw [show r + 2 - (k + 1) = (r - k) + 1 from by omega, step_coeff_succ_succ,
              ih1a (k + 1) ((r - k) + 1) (by omega), hb1, hb2,
              ih0a k ((r - k) + 1) (by omega), hrec]
            push_cast
            ring

end Induction

section Corollaries

variable (A) (i j : ℕ)

theorem Ebi_coeff_coeff_of_lt (k e : ℕ) (h : min i j + 1 < k + e) :
    ((Ebi A i j).coeff k).coeff e = 0 := by
  rw [Ebi_eq_Pbi]
  exact (Pbi_coeff A i j (min i j + 1)).1 k e h

theorem Ebi_coeff_coeff_top (k : ℕ) (hk : k ≤ min i j + 1) :
    ((Ebi A i j).coeff k).coeff (min i j + 1 - k)
      = (LinearAlgebra.DenominatorEquation.stirling1 (min i j + 1) (min i j + 1 - k) : A) := by
  rw [Ebi_eq_Pbi]
  exact (Pbi_coeff A i j (min i j + 1)).2 k hk

theorem Ebi_coeff_natDegree_le (k : ℕ) :
    ((Ebi A i j).coeff k).natDegree ≤ min i j + 1 - k := by
  refine natDegree_le_iff_coeff_eq_zero.mpr fun e he => ?_
  exact Ebi_coeff_coeff_of_lt A i j k e (by omega)

theorem Ebi_coeff_natDegree [Nontrivial A] [CharZero A] (k : ℕ) (hk : k ≤ min i j) :
    ((Ebi A i j).coeff k).natDegree = min i j + 1 - k ∧
      ((Ebi A i j).coeff k).leadingCoeff =
          (LinearAlgebra.DenominatorEquation.stirling1 (min i j + 1) (min i j + 1 - k) : A) := by
  have hpos : 0 < LinearAlgebra.DenominatorEquation.stirling1 (min i j + 1) (min i j + 1 - k) :=
    LinearAlgebra.DenominatorEquation.stirling1_pos (by omega) (by omega)
  have hne : ((Ebi A i j).coeff k).coeff (min i j + 1 - k) ≠ 0 := by
    rw [Ebi_coeff_coeff_top A i j k (by omega)]
    exact Nat.cast_ne_zero.mpr (by omega)
  have hdeg : ((Ebi A i j).coeff k).natDegree = min i j + 1 - k :=
    le_antisymm (Ebi_coeff_natDegree_le A i j k) (le_natDegree_of_ne_zero hne)
  refine ⟨hdeg, ?_⟩
  rw [leadingCoeff, hdeg, Ebi_coeff_coeff_top A i j k (by omega)]

end Corollaries

section SubBlocks

variable (i j : ℕ) (θA θB ρ : A)

theorem dcoef_scaled (t : ℕ) :
    dcoef (Polynomial A) i j (C θA * X) (C θB * X) (C ρ * X) t
      = C ((((i + j - t) * (i + j - t - 1) : ℕ)) : A)
        + C (θA * (i : A) + θB * (j : A) + ρ * (t : A)) * X := by
  rw [← dcoefS_eq_dcoef, s_scaled_eq, dcoefS_scaled]

private theorem sub_aux (r k : ℕ) :
    (tridFrom (dcoef (Polynomial A) i j (C θA * X) (C θB * X) (C ρ * X))
        (bcoef (Polynomial A) i j) (ccoef (Polynomial A) (C ρ * X)) k r).det.natDegree ≤ r ∧
      (tridFrom (dcoef (Polynomial A) i j (C θA * X) (C θB * X) (C ρ * X))
        (bcoef (Polynomial A) i j) (ccoef (Polynomial A) (C ρ * X)) k r).det.coeff r
        = ∏ u ∈ Finset.range r, (θA * (i : A) + θB * (j : A) + ρ * ((k + u : ℕ) : A)) :=
  degree_and_coeff_of_tridFrom _ _ _
    (fun t => (((i + j - t) * (i + j - t - 1) : ℕ) : A))
    (fun t => θA * (i : A) + θB * (j : A) + ρ * (t : A))
    (fun t => 2 * ρ * ((t : A) + 1) * ((((i - t) * (j - t) : ℕ)) : A))
    (dcoef_scaled i j θA θB ρ) (bc_scaled i j ρ) r k

theorem Delta_scaled_natDegree_le (r : ℕ) :
    (Delta (Polynomial A) i j (C θA * X) (C θB * X) (C ρ * X) r).natDegree ≤ r := by
  rw [Delta, ← det_trid_eq_cont, ← tridFrom_zero]
  exact (sub_aux i j θA θB ρ r 0).1

theorem Delta_scaled_coeff_top (r : ℕ) :
    (Delta (Polynomial A) i j (C θA * X) (C θB * X) (C ρ * X) r).coeff r
      = ∏ u ∈ Finset.range r, (θA * (i : A) + θB * (j : A) + ρ * (u : A)) := by
  rw [Delta, ← det_trid_eq_cont, ← tridFrom_zero, (sub_aux i j θA θB ρ r 0).2]
  exact Finset.prod_congr rfl fun u _ => by rw [Nat.zero_add]

theorem DeltaP_scaled_natDegree_le {k : ℕ} (hk : k ≤ min i j + 1) :
    (DeltaP (Polynomial A) i j (C θA * X) (C θB * X) (C ρ * X) k).natDegree
      ≤ min i j + 1 - k := by
  rw [DeltaP, Qc_of_le _ _ _ hk]
  exact (sub_aux i j θA θB ρ (min i j + 1 - k) k).1

theorem DeltaP_scaled_coeff_top {k : ℕ} (hk : k ≤ min i j + 1) :
    (DeltaP (Polynomial A) i j (C θA * X) (C θB * X) (C ρ * X) k).coeff (min i j + 1 - k)
      = ∏ u ∈ Finset.range (min i j + 1 - k),
          (θA * (i : A) + θB * (j : A) + ρ * ((k + u : ℕ) : A)) := by
  rw [DeltaP, Qc_of_le _ _ _ hk]
  exact (sub_aux i j θA θB ρ (min i j + 1 - k) k).2

end SubBlocks

end Rhone.Analysis.DenominatorEquation
