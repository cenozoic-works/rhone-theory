/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.SamplingNumerators.Basic
public import Rhone.Probability.DiagonalChain.Small
public import Mathlib.Tactic.ComputeDegree

/-! # The finite `(3,3)` numerator has the diagonal-chain leading coefficient -/

@[expose] public section

namespace Rhone.Probability.SamplingNumerators
open Polynomial LinearAlgebra.Tridiag Analysis.RecombinationExpansion
    LinearAlgebra.RecombinationExpansion Analysis.DenominatorEquation DenominatorEquation
open DiagonalChain
variable {S : Type*} [CommRing S]
def HasTop (p : Polynomial S) (n : ℕ) (c : S) : Prop := p.natDegree ≤ n ∧ p.coeff n = c
namespace HasTop
theorem mul {p q : Polynomial S} {m n : ℕ} {a b : S}
    (hp : HasTop p m a) (hq : HasTop q n b) : HasTop (p*q) (m+n) (a*b) := by
  constructor
  · exact natDegree_mul_le.trans (Nat.add_le_add hp.1 hq.1)
  · rw [coeff_mul_add_eq_of_natDegree_le hp.1 hq.1, hp.2, hq.2]
theorem add {p q : Polynomial S} {n : ℕ} {a b : S}
    (hp : HasTop p n a) (hq : HasTop q n b) : HasTop (p+q) n (a+b) := by
  exact ⟨natDegree_add_le_of_degree_le hp.1 hq.1, by rw [coeff_add, hp.2, hq.2]⟩
theorem C (a : S) : HasTop (Polynomial.C a) 0 a := by simp [HasTop]
theorem X : HasTop (Polynomial.X : Polynomial S) 1 1 := by exact ⟨natDegree_X_le, coeff_X_one⟩
theorem raise {p : Polynomial S} {m n : ℕ} {a : S}
    (hp : HasTop p m a) (hmn : m < n) : HasTop p n 0 := by
  exact ⟨hp.1.trans hmn.le, coeff_eq_zero_of_natDegree_lt (hp.1.trans_lt hmn)⟩
theorem neg {p : Polynomial S} {n : ℕ} {a : S}
    (hp : HasTop p n a) : HasTop (-p) n (-a) := by
  simpa only [HasTop, natDegree_neg, coeff_neg] using And.intro hp.1 (congrArg Neg.neg hp.2)
theorem sub {p q : Polynomial S} {n : ℕ} {a b : S}
    (hp : HasTop p n a) (hq : HasTop q n b) : HasTop (p-q) n (a-b) := by
  simpa only [sub_eq_add_neg] using hp.add hq.neg
end HasTop

private theorem usmani_three (d b c : ℕ → S) :
    Rhone.LinearAlgebra.RecombinationExpansion.usmani d b c 3 =
      !![d 1 * d 2 - b 1 * c 1, -b 0 * d 2, b 0 * b 1;
         -c 0 * d 2, d 0 * d 2, -b 1 * d 0;
         c 0 * c 1, -c 1 * d 0, d 0 * d 1 - b 0 * c 0] := by
  have q2 : Rhone.LinearAlgebra.RecombinationExpansion.Qc d b c 3 2 = d 2 := by
    rw [Rhone.LinearAlgebra.RecombinationExpansion.Qc_rec d b c (by omega : 2 < 3)]
    norm_num
  have q1 : Rhone.LinearAlgebra.RecombinationExpansion.Qc d b c 3 1 = d 1 * d 2 - b 1 * c 1 := by
    rw [Rhone.LinearAlgebra.RecombinationExpansion.Qc_rec d b c (by omega : 1 < 3), q2]
    norm_num
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Rhone.LinearAlgebra.RecombinationExpansion.usmani_apply,
        Rhone.LinearAlgebra.RecombinationExpansion.usmaniEntry,
      Rhone.LinearAlgebra.RecombinationExpansion.runProd, Rhone.LinearAlgebra.Tridiag.cont, q1, q2,
      Finset.prod_Ico_succ_top, Finset.prod_range_succ]
  ring

private theorem U_diag_lambda (θ ρ : S) (k : ℕ) (i j : Fin (min k k + 1)) :
    U (Polynomial S) k k X (C θ - X) (C ρ) i j = C (adjD k θ ρ i j) := by
  rw [U_apply, adjD, usmaniEntry_map]
  congr 1
  · funext t
    simp only [dcoef, map_add, map_mul, map_natCast, zero_mul,
      add_zero]
    ring
  · funext t
    simp [bcoef, map_ofNat]
  · funext t
    simp [ccoef]

private theorem E_diag_lambda (θ ρ : S) (k : ℕ) :
    E (Polynomial S) k k X (C θ - X) (C ρ) = C (ED k θ ρ) := by
  rw [E_eq_cont, ED, E_eq_cont, Analysis.Rescale.cont_map]
  congr 1
  · funext t
    simp only [dcoef, map_add, map_mul, map_natCast, zero_mul,
      add_zero]
    ring
  · funext t
    simp [bcoef, map_ofNat]
  · funext t
    simp [ccoef]

private theorem s22_top (θ : S) (i : Fin 3) :
    HasTop (s22 (X : Polynomial S) (C θ - X) i) 2 (if i = 2 then -2 else 0) := by
  have hp : HasTop (X + 1 : Polynomial S) 1 1 := by
    simpa using HasTop.X.add ((HasTop.C (1 : S)).raise (by omega : 0 < 1))
  have hq : HasTop (C θ - X + 1 : Polynomial S) 1 (-1) := by
    simpa using (((HasTop.C θ).raise (by omega : 0 < 1)).sub HasTop.X).add
      ((HasTop.C (1 : S)).raise (by omega : 0 < 1))
  have hconst : 2 * ((X + 1) + (C θ - X + 1)) = C (2 * (θ + 2)) := by
    simp only [map_mul, map_add, map_ofNat]
    ring
  fin_cases i
  · simpa [s22, hconst] using (HasTop.C (2 * (θ + 2))).raise (by omega : 0 < 2)
  · simpa [s22, hconst] using (HasTop.C (2 * (θ + 2))).raise (by omega : 0 < 2)
  · simpa [s22, c22, mul_assoc, map_ofNat] using (HasTop.C (2 : S)).mul (hp.mul hq)

private theorem n22_top (θ ρ : S) (i : Fin 3) :
    HasTop (n22 (X : Polynomial S) (C θ - X) (C ρ) i) 2 (-2 * adjD 2 θ ρ i 2) := by
  have h (j : Fin 3) := (HasTop.C (adjD 2 θ ρ i j)).mul (s22_top θ j)
  simp only [n22, Matrix.mulVec, dotProduct, U_diag_lambda]
  change HasTop (∑ j : Fin 3, C (adjD 2 θ ρ i j) * s22 X (C θ - X) j)
    2 (-2 * adjD 2 θ ρ i 2)
  rw [Fin.sum_univ_three]
  simpa [add_assoc, mul_comm] using ((h 0).add (h 1)).add (h 2)

private theorem U23_degree (θ ρ : S) (i j : Fin 3) :
    (U (Polynomial S) 2 3 X (C θ - X) (C ρ) i j).natDegree ≤ 2 := by
  change ((usmani (dcoef (Polynomial S) 2 3 X (C θ - X) (C ρ))
    (bcoef (Polynomial S) 2 3) (ccoef (Polynomial S) (C ρ)) 3) i j).natDegree ≤ 2
  rw [usmani_three]
  fin_cases i <;> fin_cases j <;> norm_num [dcoef, bcoef, ccoef] <;> compute_degree!

private theorem U32_degree (θ ρ : S) (i j : Fin 3) :
    (U (Polynomial S) 3 2 X (C θ - X) (C ρ) i j).natDegree ≤ 2 := by
  change ((usmani (dcoef (Polynomial S) 3 2 X (C θ - X) (C ρ))
    (bcoef (Polynomial S) 3 2) (ccoef (Polynomial S) (C ρ)) 3) i j).natDegree ≤ 2
  rw [usmani_three]
  fin_cases i <;> fin_cases j <;> norm_num [dcoef, bcoef, ccoef] <;> compute_degree!

private theorem E23_top (θ ρ : S) :
    HasTop (E (Polynomial S) 2 3 X (C θ - X) (C ρ)) 3 (-1) := by
  rw [E_eq_cont]
  norm_num [LinearAlgebra.Tridiag.cont, dcoef, bcoef, ccoef]
  constructor <;> compute_degree!

private theorem E32_top (θ ρ : S) :
    HasTop (E (Polynomial S) 3 2 X (C θ - X) (C ρ)) 3 1 := by
  rw [E_eq_cont]
  norm_num [LinearAlgebra.Tridiag.cont, dcoef, bcoef, ccoef]
  constructor <;> compute_degree!

private theorem s23_degree (θ ρ : S) (i : Fin 3) :
    (s23 (X : Polynomial S) (C θ - X) (C ρ) i).natDegree ≤ 3 := by
  have h0 (t : Fin 3) :
      (4 * (X + 1) * C (ED 2 θ ρ) + 6 * (C θ - X + 2) *
        n22 X (C θ - X) (C ρ) t).natDegree ≤ 3 :=
    natDegree_add_le_of_degree_le (by compute_degree!)
      (natDegree_mul_le_of_le (by compute_degree! :
        (6 * (C θ - X + 2)).natDegree ≤ 1) (n22_top θ ρ t).1)
  have h2 :
      (2 * (X + 1) * (C θ - X + 2) * C (ED 2 θ ρ) + 4 * (C θ - X + 2) *
        n22 X (C θ - X) (C ρ) 2).natDegree ≤ 3 :=
    natDegree_add_le_of_degree_le (by compute_degree!)
      (natDegree_mul_le_of_le (by compute_degree! :
        (4 * (C θ - X + 2)).natDegree ≤ 1) (n22_top θ ρ 2).1)
  fin_cases i
  · simpa [s23, E_diag_lambda] using h0 0
  · simpa [s23, E_diag_lambda] using h0 1
  · simpa [s23, E_diag_lambda] using h2

private theorem s32_degree (θ ρ : S) (i : Fin 3) :
    (s32 (X : Polynomial S) (C θ - X) (C ρ) i).natDegree ≤ 3 := by
  have h0 (t : Fin 3) :
      (4 * (C θ - X + 1) * C (ED 2 θ ρ) + 6 * (X + 2) *
        n22 X (C θ - X) (C ρ) t).natDegree ≤ 3 :=
    natDegree_add_le_of_degree_le (by compute_degree!)
      (natDegree_mul_le_of_le (by compute_degree! :
        (6 * (X + 2) : Polynomial S).natDegree ≤ 1) (n22_top θ ρ t).1)
  have h2 :
      (2 * (X + 2) * (C θ - X + 1) * C (ED 2 θ ρ) + 4 * (X + 2) *
        n22 X (C θ - X) (C ρ) 2).natDegree ≤ 3 :=
    natDegree_add_le_of_degree_le (by compute_degree!)
      (natDegree_mul_le_of_le (by compute_degree! :
        (4 * (X + 2) : Polynomial S).natDegree ≤ 1) (n22_top θ ρ 2).1)
  fin_cases i
  · simpa [s32, E_diag_lambda] using h0 0
  · simpa [s32, E_diag_lambda] using h0 1
  · simpa [s32, E_diag_lambda] using h2

private theorem n23_degree (θ ρ : S) (i : Fin 3) :
    (n23 (X : Polynomial S) (C θ - X) (C ρ) i).natDegree ≤ 5 := by
  rw [n23, Matrix.mulVec, dotProduct]
  exact natDegree_sum_le_of_forall_le _ _ fun j _ =>
    natDegree_mul_le_of_le (U23_degree θ ρ i j) (s23_degree θ ρ j)

private theorem n32_degree (θ ρ : S) (i : Fin 3) :
    (n32 (X : Polynomial S) (C θ - X) (C ρ) i).natDegree ≤ 5 := by
  rw [n32, Matrix.mulVec, dotProduct]
  exact natDegree_sum_le_of_forall_le _ _ fun j _ =>
    natDegree_mul_le_of_le (U32_degree θ ρ i j) (s32_degree θ ρ j)

private theorem upper_edge_top (c : S) : HasTop (X + C c : Polynomial S) 1 1 := by
  simpa using HasTop.X.add ((HasTop.C c).raise (by omega : 0 < 1))

private theorem lower_edge_top (θ c : S) : HasTop (C θ - X + C c) 1 (-1) := by
  simpa using (((HasTop.C θ).raise (by omega : 0 < 1)).sub HasTop.X).add
    ((HasTop.C c).raise (by omega : 0 < 1))

private theorem middle_top (θ ρ : S) :
    HasTop ((X + 2) * (C θ - X + 2) * E (Polynomial S) 2 3 X (C θ - X) (C ρ) *
      E (Polynomial S) 3 2 X (C θ - X) (C ρ)) 8 1 := by
  simpa [map_ofNat] using (((upper_edge_top (2 : S)).mul (lower_edge_top θ (2 : S))).mul
    (E23_top θ ρ)).mul (E32_top θ ρ)

private theorem offdiag_degree (θ ρ : S) (i : Fin 3) :
    ((X + 2) * E (Polynomial S) 3 2 X (C θ - X) (C ρ) * n23 X (C θ - X) (C ρ) i
      + (C θ - X + 2) * E (Polynomial S) 2 3 X (C θ - X) (C ρ) *
        n32 X (C θ - X) (C ρ) i).natDegree ≤ 9 := by
  apply natDegree_add_le_of_degree_le
  · exact natDegree_mul_le_of_le
      (natDegree_mul_le_of_le (by compute_degree! : (X + 2 : Polynomial S).natDegree ≤ 1)
        (E32_top θ ρ).1) (n23_degree θ ρ i)
  · exact natDegree_mul_le_of_le
      (natDegree_mul_le_of_le (by compute_degree! : (C θ - X + 2).natDegree ≤ 1)
        (E23_top θ ρ).1) (n32_degree θ ρ i)

private theorem s33_top (θ ρ : S) (i : Fin 4) :
    HasTop (s33 (X : Polynomial S) (C θ - X) (C ρ) i) 10
      (![0, 0, -4 * adjD 2 θ ρ 1 2, -12 * adjD 2 θ ρ 2 2] i) := by
  let off (t : Fin 3) :=
    (X + 2) * E (Polynomial S) 3 2 X (C θ - X) (C ρ) * n23 X (C θ - X) (C ρ) t
      + (C θ - X + 2) * E (Polynomial S) 2 3 X (C θ - X) (C ρ) *
        n32 X (C θ - X) (C ρ) t
  let mid := (X + 2) * (C θ - X + 2) * E (Polynomial S) 2 3 X (C θ - X) (C ρ) *
      E (Polynomial S) 3 2 X (C θ - X) (C ρ)
  have ho (c : S) (t : Fin 3) : HasTop (C c * off t) 10 0 := by
    have hd : (C c * off t).natDegree ≤ 9 :=
      natDegree_mul_le_of_le (by simp) (offdiag_degree θ ρ t)
    exact ⟨hd.trans (by omega), coeff_eq_zero_of_natDegree_lt (hd.trans_lt (by omega))⟩
  have hn (c : S) (t : Fin 3) :
      HasTop (C c * (mid * n22 X (C θ - X) (C ρ) t)) 10 (-2 * c * adjD 2 θ ρ t 2) := by
    convert (HasTop.C c).mul ((middle_top θ ρ).mul (n22_top θ ρ t)) using 1
    ring
  fin_cases i
  · simpa [s33, off, map_ofNat] using ho 6 0
  · simpa [s33, off, map_ofNat] using ho 6 1
  · convert (ho 4 2).add (hn 2 1) using 1 <;> simp [s33, off, mid, map_ofNat] <;> ring
  · convert hn 6 2 using 1 <;> simp [s33, mid, map_ofNat] <;> ring

theorem n33_lambda_natDegree_le (θ ρ : S) (i : Fin 4) :
    (n33 (X : Polynomial S) (C θ - X) (C ρ) i).natDegree ≤ 10 := by
  simp only [n33, Matrix.mulVec, dotProduct, U_diag_lambda]
  exact natDegree_sum_le_of_forall_le _ _ fun j _ =>
    natDegree_mul_le_of_le (by simp) (s33_top θ ρ j).1

theorem n33_lambda_coeff_ten (θ ρ : S) :
    (n33 (X : Polynomial S) (C θ - X) (C ρ) 0).coeff 10 = -W 3 θ ρ := by
  have h (j : Fin 4) := (HasTop.C (adjD 3 θ ρ 0 j)).mul (s33_top θ ρ j)
  have hs := (((h 0).add (h 1)).add (h 2)).add (h 3)
  have he := hs.2
  simp only [n33, Matrix.mulVec, dotProduct, U_diag_lambda]
  change (∑ j : Fin 4, C (adjD 3 θ ρ 0 j) * s33 X (C θ - X) (C ρ) j).coeff 10 = _
  rw [Fin.sum_univ_four]
  rw [he]
  change adjD 3 θ ρ 0 0 * 0 + adjD 3 θ ρ 0 1 * 0 +
    adjD 3 θ ρ 0 2 * (-4 * adjD 2 θ ρ 1 2) +
    adjD 3 θ ρ 0 3 * (-12 * adjD 2 θ ρ 2 2) = -W 3 θ ρ
  norm_num
  rw [adjD_three_zero_two, adjD_three_zero_three, adjD_two_one_two,
    adjD_two_two_two, W_three]
  ring

theorem n33_lambda_coeff_ten_explicit (θ ρ : S) :
    (n33 (X : Polynomial S) (C θ - X) (C ρ) 0).coeff 10 =
      -6912 * (2 * (θ + 4) * ρ + (3 * θ + 8) * (θ + 6)) := by
  rw [n33_lambda_coeff_ten, W_three]
  ring

theorem d33_lambda_top (θ ρ : S) :
    (d33 (X : Polynomial S) (C θ - X) (C ρ)).natDegree ≤ 10 ∧
      (d33 (X : Polynomial S) (C θ - X) (C ρ)).coeff 10 = -ED 2 θ ρ * ED 3 θ ρ := by
  have h := (((((((upper_edge_top (1 : S)).mul (upper_edge_top (2 : S))).mul
    (lower_edge_top θ (1 : S))).mul (lower_edge_top θ (2 : S))).mul
    (HasTop.C (ED 2 θ ρ))).mul (E23_top θ ρ)).mul (E32_top θ ρ)).mul
    (HasTop.C (ED 3 θ ρ))
  simpa [HasTop, d33, c33, E_diag_lambda, map_ofNat] using h

end Rhone.Probability.SamplingNumerators
