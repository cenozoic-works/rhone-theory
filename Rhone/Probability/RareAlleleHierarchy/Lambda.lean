/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.RareAlleleHierarchy.Reduced
public import Rhone.Analysis.RareAlleleHierarchy.Inert

/-! # The diagonal chain `T^{(k,k)} ϑ^k = v^k` -/

@[expose] public section

namespace Rhone.Probability.RareAlleleHierarchy

open LinearAlgebra.Tridiag Analysis.DenominatorEquation

section Chain

variable {K : Type*} [CommRing K]

def varthetaOne : ℕ → K := fun t => if t = 1 then 1 else 0

@[simp] theorem varthetaOne_zero : (varthetaOne 0 : K) = 0 := by simp [varthetaOne]
@[simp] theorem varthetaOne_one : (varthetaOne 1 : K) = 1 := by simp [varthetaOne]

def diagSource (w : ℕ → K) (t : ℕ) : K := ((t * (t - 1) : ℕ) : K) * w (t - 1)

@[simp] theorem diagSource_zero (w : ℕ → K) : diagSource w 0 = 0 := by simp [diagSource]
@[simp] theorem diagSource_one (w : ℕ → K) : diagSource w 1 = 0 := by simp [diagSource]

theorem diagSource_two (w : ℕ → K) : diagSource w 2 = 2 * w 1 := by
  simp [diagSource]

def IsDiagChain (θ ρ : K) (ϑ : ℕ → ℕ → K) : Prop :=
  (∀ t : ℕ, ϑ 1 t = varthetaOne t) ∧
    ∀ k : ℕ, 2 ≤ k → ∀ t : ℕ, t ≤ k →
      dcoefS K k k ((k : K) * θ) ρ t * ϑ k t
        - 2 * (((k - t) * (k - t) : ℕ) : K) * ϑ k (t + 1)
        - ρ * (t : K) * ϑ k (t - 1)
      = diagSource (ϑ (k - 1)) t

end Chain

section TwoTwo

variable {K : Type*} [CommRing K]

theorem ell_two_two_top (θA θB ρ : K) : ell 2 2 θA θB ρ 2 = 16 := by
  rw [ell, Rhone.Analysis.RecombinationExpansion.usmaniEntry_T_of_le 2 2 θA θB ρ
      (by omega : (0 : ℕ) ≤ 2)]
  norm_num [LinearAlgebra.Tridiag.cont, Rhone.LinearAlgebra.RecombinationExpansion.Qc_self,
      Finset.prod_Ico_succ_top]

theorem ell_dot_v_two (θA θB ρ : K) (w : ℕ → K) (hw : w 1 = 1) :
    (∑ s : Fin (min 2 2 + 1), ell 2 2 θA θB ρ (s : ℕ) * diagSource w (s : ℕ)) = 32 := by
  change (∑ s : Fin 3, ell 2 2 θA θB ρ (s : ℕ) * diagSource w (s : ℕ)) = 32
  rw [Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, diagSource_zero, diagSource_one,
    diagSource_two, hw, mul_zero, zero_add, mul_one, ell_two_two_top]
  norm_num

end TwoTwo

section Positivity

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {θ : K} {ϑ : ℕ → ℕ → K}

theorem pos_of_mul_pos_left {a b : K} (ha : 0 < a) (hab : 0 < a * b) : 0 < b :=
  pos_of_mul_pos_right hab ha.le

theorem dcoefS_diag_pos (hθ : 0 < θ) {k : ℕ} (hk : 1 ≤ k) (t : ℕ) :
    0 < dcoefS K k k ((k : K) * θ) 0 t := by
  have h1 : (0 : K) ≤ (((k + k - t) * (k + k - t - 1) : ℕ) : K) := Nat.cast_nonneg _
  have h2 : (0 : K) < (k : K) * θ := by
    have hkpos : (0 : K) < (k : K) := by exact_mod_cast hk
    exact mul_pos hkpos hθ
  simp only [dcoefS, zero_mul, add_zero]
  linarith

theorem chain_solve_zero (hc : IsDiagChain θ 0 ϑ) {k : ℕ} (hk : 2 ≤ k) {t : ℕ} (ht : t ≤ k) :
    dcoefS K k k ((k : K) * θ) 0 t * ϑ k t
      = diagSource (ϑ (k - 1)) t + 2 * (((k - t) * (k - t) : ℕ) : K) * ϑ k (t + 1) := by
  have h := hc.2 k hk t ht
  simp only [zero_mul, sub_zero] at h
  linarith [h]

theorem chain_step_pos (hθ : 0 < θ) (hc : IsDiagChain θ 0 ϑ) {k t : ℕ} (hk : 2 ≤ k)
    (ht : t < k) (hnext : 0 < ϑ k (t + 1))
    (hsrc : 0 ≤ diagSource (ϑ (k - 1)) t) : 0 < ϑ k t := by
  have h := chain_solve_zero hc hk (le_of_lt ht)
  have hd := dcoefS_diag_pos (K := K) hθ (by omega : 1 ≤ k) t
  have hcoe : (0 : K) < 2 * (((k - t) * (k - t) : ℕ) : K) := by
    have hpos : 0 < (k - t) * (k - t) := Nat.mul_pos (by omega) (by omega)
    have : (0 : K) < (((k - t) * (k - t) : ℕ) : K) := by exact_mod_cast hpos
    linarith
  have hterm : 0 < 2 * (((k - t) * (k - t) : ℕ) : K) * ϑ k (t + 1) := mul_pos hcoe hnext
  have hprod : 0 < dcoefS K k k ((k : K) * θ) 0 t * ϑ k t := by rw [h]; linarith
  exact pos_of_mul_pos_left hd hprod

theorem vartheta_top_pos_and_nonneg (hθ : 0 < θ) (hc : IsDiagChain θ 0 ϑ) :
    ∀ k : ℕ, 1 ≤ k → 0 < ϑ k k ∧ ∀ t : ℕ, t ≤ k → 0 ≤ ϑ k t := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ n ih =>
    intro _
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · refine ⟨by rw [hc.1 1]; simp, ?_⟩
      intro t _
      rw [hc.1 t, varthetaOne]
      split_ifs <;> norm_num
    · have hk : 2 ≤ n + 1 := by omega
      have hprev := ih hn
      have hv : ∀ t : ℕ, t ≤ n + 1 → 0 ≤ diagSource (ϑ (n + 1 - 1)) t := by
        intro t ht
        rw [diagSource]
        exact mul_nonneg (Nat.cast_nonneg _) (hprev.2 (t - 1) (by omega))
      have htop : 0 < ϑ (n + 1) (n + 1) := by
        have h := chain_solve_zero hc hk (le_refl (n + 1))
        rw [show n + 1 - (n + 1) = 0 from by omega] at h
        have hsrc : 0 < diagSource (ϑ (n + 1 - 1)) (n + 1) := by
          rw [diagSource]
          refine mul_pos ?_ hprev.1
          have hpos : 0 < (n + 1) * (n + 1 - 1) := Nat.mul_pos (by omega) (by omega)
          exact_mod_cast hpos
        have hd := dcoefS_diag_pos (K := K) hθ (by omega : 1 ≤ n + 1) (n + 1)
        have hprod : 0 < dcoefS K (n + 1) (n + 1) (((n + 1 : ℕ) : K) * θ) 0 (n + 1)
            * ϑ (n + 1) (n + 1) := by
          rw [h]
          have hz : (2 : K) * (((0 * 0 : ℕ)) : K) * ϑ (n + 1) (n + 1 + 1) = 0 := by
            norm_num
          rw [hz, add_zero]
          exact hsrc
        exact pos_of_mul_pos_left hd hprod
      refine ⟨htop, ?_⟩
      have hdown : ∀ d : ℕ, d ≤ n + 1 → 0 < ϑ (n + 1) (n + 1 - d) := by
        intro d
        induction d with
        | zero => intro _; simpa using htop
        | succ e ihe =>
          intro he
          have hnext : 0 < ϑ (n + 1) (n + 1 - e) := ihe (by omega)
          have hidx : n + 1 - (e + 1) + 1 = n + 1 - e := by omega
          refine chain_step_pos hθ hc hk (by omega : n + 1 - (e + 1) < n + 1) ?_
            (hv (n + 1 - (e + 1)) (by omega))
          rw [hidx]
          exact hnext
      intro t ht
      have hpt := hdown (n + 1 - t) (by omega)
      rw [show n + 1 - (n + 1 - t) = t from by omega] at hpt
      exact hpt.le

theorem vartheta_pos_at_zero (hθ : 0 < θ) (hc : IsDiagChain θ 0 ϑ) {k : ℕ} (hk : 2 ≤ k)
    {t : ℕ} (ht : t ≤ k) : 0 < ϑ k t := by
  have hall := vartheta_top_pos_and_nonneg hθ hc
  have hprev := hall (k - 1) (by omega)
  have hkk := (hall k (by omega)).1
  have hdown : ∀ d : ℕ, d ≤ k → 0 < ϑ k (k - d) := by
    intro d
    induction d with
    | zero => intro _; simpa using hkk
    | succ e ihe =>
      intro he
      have hnext : 0 < ϑ k (k - e) := ihe (by omega)
      have hidx : k - (e + 1) + 1 = k - e := by omega
      refine chain_step_pos hθ hc hk (by omega : k - (e + 1) < k) ?_ ?_
      · rw [hidx]; exact hnext
      · rw [diagSource]
        exact mul_nonneg (Nat.cast_nonneg _) (hprev.2 _ (by omega))
  have hpt := hdown (k - t) (by omega)
  rwa [show k - (k - t) = t from by omega] at hpt

theorem vartheta_ne_zero_at_zero (hθ : 0 < θ) (hc : IsDiagChain θ 0 ϑ) {k : ℕ} (hk : 2 ≤ k) :
    ϑ k k ≠ 0 := (vartheta_pos_at_zero hθ hc hk (le_refl k)).ne'

end Positivity

end Rhone.Probability.RareAlleleHierarchy
