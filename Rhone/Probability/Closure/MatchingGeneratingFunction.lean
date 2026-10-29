/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.Closure.Gpoly

/-! # DL‑2 in its displayed form -/

@[expose] public section

universe u

namespace Rhone.Probability.Closure

open Finset LinearAlgebra.Recursion LinearAlgebra.Multilinear Multilinear SlotDeletion

variable {F : Type*} [Field F]

noncomputable def mono3 (d1 d2 d3 : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.single 0 d1 + Finsupp.single 1 d2 + Finsupp.single 2 d3

@[simp] theorem mono3_apply_zero (d1 d2 d3 : ℕ) : mono3 d1 d2 d3 0 = d1 := by
  simp [mono3]

@[simp] theorem mono3_apply_one (d1 d2 d3 : ℕ) : mono3 d1 d2 d3 1 = d2 := by
  simp [mono3]

@[simp] theorem mono3_apply_two (d1 d2 d3 : ℕ) : mono3 d1 d2 d3 2 = d3 := by
  simp [mono3]

theorem mono3_eq_iff {a b c a' b' c' : ℕ} :
    mono3 a b c = mono3 a' b' c' ↔ a = a' ∧ b = b' ∧ c = c' := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · have := congrArg (fun f => f 0) h; simpa using this
    · have := congrArg (fun f => f 1) h; simpa using this
    · have := congrArg (fun f => f 2) h; simpa using this
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

theorem X_pow_prod_eq_monomial (d1 d2 d3 : ℕ) :
    ((MvPolynomial.X 0 : MvPolynomial (Fin 3) F) ^ d1 * MvPolynomial.X 1 ^ d2
        * MvPolynomial.X 2 ^ d3)
      = MvPolynomial.monomial (mono3 d1 d2 d3) 1 := by
  rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul_monomial,
    MvPolynomial.monomial_mul_monomial, mono3, one_mul, one_mul]

theorem coeff_term_pows (w : F) (s t p d1 d2 d3 : ℕ) :
    (MvPolynomial.C w * ((MvPolynomial.X 0 : MvPolynomial (Fin 3) F) ^ s
          * MvPolynomial.X 1 ^ t * MvPolynomial.X 2 ^ p)).coeff (mono3 d1 d2 d3)
      = if s = d1 ∧ t = d2 ∧ p = d3 then w else 0 := by
  rw [X_pow_prod_eq_monomial, MvPolynomial.C_mul_monomial, mul_one,
    MvPolynomial.coeff_monomial]
  by_cases h : s = d1 ∧ t = d2 ∧ p = d3
  · rw [ite_eq_left (mono3_eq_iff.mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun hc => h (mono3_eq_iff.mp hc)), ite_eq_right h]

variable {SA SB : Type u} [Fintype SA] [DecidableEq SA] [Fintype SB] [DecidableEq SB]

theorem coeff_Gcfg (πA πB : Fin 2 → F) (α : SA → Fin 2) (β : SB → Fin 2)
    {M : Finset (SA × SB)} (hM : IsMatching M) (d1 d2 d3 : ℕ) :
    (Gcfg πA πB (xi M α β)).coeff (mono3 d1 d2 d3)
      = ∑ S : Finset SA, ∑ T : Finset SB,
          if S.card = d1 ∧ T.card = d2 ∧ (pairsIn M S T).card = d3 then
            (∏ u ∈ Sᶜ, πA (α u)) * (∏ v ∈ Tᶜ, πB (β v)) * (∏ u ∈ S, eps F (α u))
              * ∏ v ∈ T, eps F (β v)
          else 0 := by
  rw [Gcfg_eq_sum πA πB α β hM, MvPolynomial.coeff_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [MvPolynomial.coeff_sum]
  exact Finset.sum_congr rfl fun T _ => coeff_term_pows _ _ _ _ _ _ _

theorem sum_range_triple_ite (v : ℕ → ℕ → ℕ → F) {n1 n2 n3 N1 N2 N3 : ℕ}
    (h1 : n1 < N1) (h2 : n2 < N2) (h3 : n3 < N3) :
    (∑ d1 ∈ Finset.range N1, ∑ d2 ∈ Finset.range N2, ∑ d3 ∈ Finset.range N3,
        if n1 = d1 ∧ n2 = d2 ∧ n3 = d3 then v d1 d2 d3 else 0) = v n1 n2 n3 := by
  rw [Finset.sum_eq_single_of_mem n1 (Finset.mem_range.mpr h1)]
  · rw [Finset.sum_eq_single_of_mem n2 (Finset.mem_range.mpr h2)]
    · rw [Finset.sum_eq_single_of_mem n3 (Finset.mem_range.mpr h3)]
      · rw [ite_eq_left ⟨rfl, rfl, rfl⟩]
      · intro d3 _ hd3
        rw [ite_eq_right fun hc => hd3 hc.2.2.symm]
    · intro d2 _ hd2
      refine Finset.sum_eq_zero fun d3 _ => ?_
      rw [ite_eq_right fun hc => hd2 hc.2.1.symm]
  · intro d1 _ hd1
    refine Finset.sum_eq_zero fun d2 _ => Finset.sum_eq_zero fun d3 _ => ?_
    rw [ite_eq_right fun hc => hd1 hc.1.symm]

omit [DecidableEq SA] [DecidableEq SB] in
theorem triple_swap (r1 r2 r3 : Finset ℕ) (f : ℕ → ℕ → ℕ → Finset SA → Finset SB → F) :
    (∑ d1 ∈ r1, ∑ d2 ∈ r2, ∑ d3 ∈ r3, ∑ S : Finset SA, ∑ T : Finset SB, f d1 d2 d3 S T)
      = ∑ S : Finset SA, ∑ T : Finset SB, ∑ d1 ∈ r1, ∑ d2 ∈ r2, ∑ d3 ∈ r3,
          f d1 d2 d3 S T := by
  have swap1 : ∀ (s : Finset ℕ) (g : ℕ → Finset SA → Finset SB → F),
      (∑ d ∈ s, ∑ S : Finset SA, ∑ T : Finset SB, g d S T)
        = ∑ S : Finset SA, ∑ T : Finset SB, ∑ d ∈ s, g d S T := by
    intro s g
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun S _ => Finset.sum_comm
  calc (∑ d1 ∈ r1, ∑ d2 ∈ r2, ∑ d3 ∈ r3, ∑ S : Finset SA, ∑ T : Finset SB, f d1 d2 d3 S T)
      = ∑ d1 ∈ r1, ∑ d2 ∈ r2, ∑ S : Finset SA, ∑ T : Finset SB, ∑ d3 ∈ r3,
          f d1 d2 d3 S T :=
        Finset.sum_congr rfl fun d1 _ => Finset.sum_congr rfl fun d2 _ =>
          swap1 r3 fun d3 S T => f d1 d2 d3 S T
    _ = ∑ d1 ∈ r1, ∑ S : Finset SA, ∑ T : Finset SB, ∑ d2 ∈ r2, ∑ d3 ∈ r3,
          f d1 d2 d3 S T :=
        Finset.sum_congr rfl fun d1 _ => swap1 r2 fun d2 S T => ∑ d3 ∈ r3, f d1 d2 d3 S T
    _ = ∑ S : Finset SA, ∑ T : Finset SB, ∑ d1 ∈ r1, ∑ d2 ∈ r2, ∑ d3 ∈ r3, f d1 d2 d3 S T :=
        swap1 r1 fun d1 S T => ∑ d2 ∈ r2, ∑ d3 ∈ r3, f d1 d2 d3 S T

theorem card_eq_nA {M : Finset (SA × SB)} (hM : IsMatching M) (α : SA → Fin 2)
    (β : SB → Fin 2) : Fintype.card SA = (xi M α β).nA := by
  rw [Config.nA, sumA_xi, t_xi, card_freeA hM]

theorem card_eq_nB {M : Finset (SA × SB)} (hM : IsMatching M) (α : SA → Fin 2)
    (β : SB → Fin 2) : Fintype.card SB = (xi M α β).nB := by
  rw [Config.nB, sumB_xi, t_xi, card_freeB hM]

variable [LinearOrder F] [IsStrictOrderedRing F]

theorem q_xi_eq_sum_Gcfg_coeff_mul_Phi {θA θB ρ : F} {πA πB : Fin 2 → F} (hθA : 0 < θA)
    (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    {q : Config 2 2 → F} (hq : IsSolution θA θB ρ πA πB q)
    (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1)
    (M : Finset (SA × SB)) (hM : IsMatching M) (α : SA → Fin 2) (β : SB → Fin 2) :
    q (xi M α β)
      = ∑ d1 ∈ Finset.range ((xi M α β).nA + 1), ∑ d2 ∈ Finset.range ((xi M α β).nB + 1),
          ∑ d3 ∈ Finset.range ((xi M α β).t + 1),
            (Gcfg πA πB (xi M α β)).coeff (mono3 d1 d2 d3)
              * Phi q πA πB d1 d2 d3 := by
  have hA := card_eq_nA hM α β
  have hB := card_eq_nB hM α β
  have hT : M.card = (xi M α β).t := (t_xi M α β).symm
  have hstep : ∀ d1 d2 d3 : ℕ,
      (Gcfg πA πB (xi M α β)).coeff (mono3 d1 d2 d3) * Phi q πA πB d1 d2 d3
        = ∑ S : Finset SA, ∑ T : Finset SB,
            if S.card = d1 ∧ T.card = d2 ∧ (pairsIn M S T).card = d3 then
              ((∏ u ∈ Sᶜ, πA (α u)) * (∏ v ∈ Tᶜ, πB (β v)) * (∏ u ∈ S, eps F (α u))
                * ∏ v ∈ T, eps F (β v)) * Phi q πA πB d1 d2 d3
            else 0 := by
    intro d1 d2 d3
    rw [coeff_Gcfg πA πB α β hM, Finset.sum_mul]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun T _ => ?_
    by_cases h : S.card = d1 ∧ T.card = d2 ∧ (pairsIn M S T).card = d3
    · rw [ite_eq_left h, ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right h, zero_mul]
  rw [Finset.sum_congr rfl fun d1 _ => Finset.sum_congr rfl fun d2 _ =>
    Finset.sum_congr rfl fun d3 _ => hstep d1 d2 d3, triple_swap]
  rw [q_xi_eq_sum_Phi hθA hθB hρ hq hπA hπB M hM α β]
  refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun T _ => ?_
  symm
  refine sum_range_triple_ite (fun d1 d2 d3 =>
      ((∏ u ∈ Sᶜ, πA (α u)) * (∏ v ∈ Tᶜ, πB (β v)) * (∏ u ∈ S, eps F (α u))
        * ∏ v ∈ T, eps F (β v)) * Phi q πA πB d1 d2 d3) ?_ ?_ ?_
  · have := Finset.card_le_univ S
    omega
  · have := Finset.card_le_univ T
    omega
  · have : (pairsIn M S T).card ≤ M.card := Finset.card_filter_le _ _
    omega

end Rhone.Probability.Closure
