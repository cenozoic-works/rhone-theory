/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.Propagation.Coeff
public import Rhone.Probability.Propagation.Seed

/-! # The reduction: the whole up-set is one explicit linear image -/

@[expose] public section

namespace Rhone.Probability.Propagation

open Matrix LinearAlgebra.Tridiag

variable {K : Type*} [Field K]

theorem mulVec_left_cancel {n : ℕ} {A : Matrix (Fin n) (Fin n) K} (hA : IsUnit A.det)
    {x y : Fin n → K} (h : A *ᵥ x = A *ᵥ y) : x = y :=
  Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det A).2 hA) h

noncomputable def w (θA θB ρ κA γA κB γB : K) (p q : ℕ) (v : ℕ → K) (i j t : ℕ) : K :=
  if (i, j) = (p, q) then (if t ≤ min p q then v t else 0)
  else if p ≤ i ∧ q ≤ j then
    if hi : 2 ≤ i then
      if hj : 2 ≤ j then
        if ht : t < min i j + 1 then
          ((T K i j θA θB ρ)⁻¹ *ᵥ fun s : Fin (min i j + 1) =>
              srcVal κA γA κB γB
                (fun u => w θA θB ρ κA γA κB γB p q v (i - 2) j u)
                (fun u => w θA θB ρ κA γA κB γB p q v (i - 1) j u)
                (fun u => w θA θB ρ κA γA κB γB p q v i (j - 2) u)
                (fun u => w θA θB ρ κA γA κB γB p q v i (j - 1) u)
                (fun u => w θA θB ρ κA γA κB γB p q v (i - 2) (j - 2) u)
                (fun u => w θA θB ρ κA γA κB γB p q v (i - 2) (j - 1) u)
                (fun u => w θA θB ρ κA γA κB γB p q v (i - 1) (j - 2) u)
                (fun u => w θA θB ρ κA γA κB γB p q v (i - 1) (j - 1) u)
                i j (s : ℕ)) ⟨t, ht⟩
        else 0
      else 0
    else 0
  else 0
termination_by i + j
decreasing_by all_goals omega

variable {θA θB ρ κA γA κB γB : K} {p q : ℕ} {v : ℕ → K}

theorem w_base (t : ℕ) :
    w θA θB ρ κA γA κB γB p q v p q t = if t ≤ min p q then v t else 0 := by
  rw [w, ite_eq_left rfl]

theorem w_base_le {t : ℕ} (ht : t ≤ min p q) : w θA θB ρ κA γA κB γB p q v p q t = v t := by
  rw [w_base, ite_eq_left ht]

theorem w_off {i j : ℕ} (h : ¬(p ≤ i ∧ q ≤ j)) (t : ℕ) :
    w θA θB ρ κA γA κB γB p q v i j t = 0 := by
  rw [w, ite_eq_right, ite_eq_right h]
  intro he
  exact h ⟨le_of_eq (congrArg Prod.fst he).symm, le_of_eq (congrArg Prod.snd he).symm⟩

theorem w_range {i j t : ℕ} (h : min i j < t) : w θA θB ρ κA γA κB γB p q v i j t = 0 := by
  rw [w]
  by_cases he : (i, j) = (p, q)
  · have hi : i = p := congrArg Prod.fst he
    have hj : j = q := congrArg Prod.snd he
    subst hi; subst hj
    rw [ite_eq_left rfl, ite_eq_right (by omega)]
  · rw [ite_eq_right he]
    by_cases hu : p ≤ i ∧ q ≤ j
    · rw [ite_eq_left hu]
      by_cases hi : 2 ≤ i
      · rw [dite_eq_left hi]
        by_cases hj : 2 ≤ j
        · rw [dite_eq_left hj, dite_eq_right (by omega)]
        · rw [dite_eq_right hj]
      · rw [dite_eq_right hi]
    · rw [ite_eq_right hu]

theorem w_rec {i j : ℕ} (hpi : p ≤ i) (hqj : q ≤ j) (hne : (i, j) ≠ (p, q)) (hi : 2 ≤ i)
    (hj : 2 ≤ j) (hE : E K i j θA θB ρ ≠ 0) :
    T K i j θA θB ρ *ᵥ (fun s : Fin (min i j + 1) => w θA θB ρ κA γA κB γB p q v i j (s : ℕ))
      = fun s : Fin (min i j + 1) =>
          src κA γA κB γB (w θA θB ρ κA γA κB γB p q v) i j (s : ℕ) := by
  have hdet : IsUnit (T K i j θA θB ρ).det := isUnit_iff_ne_zero.2 hE
  have hval : (fun s : Fin (min i j + 1) => w θA θB ρ κA γA κB γB p q v i j (s : ℕ))
      = (T K i j θA θB ρ)⁻¹ *ᵥ fun s : Fin (min i j + 1) =>
          src κA γA κB γB (w θA θB ρ κA γA κB γB p q v) i j (s : ℕ) := by
    funext s
    rw [w, ite_eq_right hne, ite_eq_left ⟨hpi, hqj⟩, dite_eq_left hi, dite_eq_left hj,
      dite_eq_left s.isLt]
    congr 1
  rw [hval, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]

theorem res_eq_smul_w {r : ℕ → ℕ → ℕ → K} {c : K} (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hE : ∀ i j, p ≤ i → q ≤ j → (i, j) ≠ (p, q) → E K i j θA θB ρ ≠ 0)
    (hoff : ∀ i j t, ¬(p ≤ i ∧ q ≤ j) → r i j t = 0)
    (hbase : ∀ t, t ≤ min p q → r p q t = c * v t)
    (hrec : ∀ i j, p ≤ i → q ≤ j → (i, j) ≠ (p, q) →
      T K i j θA θB ρ *ᵥ (fun s : Fin (min i j + 1) => r i j (s : ℕ))
        = fun s : Fin (min i j + 1) => src κA γA κB γB r i j (s : ℕ)) :
    ∀ i j t, t ≤ min i j → r i j t = c * w θA θB ρ κA γA κB γB p q v i j t := by
  have key : ∀ n i j t, i + j = n → t ≤ min i j →
      r i j t = c * w θA θB ρ κA γA κB γB p q v i j t := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro i j t hn ht
      by_cases hu : p ≤ i ∧ q ≤ j
      · by_cases he : (i, j) = (p, q)
        · have hi : i = p := congrArg Prod.fst he
          have hj : j = q := congrArg Prod.snd he
          subst hi; subst hj
          rw [hbase t ht, w_base_le ht]
        · have hi : 2 ≤ i := le_trans hp hu.1
          have hj : 2 ≤ j := le_trans hq hu.2
          have hdet : IsUnit (T K i j θA θB ρ).det :=
            isUnit_iff_ne_zero.2 (hE i j hu.1 hu.2 he)
          have hIH : ∀ a b u, u ≤ min a b → a + b < i + j →
              r a b u = c * w θA θB ρ κA γA κB γB p q v a b u := by
            intro a b u hub hab
            exact ih (a + b) (by omega) a b u rfl hub
          have hsrc : ∀ s : Fin (min i j + 1),
              src κA γA κB γB r i j (s : ℕ)
                = c * src κA γA κB γB (w θA θB ρ κA γA κB γB p q v) i j (s : ℕ) := by
            intro s
            rw [src_range_congr κA γA κB γB r
                (fun a b u => c * w θA θB ρ κA γA κB γB p q v a b u) (by omega) (by omega)
                hIH (by have := s.isLt; omega),
              src_smul]
          have hmul : T K i j θA θB ρ *ᵥ (fun s : Fin (min i j + 1) => r i j (s : ℕ))
              = T K i j θA θB ρ
                *ᵥ (fun s : Fin (min i j + 1) => c * w θA θB ρ κA γA κB γB p q v i j (s : ℕ)) := by
            have hsm : (fun s : Fin (min i j + 1) =>
                  c * w θA θB ρ κA γA κB γB p q v i j (s : ℕ))
                = c • fun s : Fin (min i j + 1) => w θA θB ρ κA γA κB γB p q v i j (s : ℕ) := by
              funext s; simp
            rw [hrec i j hu.1 hu.2 he, hsm, Matrix.mulVec_smul,
              w_rec hu.1 hu.2 he hi hj (hE i j hu.1 hu.2 he)]
            funext s
            rw [hsrc s]
            rfl
          exact congrFun (mulVec_left_cancel hdet hmul) ⟨t, by omega⟩
      · rw [hoff i j t hu, w_off hu, mul_zero]
  intro i j t ht
  exact key (i + j) i j t rfl ht

theorem res_eq_smul_w_kernel [CharZero K] {r : ℕ → ℕ → ℕ → K} (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hρ : ρ ≠ 0) (hEpq : E K p q θA θB ρ = 0)
    (hcop : ∀ s, s < min p q → Rhone.Analysis.DenominatorEquation.Delta K p q θA θB ρ s = 0 →
      Rhone.Analysis.DenominatorEquation.DeltaP K p q θA θB ρ (s + 1) ≠ 0)
    (hE : ∀ i j, p ≤ i → q ≤ j → (i, j) ≠ (p, q) → E K i j θA θB ρ ≠ 0)
    (hoff : ∀ i j t, ¬(p ≤ i ∧ q ≤ j) → r i j t = 0)
    (hker : T K p q θA θB ρ *ᵥ (fun s : Fin (min p q + 1) => r p q (s : ℕ)) = 0)
    (hrec : ∀ i j, p ≤ i → q ≤ j → (i, j) ≠ (p, q) →
      T K i j θA θB ρ *ᵥ (fun s : Fin (min i j + 1) => r i j (s : ℕ))
        = fun s : Fin (min i j + 1) => src κA γA κB γB r i j (s : ℕ)) :
    ∃ c : K,
      (∀ i j t, t ≤ min i j →
        r i j t = c * w θA θB ρ κA γA κB γB p q (vker K p q θA θB ρ) i j t)
        ∧ ((∃ t, t ≤ min p q ∧ r p q t ≠ 0) ↔ c ≠ 0) := by
  obtain ⟨c, hc⟩ := res_base_eq_smul_vker hρ hEpq hcop hker
  refine ⟨c, res_eq_smul_w hp hq hE hoff hc hrec, ?_⟩
  constructor
  · rintro ⟨t, ht, hne⟩ hc0
    exact hne (by rw [hc t ht, hc0, zero_mul])
  · intro hc0
    exact ⟨0, Nat.zero_le _, by
      rw [hc 0 (Nat.zero_le _)]
      exact mul_ne_zero hc0 (vker_ne_zero hρ hEpq hcop (Nat.zero_le _))⟩

theorem assembly_eq {r : ℕ → ℕ → ℕ → K} {c : K} (S : Finset (ℕ × ℕ × ℕ)) (g : ℕ × ℕ × ℕ → K)
    (hS : ∀ d ∈ S, d.2.2 ≤ min d.1 d.2.1)
    (hprop : ∀ i j t, t ≤ min i j → r i j t = c * w θA θB ρ κA γA κB γB p q v i j t) :
    (∑ d ∈ S, g d * r d.1 d.2.1 d.2.2)
      = c * ∑ d ∈ S, g d * w θA θB ρ κA γA κB γB p q v d.1 d.2.1 d.2.2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [hprop d.1 d.2.1 d.2.2 (hS d hd)]
  ring

theorem assembly_ne_zero_iff {r : ℕ → ℕ → ℕ → K} {c : K} (hc : c ≠ 0) (S : Finset (ℕ × ℕ × ℕ))
    (g : ℕ × ℕ × ℕ → K) (hS : ∀ d ∈ S, d.2.2 ≤ min d.1 d.2.1)
    (hprop : ∀ i j t, t ≤ min i j → r i j t = c * w θA θB ρ κA γA κB γB p q v i j t) :
    (∑ d ∈ S, g d * r d.1 d.2.1 d.2.2) ≠ 0
      ↔ (∑ d ∈ S, g d * w θA θB ρ κA γA κB γB p q v d.1 d.2.1 d.2.2) ≠ 0 := by
  rw [assembly_eq S g hS hprop]
  exact mul_ne_zero_iff.trans ⟨fun h => h.2, fun h => ⟨hc, h⟩⟩

end Rhone.Probability.Propagation
