/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.TruncationRemainder.Drift
public import Rhone.LinearAlgebra.Recursion.OneLocus

/-! # Edge response recursion for weak selection at the one-locus boundary -/

@[expose] public section
namespace Rhone.Coalescent
open Finset LinearAlgebra.Recursion Analysis.TruncationRemainder TruncationRemainder

section IncDec

variable {K : ℕ}

theorem decf_incf_self (m : Fin K → ℕ) (i : Fin K) : decf (incf m i) i = m := by
  funext k
  by_cases h : k = i
  · rw [h, decf_self, incf_self]; omega
  · rw [decf_of_ne _ h, incf_of_ne _ h]

theorem incf_decf_self (m : Fin K → ℕ) {i : Fin K} (hi : m i ≠ 0) :
    incf (decf m i) i = m := by
  funext k
  by_cases h : k = i
  · rw [h, incf_self, decf_self]; omega
  · rw [incf_of_ne _ h, decf_of_ne _ h]

theorem decf_incf_of_ne (m : Fin K → ℕ) {i i₀ : Fin K} (h : i ≠ i₀) :
    decf (incf m i₀) i = incf (decf m i) i₀ := by
  funext k
  by_cases hk : k = i
  · rw [hk, decf_self, incf_of_ne _ h, incf_of_ne _ h, decf_self]
  · rw [decf_of_ne _ hk]
    by_cases hk0 : k = i₀
    · rw [hk0, incf_self, incf_self, decf_of_ne _ (Ne.symm h)]
    · rw [incf_of_ne _ hk0, incf_of_ne _ hk0, decf_of_ne _ hk]

end IncDec

section OneLocus

variable {K : ℕ} {θ : ℝ} {π : Fin K → ℝ}

noncomputable def tiltResponse (θ : ℝ) (π : Fin K → ℝ) (i₀ : Fin K) (m : Fin K → ℕ) : ℝ :=
  qOne θ π (incf m i₀) - π i₀ * qOne θ π m

theorem tiltResponse_zero (hθ : θ ≠ 0) (i₀ : Fin K) :
    tiltResponse θ π i₀ (fun _ => 0) = 0 := by
  rw [tiltResponse, qOne_eA hθ, qOne_zero]; ring

theorem qOne_incf_step (hθ : 0 < θ) (m : Fin K → ℕ) (i₀ : Fin K) :
    (θ * π i₀ + ((m i₀ : ℕ) : ℝ)) * qOne θ π m
      = (θ + ((∑ k, m k : ℕ) : ℝ)) * qOne θ π (incf m i₀) := by
  have h := qOne_step_of_ne_zero (θ := θ) (π := π) (incf m i₀) (i := i₀)
    (by rw [incf_self]; omega) (rising_ne_zero hθ _)
  rw [decf_incf_self, incf_self, sum_incf] at h
  simp only [Nat.cast_add, Nat.cast_one] at h
  linear_combination h

theorem tiltResponse_recursion (hθ : 0 < θ) (π : Fin K → ℝ) (i₀ : Fin K) (m : Fin K → ℕ) :
    ((((∑ k, m k) * ((∑ k, m k) - 1) : ℕ) : ℝ) + θ * ((∑ k, m k : ℕ) : ℝ))
        * tiltResponse θ π i₀ m
      = (∑ i, (((m i * (m i - 1) : ℕ) : ℝ) + θ * π i * ((m i : ℕ) : ℝ))
            * tiltResponse θ π i₀ (decf m i))
        + (((m i₀ : ℕ) : ℝ) * qOne θ π m
            - ((∑ k, m k : ℕ) : ℝ) * qOne θ π (incf m i₀)) := by
  have hR := qOne_recursion (π := π) hθ m
  have hR' := qOne_recursion (π := π) hθ (incf m i₀)
  have hS := qOne_incf_step (π := π) hθ m i₀
  have hterm : ∀ i : Fin K,
      (((incf m i₀ i * (incf m i₀ i - 1) : ℕ) : ℝ) + θ * π i * ((incf m i₀ i : ℕ) : ℝ))
          * qOne θ π (decf (incf m i₀) i)
        = (((m i * (m i - 1) : ℕ) : ℝ) + θ * π i * ((m i : ℕ) : ℝ))
            * qOne θ π (incf (decf m i) i₀)
          + (if i = i₀ then (2 * ((m i₀ : ℕ) : ℝ) + θ * π i₀) * qOne θ π m else 0) := by
    intro i
    by_cases hi : i = i₀
    · rw [hi, decf_incf_self, incf_self]
      simp only [↓reduceIte]
      by_cases h0 : m i₀ = 0
      · rw [h0]; simp
      · rw [incf_decf_self m h0, natCast_mul_pred, natCast_mul_pred]
        push_cast
        ring
    · simp only [hi, ↓reduceIte]
      rw [incf_of_ne _ hi, add_zero]
      by_cases h0 : m i = 0
      · rw [h0]; simp
      · rw [decf_incf_of_ne m hi]
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hterm i, Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ i₀, sum_incf] at hR'
  simp only [Finset.mem_univ, ↓reduceIte] at hR'
  have hN1 : ((((∑ k, m k) + 1) * ((∑ k, m k) + 1 - 1) : ℕ) : ℝ)
      = (((∑ k, m k) * ((∑ k, m k) - 1) : ℕ) : ℝ) + 2 * ((∑ k, m k : ℕ) : ℝ) := by
    rw [natCast_mul_pred, natCast_mul_pred]
    push_cast
    ring
  rw [hN1] at hR'
  simp only [Nat.cast_add, Nat.cast_one] at hR'
  have hsum : (∑ i, (((m i * (m i - 1) : ℕ) : ℝ) + θ * π i * ((m i : ℕ) : ℝ))
        * tiltResponse θ π i₀ (decf m i))
      = (∑ i, (((m i * (m i - 1) : ℕ) : ℝ) + θ * π i * ((m i : ℕ) : ℝ))
            * qOne θ π (incf (decf m i) i₀))
        - π i₀ * ∑ i, (((m i * (m i - 1) : ℕ) : ℝ) + θ * π i * ((m i : ℕ) : ℝ))
            * qOne θ π (decf m i) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [tiltResponse]
    ring
  rw [hsum, tiltResponse]
  linear_combination hR' - π i₀ * hR + hS

end OneLocus

section Edge

variable {KA KB : ℕ} {θA θB ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}

noncomputable def edgeNeutral (θA : ℝ) (πA : Fin KA → ℝ) (ξ : Config KA KB) : ℝ :=
  qOne θA πA ξ.a

noncomputable def edgeResponse (θA : ℝ) (πA : Fin KA → ℝ) (i₀ : Fin KA)
    (ξ : Config KA KB) : ℝ :=
  tiltResponse θA πA i₀ ξ.a

theorem diag_pos_of_nB_eq_zero (hθA : 0 < θA) (ξ : Config KA KB) (hB : ξ.nB = 0)
    (hn : 1 ≤ ξ.n) : 0 < diag θA θB ρ ξ := by
  rw [diag_of_nB_eq_zero ξ hB]
  have h1 : (0 : ℝ) ≤ ((ξ.n * (ξ.n - 1) : ℕ) : ℝ) := Nat.cast_nonneg _
  have h2 : (0 : ℝ) < ((ξ.n : ℕ) : ℝ) := by exact_mod_cast hn
  nlinarith

theorem sel_of_nB_eq_zero (i₀ : Fin KA) (u : Config KA KB → ℝ) (ξ : Config KA KB)
    (h : ξ.nB = 0) :
    sel i₀ u ξ = ((ξ.a i₀ : ℕ) : ℝ) * u ξ - ((ξ.n : ℕ) : ℝ) * u (incA ξ i₀) := by
  have h1 : ξ.sumB = 0 := by simp only [Config.nB] at h; omega
  have h2 : ξ.t = 0 := by simp only [Config.nB] at h; omega
  have hb : ξ.b = fun _ => 0 := ξ.b_eq_zero_of_sumB h1
  have hc : ξ.c = fun _ _ => 0 := ξ.c_eq_zero_of_t h2
  simp only [sel, Config.mA, Config.cRow, hb, hc]
  simp

theorem nB_incA (ξ : Config KA KB) (i₀ : Fin KA) : (incA ξ i₀).nB = ξ.nB := by
  simp only [Config.nB, sumB_incA, t_incA]

theorem sum_a_of_nB_eq_zero (ξ : Config KA KB) (h : ξ.nB = 0) : (∑ k, ξ.a k) = ξ.n := by
  have h1 : ξ.sumB = 0 := by simp only [Config.nB] at h; omega
  have h2 : ξ.t = 0 := by simp only [Config.nB] at h; omega
  simp only [Config.n, Config.sumA]; omega

theorem edge_neutral_recursion (hθA : 0 < θA) (ξ : Config KA KB) (hB : ξ.nB = 0) :
    diag θA θB ρ ξ * edgeNeutral θA πA ξ
      = rhs θA θB ρ πA πB (edgeNeutral θA πA) ξ := by
  have hone := qOne_recursion (π := πA) hθA ξ.a
  rw [sum_a_of_nB_eq_zero ξ hB] at hone
  rw [diag_of_nB_eq_zero ξ hB, rhs_of_nB_eq_zero _ ξ hB, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  simp only [edgeNeutral]
  rw [hone]
  refine Finset.sum_congr rfl fun i _ => ?_
  change _ = _ * qOne θA πA (decf ξ.a i) + _ * (_ * (_ * qOne θA πA (decf ξ.a i)))
  ring

theorem edge_response_recursion (hθA : 0 < θA) (i₀ : Fin KA) (ξ : Config KA KB)
    (hB : ξ.nB = 0) :
    diag θA θB ρ ξ * edgeResponse θA πA i₀ ξ
      = rhs θA θB ρ πA πB (edgeResponse θA πA i₀) ξ
        + sel i₀ (edgeNeutral θA πA) ξ := by
  have hone := tiltResponse_recursion hθA πA i₀ ξ.a
  rw [sum_a_of_nB_eq_zero ξ hB] at hone
  rw [diag_of_nB_eq_zero ξ hB, rhs_of_nB_eq_zero _ ξ hB, sel_of_nB_eq_zero i₀ _ ξ hB,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  simp only [edgeResponse, edgeNeutral]
  rw [hone]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  change _ = _ * tiltResponse θA πA i₀ (decf ξ.a i)
    + _ * (_ * (_ * tiltResponse θA πA i₀ (decf ξ.a i)))
  ring

theorem edge_unique (hθA : 0 < θA) (g u w : Config KA KB → ℝ)
    (h0 : ∀ ξ : Config KA KB, ξ.n = 0 → u ξ = w ξ)
    (hu : ∀ ξ : Config KA KB, ξ.nB = 0 → 1 ≤ ξ.n →
      diag θA θB ρ ξ * u ξ = rhs θA θB ρ πA πB u ξ + g ξ)
    (hw : ∀ ξ : Config KA KB, ξ.nB = 0 → 1 ≤ ξ.n →
      diag θA θB ρ ξ * w ξ = rhs θA θB ρ πA πB w ξ + g ξ) :
    ∀ ξ : Config KA KB, ξ.nB = 0 → u ξ = w ξ := by
  intro ξ₀
  induction hn : ξ₀.n using Nat.strong_induction_on generalizing ξ₀ with
  | _ N IH =>
    intro hB
    rcases Nat.eq_zero_or_pos N with hN | hN
    · exact h0 ξ₀ (by omega)
    · have e1 := hu ξ₀ hB (by omega)
      have e2 := hw ξ₀ hB (by omega)
      rw [rhs_of_nB_eq_zero u ξ₀ hB] at e1
      rw [rhs_of_nB_eq_zero w ξ₀ hB] at e2
      have hstep : ∀ i : Fin KA, ξ₀.a i ≠ 0 → u (ξ₀.dropA i) = w (ξ₀.dropA i) := by
        intro i hai
        refine IH (ξ₀.dropA i).n ?_ (ξ₀.dropA i) rfl ?_
        · have := ξ₀.n_dropA i hai; omega
        · rw [Config.nB_dropA]; exact hB
      have ht1 : ∀ i : Fin KA, ((ξ₀.a i * (ξ₀.a i - 1) : ℕ) : ℝ) * u (ξ₀.dropA i)
          = ((ξ₀.a i * (ξ₀.a i - 1) : ℕ) : ℝ) * w (ξ₀.dropA i) := by
        intro i
        by_cases hai : ξ₀.a i = 0
        · rw [hai]; simp
        · rw [hstep i hai]
      have ht2 : ∀ i : Fin KA, πA i * (((ξ₀.a i : ℕ) : ℝ) * u (ξ₀.dropA i))
          = πA i * (((ξ₀.a i : ℕ) : ℝ) * w (ξ₀.dropA i)) := by
        intro i
        by_cases hai : ξ₀.a i = 0
        · rw [hai]; simp
        · rw [hstep i hai]
      rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => ht1 i,
        Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => ht2 i, ← e2] at e1
      exact mul_left_cancel₀ (diag_pos_of_nB_eq_zero hθA ξ₀ hB (by omega)).ne' e1

theorem edge_response_unique (hθA : 0 < θA) (i₀ : Fin KA) (u : Config KA KB → ℝ)
    (h0 : ∀ ξ : Config KA KB, ξ.n = 0 → u ξ = 0)
    (hu : ∀ ξ : Config KA KB, ξ.nB = 0 → 1 ≤ ξ.n →
      diag θA θB ρ ξ * u ξ
        = rhs θA θB ρ πA πB u ξ + sel i₀ (edgeNeutral θA πA) ξ) :
    ∀ ξ : Config KA KB, ξ.nB = 0 → u ξ = tiltResponse θA πA i₀ ξ.a := by
  refine edge_unique (θB := θB) (ρ := ρ) (πA := πA) (πB := πB) hθA
    (sel i₀ (edgeNeutral θA πA)) u (edgeResponse θA πA i₀) ?_ hu ?_
  · intro ξ hξ
    rw [h0 ξ hξ, ξ.eq_zero_of_n_eq_zero hξ]
    exact (tiltResponse_zero hθA.ne' i₀).symm
  · intro ξ hB _
    exact edge_response_recursion hθA i₀ ξ hB

theorem sel_eq_sel_edgeNeutral (hθA : 0 < θA) {q : Config KA KB → ℝ}
    (hq : IsSolution θA θB ρ πA πB q) (i₀ : Fin KA) (ξ : Config KA KB) (hB : ξ.nB = 0) :
    sel i₀ q ξ = sel i₀ (edgeNeutral θA πA) ξ := by
  rw [sel_of_nB_eq_zero i₀ q ξ hB, sel_of_nB_eq_zero i₀ _ ξ hB,
    hq.eq_qOne_of_nB hθA ξ hB,
    hq.eq_qOne_of_nB hθA (incA ξ i₀) (by rw [nB_incA]; exact hB)]
  rfl

theorem IsSolution.edge_response_recursion (hθA : 0 < θA) {q : Config KA KB → ℝ}
    (hq : IsSolution θA θB ρ πA πB q) (i₀ : Fin KA) (ξ : Config KA KB) (hB : ξ.nB = 0) :
    diag θA θB ρ ξ * edgeResponse θA πA i₀ ξ
      = rhs θA θB ρ πA πB (edgeResponse θA πA i₀) ξ + sel i₀ q ξ := by
  rw [sel_eq_sel_edgeNeutral hθA hq i₀ ξ hB]
  exact Rhone.Coalescent.edge_response_recursion hθA i₀ ξ hB

theorem IsHierarchy.edge_zero (hθA : 0 < θA) {i₀ : Fin KA} {V : Config KA KB → ℝ}
    {q : ℕ → Config KA KB → ℝ}
    (hq : IsHierarchy V (Tplus θA θB ρ πA πB) (Umodel θA θB ρ i₀) (vplus θA θB ρ πA πB) q)
    (ξ : Config KA KB) (hB : ξ.nB = 0) (hn : 1 ≤ ξ.n) :
    q 0 ξ = qOne θA πA ξ.a := by
  set f : Config KA KB → ℝ := fun η => if η.n = 0 then 1 else q 0 η with hf
  have hfq : ∀ η : Config KA KB, 1 ≤ η.n → f η = q 0 η := by
    intro η hη
    have : η.n ≠ 0 := by omega
    simp [hf, this]
  have key := edge_unique (θB := θB) (ρ := ρ) (πA := πA) (πB := πB) hθA (fun _ => 0) f
    (edgeNeutral θA πA) ?_ ?_ ?_ ξ hB
  · rw [← hfq ξ hn, key]; rfl
  · intro η hη
    rw [η.eq_zero_of_n_eq_zero hη]
    have h1 : f 0 = 1 := by simp [hf]
    rw [h1]
    exact (qOne_zero (θ := θA) (π := πA)).symm
  · intro η hηB hηn
    have hD := (diag_pos_of_nB_eq_zero (θB := θB) (ρ := ρ) hθA η hηB hηn).ne'
    have h := hq.zero η
    rw [Tplus_add_vplus, Tfull] at h
    rw [hfq η hηn, h, add_zero]
    field_simp
    rfl
  · intro η hηB _
    rw [add_zero]
    exact edge_neutral_recursion hθA η hηB

theorem IsHierarchy.edge_one (hθA : 0 < θA) {i₀ : Fin KA} {V : Config KA KB → ℝ}
    {q : ℕ → Config KA KB → ℝ}
    (hq : IsHierarchy V (Tplus θA θB ρ πA πB) (Umodel θA θB ρ i₀) (vplus θA θB ρ πA πB) q)
    (ξ : Config KA KB) (hB : ξ.nB = 0) (hn : 1 ≤ ξ.n) :
    q 1 ξ = tiltResponse θA πA i₀ ξ.a := by
  have hr : ∀ η : Config KA KB, 1 ≤ η.n → restr (q 1) η = q 1 η := by
    intro η hη
    have : η.n ≠ 0 := by omega
    simp [restr, this]
  rw [← hr ξ hn]
  refine edge_response_unique (θB := θB) (ρ := ρ) (πB := πB) hθA i₀ (restr (q 1)) ?_ ?_ ξ hB
  · intro η hη
    simp [restr, hη]
  · intro η hηB hηn
    have hD := (diag_pos_of_nB_eq_zero (θB := θB) (ρ := ρ) hθA η hηB hηn).ne'
    have h := hq.succ 0 η
    rw [zero_add, Tplus, Tfull, Umodel] at h
    have hsel : sel i₀ (q 0) η = sel i₀ (edgeNeutral θA πA) η := by
      rw [sel_of_nB_eq_zero i₀ (q 0) η hηB, sel_of_nB_eq_zero i₀ _ η hηB,
        IsHierarchy.edge_zero hθA hq η hηB hηn,
        IsHierarchy.edge_zero hθA hq (incA η i₀) (by rw [nB_incA]; exact hηB)
          (by rw [n_incA]; omega)]
      rfl
    rw [hr η hηn, h, ← hsel]
    field_simp

end Edge

end Rhone.Coalescent
