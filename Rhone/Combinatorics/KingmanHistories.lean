/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import ADR11.Coalescent.Factorization
public import Rhone.Combinatorics.External.ADR11Counts
/-!
# Chronologically ranked histories of Kingman forest mergers: counts and masses

Source: kingman1982, Thm 1, eq. (1.13), (2.2). -/
@[expose] public section
namespace Rhone.Combinatorics
open Finset
universe u
def RankedForestHistory {L : Type u} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) : ℕ → Type u
  | 0 => PUnit
  | t + 1 => Σ G : {G : Finset (Finset L) // G ∈ ADR11.merges F},
      RankedForestHistory G.1 t
noncomputable instance {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (t : ℕ) : Fintype (RankedForestHistory F t) := by
  induction t generalizing F with
  | zero => change Fintype PUnit; infer_instance
  | succ t ih =>
    change Fintype (Σ G : {G : Finset (Finset L) // G ∈ ADR11.merges F},
      RankedForestHistory G.1 t)
    letI : ∀ G : {G : Finset (Finset L) // G ∈ ADR11.merges F},
      Fintype (RankedForestHistory G.1 t) := fun G => ih G.1
    infer_instance
abbrev RankedLabelledHistory (n : ℕ) :=
  RankedForestHistory (ADR11.singletonForest n) (n - 1)
def historyEnd {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) : (t : ℕ) → RankedForestHistory F t → Finset (Finset L)
  | 0, _ => F
  | t + 1, h => historyEnd h.1.1 t h.2
noncomputable def historyMass {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) : (t : ℕ) → RankedForestHistory F t → ℝ
  | 0, _ => 1
  | t + 1, h => ADR11.jumpMatrix F h.1.1 * historyMass h.1.1 t h.2
theorem card_ranked_forest_history
    {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (hF : ADR11.IsForest F) (t : ℕ)
    (ht : t ≤ (ADR11.roots F).card - 1) :
    Fintype.card (RankedForestHistory F t) =
      ∏ k ∈ Finset.range t, ((ADR11.roots F).card - k).choose 2 := by
  induction t generalizing F with
  | zero => change Fintype.card PUnit = _; simp
  | succ t ih =>
    change Fintype.card (Σ G : {G : Finset (Finset L) // G ∈ ADR11.merges F},
      RankedForestHistory G.1 t) = _
    rw [Fintype.card_sigma]
    have htail (G : {G : Finset (Finset L) // G ∈ ADR11.merges F}) :
        Fintype.card (RankedForestHistory G.1 t) =
          ∏ k ∈ range t, ((ADR11.roots F).card - (k + 1)).choose 2 := by
      obtain ⟨hG, hc, -⟩ := hF.of_mem_merges G.2
      rw [ih G.1 hG (by omega)]
      apply prod_congr rfl
      intro k hk
      congr 1
      omega
    simp_rw [htail]
    rw [sum_const, card_univ, Fintype.card_coe, hF.card_merges, nsmul_eq_mul,
      prod_range_succ']
    simp [mul_comm]
theorem ranked_history_end_probability
    {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (hF : ADR11.IsForest F) (t : ℕ)
    (ht : t ≤ (ADR11.roots F).card - 1) (G : Finset (Finset L)) :
    (∑ h : RankedForestHistory F t,
      if historyEnd F t h = G then historyMass F t h else 0) =
      (ADR11.jumpMatrix^t) F G := by
  induction t generalizing F with
  | zero =>
    change (∑ h : PUnit, if F = G then 1 else 0) = _
    simp [Matrix.one_apply, eq_comm]
  | succ t ih =>
    have hk : 2 ≤ (ADR11.roots F).card := by omega
    change (∑ h : (Σ H : {H : Finset (Finset L) // H ∈ ADR11.merges F},
      RankedForestHistory H.1 t),
      if historyEnd h.1.1 t h.2 = G then
        ADR11.jumpMatrix F h.1.1 * historyMass h.1.1 t h.2 else 0) = _
    rw [Fintype.sum_sigma]
    have hinner (H : {H : Finset (Finset L) // H ∈ ADR11.merges F}) :
        (∑ h : RankedForestHistory H.1 t,
          if historyEnd H.1 t h = G then
            ADR11.jumpMatrix F H.1 * historyMass H.1 t h else 0) =
        ADR11.jumpMatrix F H.1 * (ADR11.jumpMatrix ^ t) H.1 G := by
      obtain ⟨hH, hc, -⟩ := hF.of_mem_merges H.2
      have he := ih H.1 hH (by omega)
      calc
        _ = ADR11.jumpMatrix F H.1 *
            (∑ h : RankedForestHistory H.1 t,
              if historyEnd H.1 t h = G then historyMass H.1 t h else 0) := by
          rw [mul_sum]
          apply sum_congr rfl
          intro h hh
          split <;> simp_all
        _ = _ := congrArg (fun x => ADR11.jumpMatrix F H.1 * x) he
    simp_rw [hinner]
    rw [pow_succ', Matrix.mul_apply]
    simp_rw [ADR11.jumpMatrix_apply_of_isForest hk, ite_mul, zero_mul]
    rw [sum_ite_mem, univ_inter]
    simp only [Subtype.property, ite_true]
    exact sum_coe_sort (ADR11.merges F)
      (fun H => (((ADR11.roots F).card.choose 2 : ℕ) : ℝ)⁻¹ *
        (ADR11.jumpMatrix ^ t) H G)
private theorem history_product_factorial (m : ℕ) :
    2 ^ m * (∏ k ∈ range m, (m + 1 - k).choose 2) =
      (m + 1).factorial * m.factorial := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [prod_range_succ']
    have hshift : (∏ k ∈ range m, (m + 1 + 1 - (k + 1)).choose 2) =
        ∏ k ∈ range m, (m + 1 - k).choose 2 := by
      apply prod_congr rfl
      intro k hk
      congr 1
      omega
    rw [hshift, pow_succ]
    simp only [Nat.sub_zero]
    have hc := Nat.add_one_mul_choose_eq (m + 1) 1
    simp only [Nat.choose_one_right] at hc
    calc
      _ = ((m + 2).choose 2 * 2) *
          (2 ^ m * ∏ k ∈ range m, (m + 1 - k).choose 2) := by ring
      _ = ((m + 2) * (m + 1)) * ((m + 1).factorial * m.factorial) := by
        rw [← hc, ih]
      _ = _ := by
        simp only [Nat.factorial_succ]
        ring

theorem card_ranked_labelled_history (n : ℕ) (hn : 1 ≤ n) :
    Fintype.card (RankedLabelledHistory n) =
      n.factorial * (n - 1).factorial / 2 ^ (n - 1) := by
  rw [card_ranked_forest_history _ (ADR11.isForest_singletonForest n) _
    (by rw [ADR11.card_roots_singletonForest]), ADR11.card_roots_singletonForest]
  have h := history_product_factorial (n - 1)
  rw [Nat.sub_add_cancel hn] at h
  rw [← h, Nat.mul_div_right _ (by positivity : 0 < 2 ^ (n - 1))]
theorem ranked_history_mass_uniform
    {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (hF : ADR11.IsForest F) (t : ℕ)
    (ht : t ≤ (ADR11.roots F).card - 1) (h : RankedForestHistory F t) :
    historyMass F t h =
      ((Fintype.card (RankedForestHistory F t) : ℕ) : ℝ)⁻¹ := by
  induction t generalizing F with
  | zero => simp [historyMass, RankedForestHistory]
  | succ t ih =>
    obtain ⟨H, h⟩ := h
    obtain ⟨hH, hc, -⟩ := hF.of_mem_merges H.2
    have hk : 2 ≤ (ADR11.roots F).card := by omega
    change ADR11.jumpMatrix F H.1 * historyMass H.1 t h = _
    rw [ADR11.jumpMatrix_apply_of_isForest hk,
      ite_eq_left H.2, ih H.1 hH (by omega), card_ranked_forest_history F hF _ ht,
      card_ranked_forest_history H.1 hH _ (by omega), prod_range_succ']
    have hprod : (∏ k ∈ range t, ((ADR11.roots F).card - (k + 1)).choose 2) =
        ∏ k ∈ range t, ((ADR11.roots H.1).card - k).choose 2 := by
      apply prod_congr rfl
      intro k hk
      congr 1
      omega
    rw [hprod]
    simp [mul_inv_rev, mul_comm]
theorem ranked_labelled_history_mass (n : ℕ) (hn : 1 ≤ n)
    (h : RankedLabelledHistory n) :
    historyMass (ADR11.singletonForest n) (n - 1) h =
      (2 : ℝ) ^ (n - 1) / ((n.factorial : ℝ) * ((n - 1).factorial : ℝ)) := by
  rw [ranked_history_mass_uniform _ (ADR11.isForest_singletonForest n) _
    (by rw [ADR11.card_roots_singletonForest]) h,
    card_ranked_forest_history _ (ADR11.isForest_singletonForest n) _
      (by rw [ADR11.card_roots_singletonForest]), ADR11.card_roots_singletonForest]
  have hc := history_product_factorial (n - 1)
  rw [Nat.sub_add_cancel hn] at hc
  have hr : (2 : ℝ) ^ (n - 1) *
      ((∏ k ∈ range (n - 1), (n - k).choose 2 : ℕ) : ℝ) =
      (n.factorial : ℝ) * ((n - 1).factorial : ℝ) := by exact_mod_cast hc
  rw [← hr]
  have hp : (2 : ℝ) ^ (n - 1) ≠ 0 := by positivity
  field_simp
end Rhone.Combinatorics
