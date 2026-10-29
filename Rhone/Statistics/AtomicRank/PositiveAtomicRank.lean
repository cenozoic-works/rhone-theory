/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.AtomicRank.AtomicJacobian

/-! # Full rank at a strictly positive finite-atomic probability distribution -/

@[expose] public section

noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace Rhone.Statistics.AtomicRank

lemma mixtureWeight_sum {N d : ℕ} (hN : 0 < N) (u : Fin d → ℝ) :
    (∑ a : Fin N ⊕ Fin d, mixtureWeight u a) = 1 := by
  simp only [mixtureWeight, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn : (N : ℝ) ≠ 0 := by positivity
  field_simp
  ring

lemma mixtureWeight_diagonal_pos {N d : ℕ} (hN : 0 < N) {ε : ℝ}
    (hε : 0 < ε) (hsmall : ε < 1 / ((d : ℝ) + 1)) :
    ∀ a : Fin N ⊕ Fin d, 0 < mixtureWeight (fun _ : Fin d => ε) a := by
  intro a
  cases a with
  | inl i =>
      simp only [mixtureWeight, Sum.elim_inl, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      apply div_pos _ (by positivity)
      have hd : (0 : ℝ) < (d : ℝ) + 1 := by positivity
      have he := (lt_div_iff₀ hd).mp hsmall
      nlinarith
  | inr i => exact hε

lemma mixtureLocation_unit {n d : ℕ} (z : Fin d → OpenUnitInterval)
    (a : Fin (n + 1) ⊕ Fin d) :
    0 < mixtureLocation (1 / ((n : ℝ) + 2)) (fun j => (z j).val) a ∧
      mixtureLocation (1 / ((n : ℝ) + 2)) (fun j => (z j).val) a < 1 := by
  cases a with
  | inl i =>
      change 0 < ((i.val : ℝ) + 1) * (1 / ((n : ℝ) + 2)) ∧
        ((i.val : ℝ) + 1) * (1 / ((n : ℝ) + 2)) < 1
      constructor
      · positivity
      · rw [mul_one_div, div_lt_one (by positivity)]
        exact_mod_cast (show i.val + 1 < n + 2 by omega)
  | inr i => exact (z i).property

theorem exists_positive_atomic_rank {n d : ℕ} (f : Fin d → Coefficients)
    (hf : ∀ i, DegreeBound (f i) n) (hi : IndependentModuloConstants f) :
    ∃ (z : Fin d → OpenUnitInterval) (ε : ℝ), 0 < ε ∧
      (∀ a : Fin (n + 1) ⊕ Fin d, 0 < mixtureWeight (fun _ : Fin d => ε) a) ∧
      (∑ a : Fin (n + 1) ⊕ Fin d, mixtureWeight (fun _ : Fin d => ε) a) = 1 ∧
      (∀ a : Fin (n + 1) ⊕ Fin d,
        0 < mixtureLocation (1 / ((n : ℝ) + 2)) (fun j => (z j).val) a ∧
          mixtureLocation (1 / ((n : ℝ) + 2)) (fun j => (z j).val) a < 1) ∧
      Matrix.det (atomicJacobian (N := n + 1) f (1 / ((n : ℝ) + 2))
        (fun j => (z j).val) (fun _ => ε)) ≠ 0 := by
  obtain ⟨z, hz⟩ := exists_nonsingular_atomic_baseline f hf hi
  let D : ℝ → ℝ := fun ε => Matrix.det
    (atomicJacobian (N := n + 1) f (1 / ((n : ℝ) + 2)) (fun j => (z j).val) (fun _ => ε))
  have hD : Continuous D :=
    (atomicJacobian_det_continuous (N := n + 1) f (1 / ((n : ℝ) + 2))
      (fun j => (z j).val)).comp (continuous_pi fun _ => continuous_id)
  have hD0 : D 0 ≠ 0 := hz
  have hnon : ∀ᶠ ε in 𝓝[>] (0 : ℝ), D ε ≠ 0 :=
    (hD.continuousAt.tendsto.eventually_ne hD0).filter_mono nhdsWithin_le_nhds
  have hbound0 : ∀ᶠ ε in 𝓝 (0 : ℝ), ε < 1 / ((d : ℝ) + 1) :=
    Iio_mem_nhds (by positivity : (0 : ℝ) < 1 / ((d : ℝ) + 1))
  have hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 1 / ((d : ℝ) + 1) :=
    hbound0.filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  obtain ⟨ε, hε, hsmall, hdet⟩ := (hpos.and (hbound.and hnon)).exists
  exact ⟨z, ε, hε, mixtureWeight_diagonal_pos (Nat.succ_pos n) hε hsmall,
    mixtureWeight_sum (Nat.succ_pos n) _, mixtureLocation_unit z, hdet⟩

end Rhone.Statistics.AtomicRank
