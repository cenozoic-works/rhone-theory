/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.PooledPairPowerIndex.Threshold
public import Rhone.Statistics.LinkedAgreementPower.BinaryTesting

/-! # Full-category scan and uniform common-law null size -/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace Rhone.Statistics.PooledPairPowerIndex
open DependenceBudget DependentPairedTest LinkedAgreementPower
variable {X : Type*} [Fintype X]

open scoped Classical in
def indicator (b x : X) : ℝ := if x = b then 1 else 0

omit [Fintype X] in
theorem indicator_binary (b : X) : Binary (indicator b) := by
  intro x
  unfold indicator
  split_ifs <;> simp

def ScanRejects {N : ℕ} (z : Fin N → X × X) : Prop :=
  ∃ b, RejectsAt (20 * Fintype.card X) (fun i => indicator b (z i).1 - indicator b (z i).2)

theorem probability_exists_le {ι : Type*} [Fintype ι] (P : Law X) (A : ι → X → Prop) :
    probability P (fun x => ∃ i, A i x) ≤ ∑ i, probability P (A i) := by
  classical
  unfold probability
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  by_cases h : ∃ i, A i x
  · obtain ⟨i, hi⟩ := h
    rw [ite_eq_left ⟨i, hi⟩]
    have hs := Finset.single_le_sum
      (fun j (_ : j ∈ Finset.univ) => show 0 ≤ if A j x then P.mass x else 0 by
        split_ifs <;> first | exact P.nonneg x | rfl) (Finset.mem_univ i)
    simpa only [ite_eq_left hi] using hs
  · rw [ite_eq_right h]
    exact Finset.sum_nonneg fun i _ => by split_ifs <;> first | exact P.nonneg x | rfl

theorem symmetric_threshold_size (P : Law X) (N : ℕ) (e : X ≃ X) (f : X → ℝ)
    (hP : ∀ x, P.mass (e x) = P.mass x) (hf : ∀ x, f (e x) = -f x)
    {T : ℝ} (hT : 0 < T) :
    probability (iid P N) (fun x => RejectsAt T (fun i => f (x i))) ≤ 1 / T := by
  let R : (Fin N → X) → ℝ := fun x =>
    (sumStatistic (fun i => f (x i))) ^ 2 / squareStatistic (fun i => f (x i))
  have hR : ∀ x, 0 ≤ R x := fun _ =>
    div_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hmean : rejection (iid P N) R ≤ 1 := by
    rw [show R = _ from rfl, symmetric_ratio_expectation P N e f hP hf, ← (iid P N).total]
    apply Finset.sum_le_sum
    intro x _
    apply mul_le_of_le_one_right ((iid P N).nonneg x)
    exact div_self_le_one _
  have hsub : ∀ x, RejectsAt T (fun i => f (x i)) → T ≤ R x :=
    fun x hx => (le_div_iff₀ hx.1).mpr hx.2
  exact (probability_mono (iid P N) hsub).trans
    ((finite_markov (iid P N) R hR hT).trans (div_le_div_of_nonneg_right hmean hT.le))

theorem scan_common_size [Nonempty X] (P : Law X) (N : ℕ) :
    probability (iid (independentPair P P) N) ScanRejects ≤ (1 : ℝ) / 20 := by
  have hM : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  apply (probability_exists_le (iid (independentPair P P) N) _).trans
  calc
    _ ≤ ∑ _b : X, 1 / (20 * (Fintype.card X : ℝ)) := by
      apply Finset.sum_le_sum
      intro b _
      apply symmetric_threshold_size _ N (Equiv.prodComm X X)
        (fun x => indicator b x.1 - indicator b x.2) _ _ (by positivity)
      · intro x
        simp [independentPair, mul_comm]
      · intro x
        change indicator b x.2 - indicator b x.1 = -(indicator b x.1 - indicator b x.2)
        ring
    _ = 1 / 20 := by simp

end Rhone.Statistics.PooledPairPowerIndex
