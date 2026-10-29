/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Dynamics.MendelianLaws
/-!
# Partial-selfing generation laws under an explicit unrelated outcross environment

Source: crow_kimura1970, sec. 3.8, pp. 92–94. -/
@[expose] public section
namespace Rhone.Dynamics.MendelianIBD
open Finset
noncomputable def partialSelfingLaw {A : Type*} [Fintype A] [DecidableEq A]
    (s : ℝ) (q : ((Fin 2 → A) × (Fin 2 → A)) → ℝ) (p : (Fin 2 → A) → ℝ)
    (d : Fin 2 → A) : ℝ :=
  s * selfingLaw p d + (1 - s) * mendelianLaw q Prod.fst Prod.snd d
noncomputable def partialSelfingGeneration {A : Type*} [Fintype A] [DecidableEq A]
    (s : ℝ) (q : ℕ → ((Fin 2 → A) × (Fin 2 → A)) → ℝ)
    (p : (Fin 2 → A) → ℝ) : ℕ → (Fin 2 → A) → ℝ
  | 0 => p
  | t + 1 => partialSelfingLaw s (q t) (partialSelfingGeneration s q p t)
private theorem partial_law_total {A : Type*} [Fintype A] [DecidableEq A]
    (s : ℝ) (q : ((Fin 2 → A) × (Fin 2 → A)) → ℝ) (p : (Fin 2 → A) → ℝ)
    (hp : ∑ d, p d = 1) (hq : ∑ d, q d = 1) :
    ∑ d, partialSelfingLaw s q p d = 1 := by
  unfold partialSelfingLaw selfingLaw
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, mendelian_law_total _ _ _ hp,
    mendelian_law_total _ _ _ hq]
  ring
private theorem partial_law_nonnegative {A : Type*} [Fintype A] [DecidableEq A]
    (s : ℝ) (q : ((Fin 2 → A) × (Fin 2 → A)) → ℝ) (p : (Fin 2 → A) → ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hp0 : ∀ d, 0 ≤ p d) (hq0 : ∀ d, 0 ≤ q d)
    (d : Fin 2 → A) : 0 ≤ partialSelfingLaw s q p d := by
  exact add_nonneg (mul_nonneg hs0 (mendelian_law_nonnegative p id id hp0 d))
    (mul_nonneg (sub_nonneg.mpr hs1) (mendelian_law_nonnegative q _ _ hq0 d))
private theorem partial_law_ibd {A : Type*} [Fintype A] [DecidableEq A]
    (s : ℝ) (q : ((Fin 2 → A) × (Fin 2 → A)) → ℝ) (p : (Fin 2 → A) → ℝ)
    (hp0 : ∀ d, 0 ≤ p d) (hp : ∑ d, p d = 1)
    (hq0 : ∀ d, 0 ≤ q d) (hq : ∑ d, q d = 1) :
    founderIbd (partialSelfingLaw s q p) id =
      Inbreeding.partialSelfingStep s (founderIbd p id) +
        (1 - s) * founderKinship q Prod.fst Prod.snd := by
  have hmix : founderIbd (partialSelfingLaw s q p) id =
      s * founderIbd (selfingLaw p) id +
        (1 - s) * founderIbd (mendelianLaw q Prod.fst Prod.snd) id := by
    unfold founderIbd partialSelfingLaw
    simp only [add_mul, sum_add_distrib, mul_assoc, ← mul_sum]
  have hself := selfing_generation_ibd p hp0 hp 1
  simp only [Function.iterate_one, pow_one] at hself
  rw [hmix, hself, mendelian_law_ibd q Prod.fst Prod.snd hq0 hq]
  unfold Inbreeding.partialSelfingStep
  ring
private theorem partial_generation_semiconjugacy
    {A : Type*} [Fintype A] [DecidableEq A]
    (s : ℝ) (q : ℕ → ((Fin 2 → A) × (Fin 2 → A)) → ℝ)
    (p : (Fin 2 → A) → ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hp0 : ∀ d, 0 ≤ p d) (hp : ∑ d, p d = 1)
    (hq0 : ∀ t d, 0 ≤ q t d) (hq : ∀ t, ∑ d, q t d = 1)
    (hunrelated : ∀ t, founderKinship (q t) Prod.fst Prod.snd = 0) (t : ℕ) :
    founderIbd (partialSelfingGeneration s q p t) id =
      ((Inbreeding.partialSelfingStep s)^[t]) (founderIbd p id) := by
  have hvalid : ∀ t, (∀ d, 0 ≤ partialSelfingGeneration s q p t d) ∧
      (∑ d, partialSelfingGeneration s q p t d) = 1 := by
    intro t
    induction t with
    | zero => exact ⟨hp0, hp⟩
    | succ t ih =>
      exact ⟨partial_law_nonnegative s (q t) _ hs0 hs1 ih.1 (hq0 t),
        partial_law_total s (q t) _ ih.2 (hq t)⟩
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [partialSelfingGeneration, partial_law_ibd _ _ _ (hvalid t).1 (hvalid t).2
      (hq0 t) (hq t), hunrelated t, mul_zero, add_zero, ih, Function.iterate_succ_apply']
theorem partial_selfing_generation_ibd
    {A : Type*} [Fintype A] [DecidableEq A]
    (s : ℝ) (q : ℕ → ((Fin 2 → A) × (Fin 2 → A)) → ℝ)
    (p : (Fin 2 → A) → ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hp0 : ∀ d, 0 ≤ p d) (hp : ∑ d, p d = 1)
    (hq0 : ∀ t d, 0 ≤ q t d) (hq : ∀ t, ∑ d, q t d = 1)
    (hunrelated : ∀ t, founderKinship (q t) Prod.fst Prod.snd = 0) (t : ℕ) :
    founderIbd (partialSelfingGeneration s q p t) id =
      Inbreeding.partialSelfingFixed s + (s / 2) ^ t *
        (founderIbd p id - Inbreeding.partialSelfingFixed s) := by
  rw [partial_generation_semiconjugacy s q p hs0 hs1 hp0 hp hq0 hq hunrelated t]
  exact Inbreeding.partial_selfing_iterate (by linarith) _ _
theorem tendsto_partial_selfing_generation
    {A : Type*} [Fintype A] [DecidableEq A]
    (s : ℝ) (q : ℕ → ((Fin 2 → A) × (Fin 2 → A)) → ℝ)
    (p : (Fin 2 → A) → ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hp0 : ∀ d, 0 ≤ p d) (hp : ∑ d, p d = 1)
    (hq0 : ∀ t d, 0 ≤ q t d) (hq : ∀ t, ∑ d, q t d = 1)
    (hunrelated : ∀ t, founderKinship (q t) Prod.fst Prod.snd = 0) :
    Filter.Tendsto (fun t => founderIbd (partialSelfingGeneration s q p t) id)
      Filter.atTop (nhds (Inbreeding.partialSelfingFixed s)) := by
  have hfun : (fun t => founderIbd (partialSelfingGeneration s q p t) id) =
      (fun t => ((Inbreeding.partialSelfingStep s)^[t]) (founderIbd p id)) := by
    funext t
    exact partial_generation_semiconjugacy s q p hs0 hs1 hp0 hp hq0 hq hunrelated t
  rw [hfun]
  exact Inbreeding.tendsto_partial_selfing hs0 hs1 _
end Rhone.Dynamics.MendelianIBD
