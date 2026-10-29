/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.FinitePhaseFirstDomination
public import Rhone.Statistics.Identifiability.FiniteRealizedPanMembership
public import Rhone.Statistics.Identifiability.WeightedSurvivalPositive

/-! # Finite homogeneous two-stage models, specified by checkable generator identities -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory Matrix
open scoped Topology Matrix Matrix.Norms.Operator ENNReal
namespace Rhone.Statistics.Identifiability.FinitePhase
open FiniteExponentialJets ThreeSampleMembership

structure Model (n m : ℕ) where
  A : Matrix (Fin n) (Fin n) ℝ
  B : Matrix (Fin m) (Fin m) ℝ
  F : Matrix (Fin n) (Fin m) ℝ
  N : Matrix (Fin (n + m)) (Fin (n + m)) ℝ
  α : Fin n → ℝ
  A_metzler : IsMetzler A
  B_metzler : IsMetzler B
  N_metzler : IsMetzler N
  A_rows : ∀ i, (∑ j, A i j) ≤ 0
  B_rows : ∀ i, (∑ j, B i j) ≤ 0
  N_rows : ∀ i, (∑ j, N i j) ≤ 0
  F_nonnegative : ∀ i j, 0 ≤ F i j
  α_nonnegative : ∀ i, 0 ≤ α i
  α_sum : ∑ i, α i = 1
  flux : F *ᵥ (fun _ => 1) = exitRate A
  pre_pre : ∀ i j, N (Fin.castAdd m i) (Fin.castAdd m j) = A i j
  post_pre : ∀ i j, N (Fin.natAdd n i) (Fin.castAdd m j) = 0
  pre_post : ∀ i j, N (Fin.castAdd m i) (Fin.natAdd n j) = F i j
  post_post : ∀ i j, N (Fin.natAdd n i) (Fin.natAdd n j) = B i j
  exit_pre : ∀ i, exitRate N (Fin.castAdd m i) = 0
  exit_post : ∀ j, exitRate N (Fin.natAdd n j) = exitRate B j

namespace Model
variable {n m : ℕ}
def density (M : Model n m) := FinitePhase.density M.A M.F M.B M.α
def law (M : Model n m) := FinitePhase.law M.A M.F M.B M.α
def γ (M : Model n m) : Fin (n + m) → ℝ := initial M.α
def h (_M : Model n m) : Fin (n + m) → ℝ :=
  Fin.addCases (fun _ => 1) (fun _ => 2/3)
def u (M : Model n m) (t : ℝ) : ℝ := dotProduct M.γ (NormedSpace.exp (t • M.N) *ᵥ M.h)
def d (M : Model n m) (t : ℝ) : ℝ :=
  dotProduct M.γ (NormedSpace.exp (t • M.N) *ᵥ (M.N *ᵥ M.h))

lemma γ_nonnegative (M : Model n m) (i : Fin (n + m)) : 0 ≤ M.γ i := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa [γ, initial] using M.α_nonnegative j
  · simp [γ, initial]

lemma γ_sum (M : Model n m) : ∑ i, M.γ i = 1 := by
  simp [γ, initial, Fin.sum_univ_add, M.α_sum]

lemma density_continuous (M : Model n m) : Continuous M.density :=
  orderedKernelDensity_continuous M.A M.B M.α M.F (exitRate M.B)

lemma density_nonnegative (M : Model n m) {p : ℝ × ℝ} (hp : p ∈ upperWedge) :
    0 ≤ M.density p :=
  orderedKernelDensity_nonnegative M.A M.B M.α M.F (exitRate M.B)
    M.A_metzler M.B_metzler M.α_nonnegative M.F_nonnegative
    (exitRate_nonneg M.B M.B_rows) hp

lemma root_marginal (M : Model n m) : M.law.map Prod.snd = WeightedExit.law M.N M.γ :=
  law_map_root M.N M.A M.F M.B M.α M.pre_pre M.post_pre M.pre_post M.post_post
    M.exit_pre M.exit_post (fun _ hp => M.density_nonnegative hp)

lemma first_marginal (M : Model n m) [IsProbabilityMeasure M.law] :
    M.law.map Prod.fst = WeightedExit.law M.A M.α := by
  let : IsProbabilityMeasure (FinitePhase.law M.A M.F M.B M.α) :=
    inferInstanceAs (IsProbabilityMeasure M.law)
  exact law_map_first_of_probability M.A M.F M.B M.α M.A_metzler M.A_rows
    M.B_metzler M.B_rows M.F_nonnegative M.α_nonnegative M.α_sum M.flux

lemma u_survivals (M : Model n m) (t : ℝ) :
    M.u t = (1/3 : ℝ) * WeightedExit.survival M.A M.α t +
      (2/3 : ℝ) * WeightedExit.survival M.N M.γ t := by
  simp only [u, γ, h, initial, dotProduct, Matrix.mulVec, WeightedExit.survival,
    flowOutput, pow_zero, Matrix.one_mul, Fin.sum_univ_add,
    Fin.addCases_left, Fin.addCases_right, zero_mul, Finset.sum_const_zero, add_zero,
    mul_one]
  simp_rw [phase_pre_exp M.N M.A M.pre_pre M.post_pre]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [← Finset.sum_mul]
  ring

lemma weighted_survival_eq (M : Model n m) [IsProbabilityMeasure M.law] :
    ∀ t, 0 ≤ t → weightedSurvival M.law t = M.u t := by
  intro t ht
  rw [weightedSurvival, M.first_marginal, M.root_marginal,
    WeightedExit.real_Ioc M.A M.α M.A_metzler M.A_rows M.α_nonnegative ht,
    WeightedExit.real_Ioc M.N M.γ M.N_metzler M.N_rows M.γ_nonnegative ht,
    M.α_sum, M.γ_sum, M.u_survivals]
  ring

end Model
end Rhone.Statistics.Identifiability.FinitePhase
