/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ErlangPhase.Resolvent

/-! # Laplace transforms of the initial-event density and mixture law in the Erlang-phase model -/

@[expose] public section

noncomputable section
open Matrix MeasureTheory Set Filter
open scoped Matrix Topology
namespace Rhone.Statistics.ErlangPhase
open MarkovChain.Identifiability Identifiability FinitePhase
variable {J N : ℕ}

set_option backward.isDefEq.respectTransparency false

def firstState (hN : 0 < N) (j : Fin J) : Fin (J * N) := coordinates.symm (j, ⟨0, hN⟩)

lemma weights_payoff (w : Fin J → ℝ) (hN : 0 < N) (v : Fin (J * N) → ℝ) :
    (∑ i, weights w i * v i) = ∑ j, w j * v (firstState hN j) := by
  rw [sum_coordinates]
  apply Finset.sum_congr rfl
  intro j _
  simp only [weights, Equiv.apply_symm_apply, ite_mul, zero_mul]
  rw [Finset.sum_eq_single ⟨0, hN⟩]
  · rfl
  · intro k _ hk
    have hn : k.val ≠ 0 := by intro h; exact hk (Fin.ext h)
    simp [hn]
  · simp

lemma first_survival_zero (r : Fin J → ℝ) (hr : ∀ j, 0 < r j) (hN : 0 < N) (j : Fin J) :
    Tendsto (flowOutput (pre (N := N) r) (firstState hN j) (fun _ => 1) 0) atTop (𝓝 0) := by
  let w : Fin J → ℝ := fun k => if k = j then 1 else 0
  have h := WeightedExit.survival_tendsto_zero_of_rowSpace (pre (N := N) r) (weights w)
    (pre_metzler r hr)
    (by
      intro i
      rw [pre_row]
      split_ifs
      · exact le_refl 0
      · exact neg_nonpos.mpr (hr _).le)
    (by intro i; unfold weights w; split_ifs <;> norm_num)
    ⟨potentialPre r w, potential_pre_mul r w hr⟩
  have he : WeightedExit.survival (pre (N := N) r) (weights w) =
      flowOutput (pre (N := N) r) (firstState hN j) (fun _ => 1) 0 := by
    funext t
    unfold WeightedExit.survival
    rw [weights_payoff w hN]
    simp [w]
  rwa [he] at h

lemma first_density_laplace (r : Fin J → ℝ) (hr : ∀ j, 0 < r j)
    (hN : 0 < N) (s : ℝ) (hs : 0 ≤ s) (j : Fin J) :
    (∫ t in Ioi 0, Real.exp (-s * t) *
      flowOutput (pre (N := N) r) (firstState hN j) (exitRate (pre (N := N) r)) 0 t) =
      (r j / (r j + s)) ^ N := by
  have h := reward_integral_eq_potential (generator (N := N) r - s • 1)
    (isMetzler_sub_scalar_identity (pre_metzler r hr) s) (firstState hN j)
    (laplacePotential r s) (exitRate (pre (N := N) r)) (laplacePotential_equation r s hr hs)
    (exitRate_nonneg (pre (N := N) r) (by
      intro i
      rw [pre_row]
      split_ifs
      · exact le_refl 0
      · exact neg_nonpos.mpr (hr _).le))
    (survival_sub_scalar_identity_tendsto_zero (pre (N := N) r) (pre_metzler r hr) hs _
      (first_survival_zero r hr hN j))
  simpa only [flowOutput_sub_scalar_identity, laplacePotential, firstState,
    Equiv.apply_symm_apply, Nat.sub_zero] using h

lemma first_density_laplace_integrable (r : Fin J → ℝ) (hr : ∀ j, 0 < r j)
    (hN : 0 < N) (s : ℝ) (hs : 0 ≤ s) (j : Fin J) :
    IntegrableOn (fun t => Real.exp (-s * t) *
      flowOutput (pre (N := N) r) (firstState hN j) (exitRate (pre (N := N) r)) 0 t) (Ioi 0) := by
  have h := reward_integrable (generator (N := N) r - s • 1)
    (isMetzler_sub_scalar_identity (pre_metzler r hr) s) (firstState hN j)
    (laplacePotential r s) (exitRate (pre (N := N) r)) (laplacePotential_equation r s hr hs)
    (exitRate_nonneg (pre (N := N) r) (by
      intro i
      rw [pre_row]
      split_ifs
      · exact le_refl 0
      · exact neg_nonpos.mpr (hr _).le))
    (survival_sub_scalar_identity_tendsto_zero (pre (N := N) r) (pre_metzler r hr) hs _
      (first_survival_zero r hr hN j))
  convert h using 1
  ext t
  exact (flowOutput_sub_scalar_identity (generator r) s (firstState hN j)
    (exitRate (pre r)) t).symm

lemma mixture_density_laplace (r w : Fin J → ℝ) (hr : ∀ j, 0 < r j)
    (hN : 0 < N) (s : ℝ) (hs : 0 ≤ s) :
    (∫ t in Ioi 0, Real.exp (-s * t) * WeightedExit.density (pre (N := N) r) (weights w) t) =
      ∑ j, w j * (r j / (r j + s)) ^ N := by
  have he : (fun t => Real.exp (-s * t) * WeightedExit.density (pre (N := N) r) (weights w) t) =
      fun t => ∑ j, w j * (Real.exp (-s * t) *
        flowOutput (pre (N := N) r) (firstState hN j) (exitRate (pre (N := N) r)) 0 t) := by
    funext t
    unfold WeightedExit.density
    rw [weights_payoff w hN, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    rw [integral_const_mul, first_density_laplace r hr hN s hs j]
  · intro j _
    exact (first_density_laplace_integrable r hr hN s hs j).const_mul (w j)

lemma mixture_law_laplace (r w : Fin J → ℝ) (hr : ∀ j, 0 < r j) (hw : ∀ j, 0 ≤ w j)
    (hN : 0 < N) (s : ℝ) (hs : 0 ≤ s) :
    (∫ t, Real.exp (-s * t) ∂WeightedExit.law (pre (N := N) r) (weights w)) =
      ∑ j, w j * (r j / (r j + s)) ^ N := by
  rw [WeightedExit.law, integral_withDensity_eq_integral_toReal_smul₀
    (WeightedExit.density_continuous (pre (N := N) r) (weights w)).aemeasurable.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  rw [← mixture_density_laplace r w hr hN s hs]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hn : 0 ≤ WeightedExit.density (pre (N := N) r) (weights w) t :=
    WeightedExit.density_nonnegative (pre (N := N) r) (weights w) (pre_metzler r hr)
      (by
        intro i
        rw [pre_row]
        split_ifs
        · exact le_refl 0
        · exact neg_nonpos.mpr (hr _).le)
      (by
        intro i
        unfold weights
        split_ifs
        · exact hw _
        · exact le_refl 0) ht.le
  simp only [ENNReal.toReal_ofReal hn, smul_eq_mul, mul_comm]

lemma model_first_laplace (r w : Fin J → ℝ) (b : ℝ) (hN : 0 < N)
    (hr : ∀ j, 0 < r j) (hw : ∀ j, 0 < w j) (hsum : ∑ j, w j = 1) (hb : 0 < b)
    (s : ℝ) (hs : 0 ≤ s) :
    (∫ t, Real.exp (-s * t) ∂(model r w b hN hr hw hsum hb).law.map Prod.fst) =
      ∑ j, w j * (r j / (r j + s)) ^ N := by
  let := model_probability r w b hN hr hw hsum hb
  rw [(model r w b hN hr hw hsum hb).first_marginal]
  exact mixture_law_laplace r w hr (fun j => (hw j).le) hN s hs

end Rhone.Statistics.ErlangPhase
