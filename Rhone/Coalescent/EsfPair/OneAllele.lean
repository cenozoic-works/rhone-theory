/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.EsfPair.Inject
public import Rhone.Probability.Denominator.Marginal

/-! # One allele at locus `A`: the sampling probability is the one-locus marginal -/

@[expose] public section

namespace Rhone.Coalescent.EsfPair

open Finset TwoLocusGenealogy LinearAlgebra.Recursion

variable {KB : ℕ} {θA θB ρ : ℝ} {πA : Fin 1 → ℝ} {πB : Fin KB → ℝ}

theorem incf_decf {ι : Type*} [DecidableEq ι] {f : ι → ℕ} {j : ι} (h : f j ≠ 0) :
    incf (decf f j) j = f := by
  funext k
  by_cases hk : k = j
  · subst hk
    rw [incf_self, decf_self]
    omega
  · rw [incf_of_ne _ hk, decf_of_ne _ hk]

theorem addC_dropC {KA : ℕ} {ξ : Config KA KB} {i : Fin KA} {j : Fin KB} (h : ξ.c i j ≠ 0) :
    Probability.Denominator.addC (ξ.dropC i j) i j = ξ := by
  refine Config.ext rfl rfl ?_
  change Config.incC (Config.decC ξ.c i j) i j = ξ.c
  funext k
  by_cases hk : k = i
  · subst hk
    rw [Config.incC, Config.decC, Function.update_self, Function.update_self]
    exact incf_decf h
  · rw [Config.incC, Config.decC, Function.update_of_ne hk, Function.update_of_ne hk]

theorem q_of_one_alleleA (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (hπA : ∑ i, πA i = 1) :
    ∀ (T : ℕ) (ξ : Config 1 KB), ξ.t = T → ξ.a = (fun _ => 0) →
      LinearAlgebra.Recursion.q (πA := πA) (πB := πB) hθA hθB hρ ξ = qOne θB πB ξ.mB := by
  intro T
  induction T using Nat.strong_induction_on with
  | _ T IH =>
    intro ξ hT ha
    rcases Nat.eq_zero_or_pos T with hT0 | hTpos
    · have ht : ξ.t = 0 := by omega
      have hsA : ξ.sumA = 0 := by
        rw [Config.sumA, ha]
        simp
      have hnA : ξ.nA = 0 := by rw [Config.nA, hsA, ht]
      have hmB : ξ.mB = ξ.b := by
        funext j
        have hc : ξ.c = fun _ _ => 0 := ξ.c_eq_zero_of_t ht
        rw [Config.mB, Config.cCol, hc]
        simp
      rw [hmB]
      exact (q_isSolution hθA hθB hρ).eq_qOne_of_nA hθB ξ hnA
    · have hcne : ∃ j : Fin KB, ξ.c 0 j ≠ 0 := by
        by_contra hc
        have hall : ∀ j : Fin KB, ξ.c 0 j = 0 := fun j => by
          by_contra hj
          exact hc ⟨j, hj⟩
        have hz : ξ.t = 0 := by
          rw [Config.t, Fin.sum_univ_one]
          exact Finset.sum_eq_zero fun j _ => hall j
        omega
      obtain ⟨j, hj⟩ := hcne
      have hadd : Probability.Denominator.addC (ξ.dropC 0 j) 0 j = ξ := addC_dropC hj
      have hmarg := Probability.Denominator.q_marginalise_C (πB := πB) hθA hθB hρ hπA (ξ.dropC 0 j)
          j
      rw [Fin.sum_univ_one, hadd] at hmarg
      have hηa : (Probability.Denominator.addB (ξ.dropC 0 j) j).a = fun _ => 0 := ha
      have h1 : (ξ.dropC 0 j).t + 1 = ξ.t := Config.t_dropC ξ 0 j hj
      have hηt : (Probability.Denominator.addB (ξ.dropC 0 j) j).t = T - 1 := by
        have h2 : (Probability.Denominator.addB (ξ.dropC 0 j) j).t = (ξ.dropC 0 j).t := rfl
        omega
      have hcol : ∀ j'' : Fin KB, (ξ.dropC 0 j).cCol j'' = decf (fun j₀ => ξ.c 0 j₀) j j'' := by
        intro j''
        rw [Config.cCol, Fin.sum_univ_one]
        rfl
      have hcol0 : ∀ j'' : Fin KB, ξ.cCol j'' = ξ.c 0 j'' := by
        intro j''
        rw [Config.cCol, Fin.sum_univ_one]
      have hηc : ∀ j'' : Fin KB,
          (Probability.Denominator.addB (ξ.dropC 0 j) j).cCol j'' = (ξ.dropC 0 j).cCol j'' := fun _
              => rfl
      have hηmB : (Probability.Denominator.addB (ξ.dropC 0 j) j).mB = ξ.mB := by
        funext j'
        by_cases hjj : j' = j
        · subst hjj
          have hb : (Probability.Denominator.addB (ξ.dropC 0 j') j').b j' = ξ.b j' + 1 := incf_self
              _ _
          have hc : (ξ.dropC 0 j').cCol j' = ξ.c 0 j' - 1 := by
            rw [hcol j', decf_self]
          rw [Config.mB, Config.mB, hb, hηc j', hc, hcol0 j']
          omega
        · have hb : (Probability.Denominator.addB (ξ.dropC 0 j) j).b j' = ξ.b j' := incf_of_ne _ hjj
          have hc : (ξ.dropC 0 j).cCol j' = ξ.cCol j' := by
            rw [hcol j', decf_of_ne _ hjj, hcol0 j']
          rw [Config.mB, Config.mB, hb, hηc j', hc]
      rw [hmarg, IH (T - 1) (by omega) (Probability.Denominator.addB (ξ.dropC 0 j) j) hηt hηa, hηmB]

variable {n : ℕ}

def countB (σB : Fin n → Fin KB) (j : Fin KB) : ℕ :=
  (Finset.univ.filter fun k => σB k = j).card

theorem mB_cSample_one (σA : Fin n → Fin 1) (σB : Fin n → Fin KB) :
    (cSample σA σB).mB = countB σB := by
  funext j
  have h : (cSample σA σB).b = fun _ => 0 := rfl
  rw [Config.mB, h, Config.cCol, Fin.sum_univ_one]
  have hc : (cSample σA σB).c 0 j = (Finset.univ.filter fun k => σA k = 0 ∧ σB k = j).card := rfl
  rw [hc, countB]
  simp only [Nat.zero_add]
  congr 1
  refine Finset.filter_congr fun k _ => ?_
  simp [Subsingleton.elim (σA k) 0]

theorem q_cSample_one_alleleA (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (hπA : ∑ i, πA i = 1)
    (σA : Fin n → Fin 1) (σB : Fin n → Fin KB) :
    LinearAlgebra.Recursion.q (πA := πA) (πB := πB) hθA hθB hρ (cSample σA σB) = qOne θB πB
        (countB σB) := by
  rw [← mB_cSample_one σA σB]
  exact q_of_one_alleleA hθA hθB hρ hπA (cSample σA σB).t (cSample σA σB) rfl rfl

end Rhone.Coalescent.EsfPair
