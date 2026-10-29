/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.TwoLocusGenealogy.Absorb

/-! # The ancestral chain as a Markov kernel, and its trajectory measure -/

@[expose] public section

namespace Rhone.Coalescent.TwoLocusGenealogy

open Finset LinearAlgebra.Recursion MeasureTheory ProbabilityTheory

variable {n : ℕ} {θA θB ρ : ℝ}

theorem stepU_finsetSum {ι : Type*} [Fintype ι] (g : ι → Finset (Lin n) → ℝ)
    (L : Finset (Lin n)) :
    (∑ x, stepU θA θB ρ (g x) L) = stepU θA θB ρ (fun M => ∑ x, g x M) L := by
  have h1 : (∑ x, ∑ p ∈ L, ∑ q ∈ L.erase p, g x (coalL L p q))
      = ∑ p ∈ L, ∑ q ∈ L.erase p, ∑ x, g x (coalL L p q) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  have h2 : (∑ x, ∑ p ∈ carA L, g x (mutAL L p)) = ∑ p ∈ carA L, ∑ x, g x (mutAL L p) :=
    Finset.sum_comm
  have h3 : (∑ x, ∑ p ∈ carB L, g x (mutBL L p)) = ∑ p ∈ carB L, ∑ x, g x (mutBL L p) :=
    Finset.sum_comm
  have h4 : (∑ x, ∑ p ∈ carC L, g x (recL L p)) = ∑ p ∈ carC L, ∑ x, g x (recL L p) :=
    Finset.sum_comm
  simp only [stepU, Finset.sum_add_distrib, ← Finset.mul_sum, h1, h2, h3, h4]

noncomputable def trans (θA θB ρ : ℝ) (L M : Finset (Lin n)) : ℝ :=
  if 0 < dtot θA θB ρ L then
    stepU θA θB ρ (fun M' => if M' = M then 1 else 0) L / dtot θA θB ρ L
  else if M = ∅ then 1 else 0

theorem dtot_empty : dtot θA θB ρ (∅ : Finset (Lin n)) = 0 := by
  simp [dtot, na, nb, tt, carA, carB, carC]

theorem dtot_nonneg (hθA : 0 ≤ θA) (hθB : 0 ≤ θB) (hρ : 0 ≤ ρ) (L : Finset (Lin n)) :
    0 ≤ dtot θA θB ρ L := by
  refine add_nonneg (add_nonneg (add_nonneg (Nat.cast_nonneg _) ?_) ?_) ?_
  · exact mul_nonneg hθA (Nat.cast_nonneg _)
  · exact mul_nonneg hθB (Nat.cast_nonneg _)
  · exact mul_nonneg hρ (Nat.cast_nonneg _)

theorem dtot_pos (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) {L : Finset (Lin n)} (hw : WF L)
    (hL : L.Nonempty) : 0 < dtot θA θB ρ L := by
  have hpos := na_add_nb_pos hw hL
  have h1 : (0 : ℝ) ≤ ((L.card * (L.card - 1) : ℕ) : ℝ) := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ ρ * ((tt L : ℕ) : ℝ) := mul_nonneg hρ (Nat.cast_nonneg _)
  have h3 : (0 : ℝ) ≤ θA * ((na L : ℕ) : ℝ) := mul_nonneg hθA.le (Nat.cast_nonneg _)
  have h4 : (0 : ℝ) ≤ θB * ((nb L : ℕ) : ℝ) := mul_nonneg hθB.le (Nat.cast_nonneg _)
  rcases Nat.eq_zero_or_pos (na L) with h | h
  · have hb : 0 < nb L := by omega
    have : (0 : ℝ) < θB * ((nb L : ℕ) : ℝ) := mul_pos hθB (by exact_mod_cast hb)
    simp only [dtot]
    linarith
  · have : (0 : ℝ) < θA * ((na L : ℕ) : ℝ) := mul_pos hθA (by exact_mod_cast h)
    simp only [dtot]
    linarith

theorem stepU_nonneg (hθA : 0 ≤ θA) (hθB : 0 ≤ θB) (hρ : 0 ≤ ρ) {g : Finset (Lin n) → ℝ}
    (hg : ∀ M, 0 ≤ g M) (L : Finset (Lin n)) : 0 ≤ stepU θA θB ρ g L := by
  refine add_nonneg (add_nonneg (add_nonneg ?_ ?_) ?_) ?_
  · exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hg _
  · exact mul_nonneg hθA (Finset.sum_nonneg fun _ _ => hg _)
  · exact mul_nonneg hθB (Finset.sum_nonneg fun _ _ => hg _)
  · exact mul_nonneg hρ (Finset.sum_nonneg fun _ _ => hg _)

theorem trans_nonneg (hθA : 0 ≤ θA) (hθB : 0 ≤ θB) (hρ : 0 ≤ ρ) (L M : Finset (Lin n)) :
    0 ≤ trans θA θB ρ L M := by
  rw [trans]
  split_ifs with hd
  · exact div_nonneg (stepU_nonneg hθA hθB hρ (fun M' => by positivity) L) hd.le
  · norm_num
  · norm_num

theorem sum_trans (L : Finset (Lin n)) : (∑ M, trans θA θB ρ L M) = 1 := by
  by_cases hd : 0 < dtot θA θB ρ L
  · have hM : ∀ M : Finset (Lin n), trans θA θB ρ L M
        = stepU θA θB ρ (fun M' => if M' = M then 1 else 0) L / dtot θA θB ρ L :=
      fun M => by rw [trans, ite_eq_left hd]
    simp only [hM]
    rw [← Finset.sum_div, stepU_finsetSum]
    have hone : (fun M' : Finset (Lin n) => ∑ M : Finset (Lin n), if M' = M then (1 : ℝ) else 0)
        = fun _ => (1 : ℝ) := by
      funext M'
      rw [Finset.sum_ite_eq Finset.univ M' (fun _ => (1 : ℝ)), ite_eq_left (Finset.mem_univ M')]
    rw [hone, stepU_one, div_self hd.ne']
  · have hM : ∀ M : Finset (Lin n), trans θA θB ρ L M = if M = ∅ then 1 else 0 :=
      fun M => by rw [trans, ite_eq_right hd]
    simp only [hM]
    rw [Finset.sum_ite_eq' Finset.univ (∅ : Finset (Lin n)) (fun _ => (1 : ℝ)),
      ite_eq_left (Finset.mem_univ _)]

def ASt (n : ℕ) : Type := Finset (Lin n)

namespace ASt

instance : MeasurableSpace (ASt n) := ⊤
instance : Fintype (ASt n) := inferInstanceAs (Fintype (Finset (Lin n)))
instance : DecidableEq (ASt n) := inferInstanceAs (DecidableEq (Finset (Lin n)))
instance : Inhabited (ASt n) := ⟨(∅ : Finset (Lin n))⟩
instance : Nonempty (ASt n) := ⟨(∅ : Finset (Lin n))⟩
instance : DiscreteMeasurableSpace (ASt n) := ⟨fun _ => trivial⟩

end ASt

noncomputable def onePMF (θA θB ρ : ℝ) (hθA : 0 ≤ θA) (hθB : 0 ≤ θB) (hρ : 0 ≤ ρ)
    (L : ASt n) : PMF (ASt n) :=
  PMF.ofFintype (fun M : ASt n =>
      ENNReal.ofReal (trans θA θB ρ (L : Finset (Lin n)) (M : Finset (Lin n)))) (by
    have hnn : ∀ M ∈ (Finset.univ : Finset (ASt n)),
        0 ≤ trans θA θB ρ (L : Finset (Lin n)) (M : Finset (Lin n)) :=
      fun M _ => trans_nonneg hθA hθB hρ _ _
    have h2 : (∑ M : ASt n, trans θA θB ρ (L : Finset (Lin n)) (M : Finset (Lin n))) = 1 :=
      sum_trans (L : Finset (Lin n))
    rw [(ENNReal.ofReal_sum_of_nonneg hnn).symm, h2, ENNReal.ofReal_one])

@[simp] theorem onePMF_apply (hθA : 0 ≤ θA) (hθB : 0 ≤ θB) (hρ : 0 ≤ ρ) (L M : ASt n) :
    onePMF θA θB ρ hθA hθB hρ L M = ENNReal.ofReal (trans θA θB ρ L M) := rfl

noncomputable def argKernel (θA θB ρ : ℝ) (hθA : 0 ≤ θA) (hθB : 0 ≤ θB) (hρ : 0 ≤ ρ) :
    Kernel (ASt n) (ASt n) where
  toFun L := (onePMF θA θB ρ hθA hθB hρ L).toMeasure
  measurable' := Measurable.of_discrete

theorem argKernel_apply (hθA : 0 ≤ θA) (hθB : 0 ≤ θB) (hρ : 0 ≤ ρ) (L : ASt n) :
    argKernel θA θB ρ hθA hθB hρ L = (onePMF θA θB ρ hθA hθB hρ L).toMeasure := rfl

instance isMarkovKernel_argKernel (hθA : 0 ≤ θA) (hθB : 0 ≤ θB) (hρ : 0 ≤ ρ) :
    IsMarkovKernel (argKernel (n := n) θA θB ρ hθA hθB hρ) :=
  ⟨fun L => by rw [argKernel_apply]; infer_instance⟩

theorem argKernel_singleton (hθA : 0 ≤ θA) (hθB : 0 ≤ θB) (hρ : 0 ≤ ρ) (L M : ASt n) :
    argKernel θA θB ρ hθA hθB hρ L {M}
      = ENNReal.ofReal (trans θA θB ρ (L : Finset (Lin n)) (M : Finset (Lin n))) := by
  rw [argKernel_apply, PMF.toMeasure_apply_singleton _ _ (MeasurableSet.of_discrete)]
  rfl

noncomputable def argSeq (θA θB ρ : ℝ) (hθA : 0 ≤ θA) (hθB : 0 ≤ θB) (hρ : 0 ≤ ρ) (m : ℕ) :
    Kernel ((_i : Finset.Iic m) → ASt n) (ASt n) :=
  (argKernel θA θB ρ hθA hθB hρ).comap (fun x => x ⟨m, Finset.mem_Iic.2 le_rfl⟩)
    Measurable.of_discrete

instance isMarkovKernel_argSeq (hθA : 0 ≤ θA) (hθB : 0 ≤ θB) (hρ : 0 ≤ ρ) (m : ℕ) :
    IsMarkovKernel (argSeq (n := n) θA θB ρ hθA hθB hρ m) := by
  rw [argSeq]
  infer_instance

noncomputable def argTraj (θA θB ρ : ℝ) (hθA : 0 ≤ θA) (hθB : 0 ≤ θB) (hρ : 0 ≤ ρ)
    (L : ASt n) : Measure ((_ : ℕ) → ASt n) :=
  Kernel.traj (X := fun _ => ASt n) (argSeq θA θB ρ hθA hθB hρ) 0 (fun _ => L)

instance isProbabilityMeasure_argTraj (hθA : 0 ≤ θA) (hθB : 0 ≤ θB) (hρ : 0 ≤ ρ) (L : ASt n) :
    IsProbabilityMeasure (argTraj (n := n) θA θB ρ hθA hθB hρ L) := by
  rw [argTraj]
  infer_instance

noncomputable def rateTot (θA θB ρ : ℝ) (L : Finset (Lin n)) : ℝ :=
  ((L.card * (L.card - 1) : ℕ) : ℝ) / 2 + θA / 2 * ((na L : ℕ) : ℝ)
    + θB / 2 * ((nb L : ℕ) : ℝ) + ρ / 2 * ((tt L : ℕ) : ℝ)

theorem two_mul_rateTot (L : Finset (Lin n)) :
    2 * rateTot θA θB ρ L = dtot θA θB ρ L := by
  rw [rateTot, dtot]; ring

theorem rateTot_eq_half_diag {KA KB : ℕ} {σA : Fin n → Fin KA} {σB : Fin n → Fin KB}
    {L : Finset (Lin n)} (hw : WF L) (hcl : Clean σA σB L) :
    rateTot θA θB ρ L = LinearAlgebra.Recursion.diag θA θB ρ (cfg σA σB L) / 2 := by
  rw [← dtot_eq_diag hw hcl, ← two_mul_rateTot]
  ring

end Rhone.Coalescent.TwoLocusGenealogy
