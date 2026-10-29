/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.TwoLocusGenealogy.Kernel
public import Rhone.MarkovChain.Trajectory
public import Rhone.MarkovChain.RateChain

/-! # The two-locus ancestral chain as an instance of the Core chain definitions -/

@[expose] public section
namespace Rhone.Coalescent
open MeasureTheory ProbabilityTheory Finset Rhone.LinearAlgebra MarkovChain TwoLocusGenealogy

variable {n : ℕ} {θA θB ρ : ℝ}

noncomputable def argChain (θA θB ρ : ℝ) (hθA : 0 ≤ θA) (hθB : 0 ≤ θB) (hρ : 0 ≤ ρ) :
    FinChain (ASt n) where
  P := fun L M => trans θA θB ρ L M
  nonneg := fun L M => trans_nonneg hθA hθB hρ L M
  row_sum := fun L => sum_trans L

theorem argChain_P (hθA : 0 ≤ θA) (hθB : 0 ≤ θB) (hρ : 0 ≤ ρ) (L M : ASt n) :
    (argChain θA θB ρ hθA hθB hρ).P L M = trans θA θB ρ L M := rfl

theorem argChain_kernel (hθA : 0 ≤ θA) (hθB : 0 ≤ θB) (hρ : 0 ≤ ρ) :
    (argChain (n := n) θA θB ρ hθA hθB hρ).kernel = argKernel θA θB ρ hθA hθB hρ := rfl

theorem argChain_pathLaw (hθA : 0 ≤ θA) (hθB : 0 ≤ θB) (hρ : 0 ≤ ρ) (L : ASt n) :
    (argChain θA θB ρ hθA hθB hρ).pathLaw L = argTraj θA θB ρ hθA hθB hρ L := rfl

theorem argTraj_real_eval (hθA : 0 ≤ θA) (hθB : 0 ≤ θB) (hρ : 0 ≤ ρ) (m : ℕ) (L M : ASt n) :
    (argTraj θA θB ρ hθA hθB hρ L).real {ω | ω m = M} =
      (argChain θA θB ρ hθA hθB hρ).stepN m L M := by
  rw [← argChain_pathLaw]
  exact FinChain.pathLaw_real_eval _ m L M

theorem argChain_isAbsorbing_empty (hθA : 0 ≤ θA) (hθB : 0 ≤ θB) (hρ : 0 ≤ ρ) :
    (argChain (n := n) θA θB ρ hθA hθB hρ).IsAbsorbing (∅ : Finset (Lin n)) := by
  have hd : ¬ 0 < dtot θA θB ρ (∅ : Finset (Lin n)) := by
    rw [dtot_empty]
    exact lt_irrefl 0
  change trans θA θB ρ (∅ : Finset (Lin n)) ∅ = 1
  rw [Coalescent.TwoLocusGenealogy.trans, ite_eq_right hd, ite_eq_left rfl]

theorem coalL_ne {L : Finset (Lin n)} {p q : Lin n} (hp : p ∈ L) (hq : q ∈ L.erase p) :
    coalL L p q ≠ L := by
  intro h
  have h1 : (coalL L p q).card ≤ ((L.erase p).erase q).card + 1 := Finset.card_insert_le _ _
  have h2 : 0 < (L.erase p).card := Finset.card_pos.2 ⟨q, hq⟩
  rw [Finset.card_erase_of_mem hq, Finset.card_erase_of_mem hp, h] at h1
  rw [Finset.card_erase_of_mem hp] at h2
  omega

theorem mutAL_ne {L : Finset (Lin n)} {p : Lin n} (hp : p ∈ carA L) : mutAL L p ≠ L := by
  obtain ⟨hpL, hne⟩ := mem_carA.1 hp
  intro h
  have hmem : p ∈ mutAL L p := by
    rw [h]
    exact hpL
  unfold mutAL at hmem
  split_ifs at hmem
  · exact Finset.notMem_erase p L hmem
  · rcases Finset.mem_insert.1 hmem with h1 | h1
    · exact hne.ne_empty (congrArg Prod.fst h1)
    · exact Finset.notMem_erase p L h1

theorem mutBL_ne {L : Finset (Lin n)} {p : Lin n} (hp : p ∈ carB L) : mutBL L p ≠ L := by
  obtain ⟨hpL, hne⟩ := mem_carB.1 hp
  intro h
  have hmem : p ∈ mutBL L p := by
    rw [h]
    exact hpL
  unfold mutBL at hmem
  split_ifs at hmem
  · exact Finset.notMem_erase p L hmem
  · rcases Finset.mem_insert.1 hmem with h1 | h1
    · exact hne.ne_empty (congrArg Prod.snd h1)
    · exact Finset.notMem_erase p L h1

theorem recL_ne {L : Finset (Lin n)} {p : Lin n} (hp : p ∈ carC L) : recL L p ≠ L := by
  obtain ⟨hpL, hneA, hneB⟩ := mem_carC.1 hp
  intro h
  have hmem : p ∈ recL L p := by
    rw [h]
    exact hpL
  unfold recL at hmem
  rcases Finset.mem_insert.1 hmem with h1 | h1
  · exact hneB.ne_empty (congrArg Prod.snd h1)
  · rcases Finset.mem_insert.1 h1 with h2 | h2
    · exact hneA.ne_empty (congrArg Prod.fst h2)
    · exact Finset.notMem_erase p L h2

theorem stepU_indicator_self (θA θB ρ : ℝ) (L : Finset (Lin n)) :
    stepU θA θB ρ (fun M => if M = L then 1 else 0) L = 0 := by
  have h1 : (∑ p ∈ L, ∑ q ∈ L.erase p, (if coalL L p q = L then (1 : ℝ) else 0)) = 0 :=
    Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun q hq => ite_eq_right (coalL_ne hp hq)
  have h2 : (∑ p ∈ carA L, (if mutAL L p = L then (1 : ℝ) else 0)) = 0 :=
    Finset.sum_eq_zero fun p hp => ite_eq_right (mutAL_ne hp)
  have h3 : (∑ p ∈ carB L, (if mutBL L p = L then (1 : ℝ) else 0)) = 0 :=
    Finset.sum_eq_zero fun p hp => ite_eq_right (mutBL_ne hp)
  have h4 : (∑ p ∈ carC L, (if recL L p = L then (1 : ℝ) else 0)) = 0 :=
    Finset.sum_eq_zero fun p hp => ite_eq_right (recL_ne hp)
  simp only [stepU, h1, h2, h3, h4, mul_zero, add_zero]

theorem sum_stepU_indicator (θA θB ρ : ℝ) (L : Finset (Lin n)) :
    (∑ M : Finset (Lin n), stepU θA θB ρ (fun M' => if M' = M then 1 else 0) L) =
      dtot θA θB ρ L := by
  have hone : (fun M' : Finset (Lin n) => ∑ M : Finset (Lin n), if M' = M then (1 : ℝ) else 0)
      = fun _ => (1 : ℝ) := by
    funext M'
    rw [Finset.sum_ite_eq Finset.univ M' (fun _ => (1 : ℝ)), ite_eq_left (Finset.mem_univ M')]
  rw [stepU_finsetSum, hone, stepU_one]

noncomputable def argRateChain (θA θB ρ : ℝ) (hθA : 0 ≤ θA) (hθB : 0 ≤ θB) (hρ : 0 ≤ ρ) :
    RateChain (ASt n) where
  Q := fun (L M : Finset (Lin n)) => if L = M then -(dtot θA θB ρ L / 2) else
    stepU θA θB ρ (fun M' => if M' = M then 1 else 0) L / 2
  off_diag_nonneg := fun (L M : Finset (Lin n)) hLM => by
    have hLM' : ¬ L = M := hLM
    rw [ite_eq_right hLM']
    refine div_nonneg (stepU_nonneg hθA hθB hρ (fun M' => ?_) L) (by norm_num)
    split_ifs <;> norm_num
  row_sum := fun (L : Finset (Lin n)) => by
    have hterm : ∀ M : Finset (Lin n),
        (if L = M then -(dtot θA θB ρ L / 2) else
          stepU θA θB ρ (fun M' => if M' = M then 1 else 0) L / 2) =
        stepU θA θB ρ (fun M' => if M' = M then 1 else 0) L / 2 -
          (if L = M then dtot θA θB ρ L / 2 else 0) := by
      intro M
      by_cases h : L = M
      · subst h
        rw [ite_eq_left rfl, ite_eq_left rfl, stepU_indicator_self]
        ring
      · rw [ite_eq_right h, ite_eq_right h, sub_zero]
    change (∑ M : Finset (Lin n), (if L = M then -(dtot θA θB ρ L / 2) else
      stepU θA θB ρ (fun M' => if M' = M then 1 else 0) L / 2)) = 0
    simp only [hterm]
    rw [Finset.sum_sub_distrib, ← Finset.sum_div,
      Finset.sum_ite_eq Finset.univ L (fun _ => dtot θA θB ρ L / 2),
      ite_eq_left (Finset.mem_univ L), sum_stepU_indicator]
    ring

theorem argRateChain_Q_self (hθA : 0 ≤ θA) (hθB : 0 ≤ θB) (hρ : 0 ≤ ρ) (L : Finset (Lin n)) :
    (argRateChain θA θB ρ hθA hθB hρ).Q L L = -(dtot θA θB ρ L / 2) :=
  ite_eq_left rfl

theorem argRateChain_Q_of_ne (hθA : 0 ≤ θA) (hθB : 0 ≤ θB) (hρ : 0 ≤ ρ)
    {L M : Finset (Lin n)} (hLM : L ≠ M) :
    (argRateChain θA θB ρ hθA hθB hρ).Q L M =
      stepU θA θB ρ (fun M' => if M' = M then 1 else 0) L / 2 :=
  ite_eq_right hLM

theorem trans_of_pos {L : Finset (Lin n)} (M : Finset (Lin n)) (hL : 0 < dtot θA θB ρ L) :
    trans θA θB ρ L M =
      stepU θA θB ρ (fun M' => if M' = M then 1 else 0) L / dtot θA θB ρ L := by
  rw [Coalescent.TwoLocusGenealogy.trans, ite_eq_left hL]

theorem trans_empty (θA θB ρ : ℝ) (M : Finset (Lin n)) :
    trans θA θB ρ (∅ : Finset (Lin n)) M = if M = ∅ then 1 else 0 := by
  have hd : ¬ 0 < dtot θA θB ρ (∅ : Finset (Lin n)) := by
    rw [dtot_empty]
    exact lt_irrefl 0
  rw [Coalescent.TwoLocusGenealogy.trans, ite_eq_right hd]

theorem argRateChain_rate (hθA : 0 ≤ θA) (hθB : 0 ≤ θB) (hρ : 0 ≤ ρ) (L : ASt n) :
    (argRateChain θA θB ρ hθA hθB hρ).rate L = rateTot θA θB ρ L := by
  have h2 := two_mul_rateTot (θA := θA) (θB := θB) (ρ := ρ) (L := L)
  have hQ := argRateChain_Q_self hθA hθB hρ (L := L)
  rw [RateChain.rate]
  linarith

theorem argRateChain_jumpChain_P (hθA : 0 ≤ θA) (hθB : 0 ≤ θB) (hρ : 0 ≤ ρ) (L M : ASt n)
    (hL : 0 < dtot θA θB ρ L ∨ L = (∅ : Finset (Lin n))) :
    (argRateChain θA θB ρ hθA hθB hρ).jumpChain.P L M = trans θA θB ρ L M := by
  have hrate := argRateChain_rate hθA hθB hρ L
  have h2 := two_mul_rateTot (θA := θA) (θB := θB) (ρ := ρ) (L := L)
  rcases hL with hL | hL
  · have hr : (argRateChain θA θB ρ hθA hθB hρ).rate L ≠ 0 := by
      rw [hrate]
      intro h0
      rw [h0, mul_zero] at h2
      exact hL.ne h2
    refine Eq.trans ?_ (trans_of_pos (L := L) M hL).symm
    by_cases hLM : L = M
    · subst hLM
      have h0 : (argRateChain θA θB ρ hθA hθB hρ).jumpChain.P L L = 0 := by
        simp [RateChain.jumpChain_P, RateChain.jumpMatrix, hr]
      have hs := stepU_indicator_self θA θB ρ (L := L)
      rw [h0, hs, zero_div]
    · have hQ := argRateChain_Q_of_ne hθA hθB hρ (L := L) (M := M) hLM
      rw [RateChain.jumpChain_P_of_ne hr hLM, hQ, hrate, ← h2]
      have h20 : (2 : ℝ) ≠ 0 := two_ne_zero
      field_simp
  · subst hL
    have hr : (argRateChain (n := n) θA θB ρ hθA hθB hρ).rate (∅ : Finset (Lin n)) = 0 := by
      rw [hrate]
      rw [dtot_empty] at h2
      linarith
    refine Eq.trans ?_ (trans_empty θA θB ρ M).symm
    by_cases hM : M = (∅ : Finset (Lin n))
    · subst hM
      rw [ite_eq_left rfl]
      exact RateChain.jumpChain_isAbsorbing hr
    · have hM' : (∅ : Finset (Lin n)) ≠ M := fun h => hM h.symm
      have hP : (argRateChain θA θB ρ hθA hθB hρ).jumpChain.P (∅ : Finset (Lin n)) M = 0 := by
        change RateChain.jumpMatrix _ _ _ = 0
        unfold RateChain.jumpMatrix
        rw [ite_eq_left hr]
        exact ite_eq_right hM'
      exact hP.trans (ite_eq_right hM).symm

theorem argRateChain_jumpChain_P_of_wf (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    {L : Finset (Lin n)} (hw : WF L) (M : ASt n) :
    (argRateChain θA θB ρ hθA.le hθB.le hρ).jumpChain.P L M = trans θA θB ρ L M := by
  refine argRateChain_jumpChain_P hθA.le hθB.le hρ L M ?_
  rcases L.eq_empty_or_nonempty with h | h
  · exact Or.inr h
  · exact Or.inl (dtot_pos hθA hθB hρ hw h)

end Rhone.Coalescent
