/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.MoranCannings
public import Rhone.MarkovChain.WrightFisherCanningsBridge
public import Rhone.MarkovChain.DriftHeterozygosity

/-!
# Heterozygosity decay in a neutral Cannings model

Source: cannings1974, sec. 3, p. 266; ewens2004, sec. 3.3. -/

@[expose] public section

namespace Rhone.MarkovChain.CanningsModel

open Finset

variable {N : ℕ} {Ω : Type*} [Fintype Ω]

noncomputable def offspringVariance (M : CanningsModel N Ω) (k : Fin N) : ℝ :=
  ∑ ω, M.w ω * ((M.ν ω k : ℝ) - 1) ^ 2

/-- Source: cannings1974, sec. 3, p. 266. -/
theorem offspringVariance_eq (M : CanningsModel N Ω) (k l : Fin N) :
    M.offspringVariance k = M.offspringVariance l := by
  have h := M.exchangeable (Equiv.swap k l) (fun x => ((x k : ℝ) - 1) ^ 2)
  simp only [Equiv.swap_apply_left] at h
  exact h.symm

/-- Source: cannings1974, sec. 3, p. 266. -/
theorem countChain_expect_natFun (M : CanningsModel N Ω) (g : ℕ → ℝ) (i : Fin (N + 1)) :
    M.countChain.expect (fun j => g (j : ℕ)) i = ∑ ω, M.w ω *
      g (∑ k ∈ Finset.univ.filter (fun k : Fin N => k.val < i.val), M.ν ω k) := by
  classical
  change (∑ j : Fin (N + 1), (∑ ω : Ω,
    if (∑ k ∈ Finset.univ.filter (fun k : Fin N => k.val < i.val), M.ν ω k) = j.val
    then M.w ω else 0) * g j.val) = _
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  have hle : (∑ k ∈ Finset.univ.filter (fun k : Fin N => k.val < i.val), M.ν ω k) ≤ N :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => Nat.zero_le _)).trans_eq (M.sum_ν ω)
  generalize (∑ k ∈ Finset.univ.filter (fun k : Fin N => k.val < i.val), M.ν ω k) = c at hle ⊢
  rw [Finset.sum_eq_single (⟨c, Nat.lt_succ_of_le hle⟩ : Fin (N + 1))]
  · rw [ite_eq_left rfl]
  · intro j _ hj
    have hne : ¬ c = j.val := fun h => hj (Fin.ext h.symm)
    rw [ite_eq_right hne, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Source: cannings1974, sec. 3, p. 266. -/
theorem sub_one_mul_sum_offspring_mul (M : CanningsModel N Ω) {a b : Fin N} (hab : a ≠ b) :
    ((N : ℝ) - 1) * ∑ ω, M.w ω * ((M.ν ω a : ℝ) * (M.ν ω b : ℝ)) =
      (N : ℝ) - 1 - M.offspringVariance a := by
  classical
  have hswap : ∀ c ∈ (Finset.univ : Finset (Fin N)).erase a,
      ∑ ω, M.w ω * ((M.ν ω a : ℝ) * (M.ν ω c : ℝ)) =
        ∑ ω, M.w ω * ((M.ν ω a : ℝ) * (M.ν ω b : ℝ)) := by
    intro c hc
    have hca : c ≠ a := Finset.ne_of_mem_erase hc
    have h := M.exchangeable (Equiv.swap b c) (fun x => (x a : ℝ) * (x b : ℝ))
    simp only [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hab hca.symm] at h
    exact h
  have hmean : ∑ ω, M.w ω * (M.ν ω a : ℝ) = 1 := M.expected_offspring a
  have htot : ∑ c, ∑ ω, M.w ω * ((M.ν ω a : ℝ) * (M.ν ω c : ℝ)) = N := by
    rw [Finset.sum_comm]
    have hrow : ∀ ω, ∑ c, M.w ω * ((M.ν ω a : ℝ) * (M.ν ω c : ℝ)) =
        (N : ℝ) * (M.w ω * (M.ν ω a : ℝ)) := by
      intro ω
      have hs : ∑ c, (M.ν ω c : ℝ) = N := by exact_mod_cast M.sum_ν ω
      rw [← Finset.mul_sum, ← Finset.mul_sum, hs]
      ring
    rw [Finset.sum_congr rfl fun ω _ => hrow ω, ← Finset.mul_sum, hmean, mul_one]
  have hsq : ∑ ω, M.w ω * ((M.ν ω a : ℝ) * (M.ν ω a : ℝ)) = M.offspringVariance a + 1 := by
    have hterm : ∀ ω, M.w ω * ((M.ν ω a : ℝ) * (M.ν ω a : ℝ)) =
        M.w ω * ((M.ν ω a : ℝ) - 1) ^ 2 + 2 * (M.w ω * (M.ν ω a : ℝ)) - M.w ω :=
      fun ω => by ring
    rw [Finset.sum_congr rfl fun ω _ => hterm ω, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum, hmean, M.sum_w]
    unfold offspringVariance
    ring
  have hcard : (((Finset.univ : Finset (Fin N)).erase a).card : ℝ) = (N : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub (Nat.succ_le_of_lt (Fin.pos a)), Nat.cast_one]
  have hsplit : ∑ ω, M.w ω * ((M.ν ω a : ℝ) * (M.ν ω a : ℝ)) +
      ∑ c ∈ (Finset.univ : Finset (Fin N)).erase a,
        ∑ ω, M.w ω * ((M.ν ω a : ℝ) * (M.ν ω c : ℝ)) =
      ∑ c, ∑ ω, M.w ω * ((M.ν ω a : ℝ) * (M.ν ω c : ℝ)) :=
    Finset.add_sum_erase Finset.univ
      (fun c => ∑ ω, M.w ω * ((M.ν ω a : ℝ) * (M.ν ω c : ℝ))) (Finset.mem_univ a)
  rw [htot, hsq, Finset.sum_congr rfl hswap, Finset.sum_const, nsmul_eq_mul, hcard] at hsplit
  linarith

/-- Source: cannings1974, sec. 3, p. 266; ewens2004, sec. 3.3. -/
theorem countChain_expect_hetCount (M : CanningsModel N Ω) (k : Fin N) (i : Fin (N + 1)) :
    M.countChain.expect (fun j => (j : ℝ) * ((N : ℝ) - j)) i =
      (1 - M.offspringVariance k / ((N : ℝ) - 1)) * ((i : ℝ) * ((N : ℝ) - i)) := by
  classical
  have hiN : (i : ℕ) ≤ N := Nat.le_of_lt_succ i.isLt
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin N),
      S = Finset.univ.filter (fun k : Fin N => k.val < i.val) := ⟨_, rfl⟩
  have hc : (S.card : ℝ) = i.val := by
    rw [hS, Fin.card_filter_val_lt, min_eq_right hiN]
  have hcc : (Sᶜ.card : ℝ) = (N : ℝ) - i.val := by
    rw [Finset.card_compl, Fintype.card_fin, hS, Fin.card_filter_val_lt, min_eq_right hiN,
      Nat.cast_sub hiN]
  have hcross : ∀ a ∈ S, ∀ b ∈ Sᶜ, ∑ ω, M.w ω * ((M.ν ω a : ℝ) * (M.ν ω b : ℝ)) =
      1 - M.offspringVariance k / ((N : ℝ) - 1) := by
    intro a ha b hb
    have hab : a ≠ b := fun h => (Finset.mem_compl.1 hb) (h ▸ ha)
    have h2 : 2 ≤ N := by
      have h1 := a.isLt
      have h2 := b.isLt
      have h3 : a.val ≠ b.val := Fin.val_ne_of_ne hab
      omega
    have hne : (N : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ N := by exact_mod_cast h2
      linarith
    have h := M.sub_one_mul_sum_offspring_mul hab
    rw [M.offspringVariance_eq a k] at h
    have hm : ∑ ω, M.w ω * ((M.ν ω a : ℝ) * (M.ν ω b : ℝ)) =
        ((N : ℝ) - 1 - M.offspringVariance k) / ((N : ℝ) - 1) := by
      rw [eq_div_iff hne]
      linarith
    rw [hm, sub_div, div_self hne]
  have hpoint : ∀ ω, ((∑ a ∈ S, M.ν ω a : ℕ) : ℝ) * ((N : ℝ) - (∑ a ∈ S, M.ν ω a : ℕ)) =
      ∑ a ∈ S, ∑ b ∈ Sᶜ, (M.ν ω a : ℝ) * (M.ν ω b : ℝ) := by
    intro ω
    have hsum := Finset.sum_add_sum_compl S (fun c => (M.ν ω c : ℝ))
    have hs : ∑ c, (M.ν ω c : ℝ) = N := by exact_mod_cast M.sum_ν ω
    have hX : (N : ℝ) - ∑ a ∈ S, (M.ν ω a : ℝ) = ∑ b ∈ Sᶜ, (M.ν ω b : ℝ) := by linarith
    rw [Nat.cast_sum, hX, Finset.sum_mul_sum]
  refine (M.countChain_expect_natFun (fun n => (n : ℝ) * ((N : ℝ) - n)) i).trans ?_
  rw [← hS]
  calc ∑ ω, M.w ω * (((∑ a ∈ S, M.ν ω a : ℕ) : ℝ) * ((N : ℝ) - (∑ a ∈ S, M.ν ω a : ℕ)))
      = ∑ ω, ∑ a ∈ S, ∑ b ∈ Sᶜ, M.w ω * ((M.ν ω a : ℝ) * (M.ν ω b : ℝ)) :=
        Finset.sum_congr rfl fun ω _ => by
          rw [hpoint ω, Finset.mul_sum]
          exact Finset.sum_congr rfl fun a _ => Finset.mul_sum _ _ _
    _ = ∑ a ∈ S, ∑ b ∈ Sᶜ, ∑ ω, M.w ω * ((M.ν ω a : ℝ) * (M.ν ω b : ℝ)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a ∈ S, ∑ b ∈ Sᶜ, (1 - M.offspringVariance k / ((N : ℝ) - 1)) :=
        Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => hcross a ha b hb
    _ = (1 - M.offspringVariance k / ((N : ℝ) - 1)) * ((i : ℝ) * ((N : ℝ) - i)) := by
        rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, hc, hcc]
        ring

/-- Source: cannings1974, sec. 3, p. 266; ewens2004, sec. 3.3. -/
theorem countChain_expectN_hetCount (M : CanningsModel N Ω) (k : Fin N) (t : ℕ)
    (i : Fin (N + 1)) :
    M.countChain.expectN t (fun j => (j : ℝ) * ((N : ℝ) - j)) i =
      (1 - M.offspringVariance k / ((N : ℝ) - 1)) ^ t * ((i : ℝ) * ((N : ℝ) - i)) := by
  change (M.countKernel.toFinChain M.countKernel_isStochastic).expectN t
    (fun j => (j : ℝ) * ((N : ℝ) - j)) i = _
  rw [CountKernel.toFinChain_expectN]
  exact CountKernel.expectIter_eigen M.countKernel _ _
    (fun i => M.countChain_expect_hetCount k i) t i

/-- Source: cannings1974, sec. 3, p. 266; ewens2004, sec. 3.3. -/
theorem countChain_expect_het (M : CanningsModel N Ω) (k : Fin N) (i : Fin (N + 1)) :
    M.countChain.expect (fun j => Rhone.MarkovChain.het N j) i =
      (1 - M.offspringVariance k / ((N : ℝ) - 1)) * Rhone.MarkovChain.het N i := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Fin.pos k).ne'
  have hhet : ∀ n : ℕ, Rhone.MarkovChain.het N n =
      2 / (N : ℝ) ^ 2 * ((n : ℝ) * ((N : ℝ) - n)) := fun n => by
    unfold Rhone.MarkovChain.het
    field_simp
  have h := M.countChain_expect_hetCount k i
  change M.countKernel.expect (fun j => (j : ℝ) * ((N : ℝ) - j)) i = _ at h
  change M.countKernel.expect (fun j => Rhone.MarkovChain.het N j) i = _
  simp only [hhet]
  rw [CountKernel.expect_const_mul, h]
  ring

/-- Source: cannings1974, sec. 3, p. 266. -/
theorem offspringVariance_eq_countChain_expect (M : CanningsModel N Ω) (k : Fin N) :
    M.offspringVariance k = M.countChain.expect (fun j => ((j : ℝ) - 1) ^ 2)
      ⟨1, Nat.succ_lt_succ (Fin.pos k)⟩ := by
  classical
  have hfilter : Finset.univ.filter (fun l : Fin N => l.val < 1) = {⟨0, Fin.pos k⟩} := by
    ext l
    rw [Finset.mem_filter, Finset.mem_singleton, Fin.ext_iff]
    exact ⟨fun h => Nat.lt_one_iff.1 h.2, fun h => ⟨Finset.mem_univ l, Nat.lt_one_iff.2 h⟩⟩
  refine (M.offspringVariance_eq k ⟨0, Fin.pos k⟩).trans ?_
  refine ((M.countChain_expect_natFun (fun n => ((n : ℝ) - 1) ^ 2)
    ⟨1, Nat.succ_lt_succ (Fin.pos k)⟩).trans ?_).symm
  refine Finset.sum_congr rfl fun ω _ => ?_
  change M.w ω * ((∑ l ∈ Finset.univ.filter (fun l : Fin N => l.val < 1), M.ν ω l : ℕ) - 1) ^ 2
    = _
  rw [hfilter, Finset.sum_singleton]

end Rhone.MarkovChain.CanningsModel

namespace Rhone.MarkovChain

open Finset

/-- Source: cannings1974, sec. 3.1, pp. 268–269; ewens2004, sec. 3.3. -/
theorem wfModel_offspringVariance (N : ℕ) (k : Fin N) :
    (wfModel N).offspringVariance k = 1 - 1 / (N : ℝ) := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Fin.pos k).ne'
  rw [CanningsModel.offspringVariance_eq_countChain_expect, wfModel_countChain]
  have h0 := (wf_isStochastic N).2 ⟨1, Nat.succ_lt_succ (Fin.pos k)⟩
  have h1 := wf_expect_id N ⟨1, Nat.succ_lt_succ (Fin.pos k)⟩
  have h2 := wf_expect_sq N ⟨1, Nat.succ_lt_succ (Fin.pos k)⟩
  change (wf N).expect (fun j => ((j : ℝ) - 1) ^ 2) ⟨1, Nat.succ_lt_succ (Fin.pos k)⟩ = _
  unfold CountKernel.expect at h1 h2 ⊢
  have key : ∀ j : Fin (N + 1),
      wf N ⟨1, Nat.succ_lt_succ (Fin.pos k)⟩ j * ((j : ℝ) - 1) ^ 2 =
        wf N ⟨1, Nat.succ_lt_succ (Fin.pos k)⟩ j * (j * j) -
          2 * (wf N ⟨1, Nat.succ_lt_succ (Fin.pos k)⟩ j * j) +
          wf N ⟨1, Nat.succ_lt_succ (Fin.pos k)⟩ j := fun j => by ring
  rw [Finset.sum_congr rfl fun j _ => key j, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, h0, h1, h2]
  simp only [Nat.cast_one]
  field_simp
  ring

/-- Source: moran1958; cannings1974, sec. 3.2, p. 269; ewens2004, sec. 3.3. -/
theorem moranModel_offspringVariance (N : ℕ) (hN : 0 < N) (k : Fin N) :
    (moranModel N hN).offspringVariance k = 2 * ((N : ℝ) - 1) / (N : ℝ) ^ 2 := by
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [CanningsModel.offspringVariance_eq_countChain_expect, moranModel_countChain]
  refine (moran_expect (N := N) (r := 1) (fun n : ℕ => ((n : ℝ) - 1) ^ 2)
    ⟨1, Nat.succ_lt_succ (Fin.pos k)⟩).trans ?_
  rw [moranUp_one, moranDown_one]
  simp only [Nat.cast_one, Nat.cast_ofNat, Nat.cast_zero, Nat.sub_self, Nat.reduceAdd]
  field_simp
  ring

end Rhone.MarkovChain
