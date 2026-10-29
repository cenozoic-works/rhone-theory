/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.NeutralFixationReachable
public import Rhone.MarkovChain.WrightFisherCannings

/-!
# Reachability of the boundary for the count chain of a Cannings model

Source: cannings1974, sec. 3, eq. (4)–(5), p. 266; ewens2004, secs. 3.3, 3.4. -/

@[expose] public section

namespace Rhone.MarkovChain

open Finset MeasureTheory

variable {N : ℕ} {Ω : Type*} [Fintype Ω]

theorem sum_pos_iff_exists_pos {g : Ω → ℝ} (hg : ∀ ω, 0 ≤ g ω) :
    0 < ∑ ω, g ω ↔ ∃ ω, 0 < g ω := by
  rw [Finset.sum_pos_iff_of_nonneg fun ω _ => hg ω]
  simp

theorem exists_card_eq_sum_lt (ν : Fin N → ℕ) (hsum : ∑ k, ν k = N) (h0 : ∃ k, ν k = 0)
    {m : ℕ} (hm : 0 < m) (hmN : m < N) :
    ∃ T : Finset (Fin N), T.card = m ∧ ∑ k ∈ T, ν k < m := by
  have key : ∀ d m : ℕ, m + d + 1 = N → 0 < m →
      ∃ T : Finset (Fin N), T.card = m ∧ ∑ k ∈ T, ν k < m := by
    intro d
    induction d with
    | zero =>
      intro m hmd hm
      obtain ⟨k0, hk0⟩ := h0
      have h2 : ∃ k, 2 ≤ ν k := by
        by_contra hcon
        push Not at hcon
        have hle : ∑ k ∈ univ.erase k0, ν k ≤ ∑ _k ∈ univ.erase k0, 1 :=
          Finset.sum_le_sum fun k _ => Nat.le_of_lt_succ (hcon k)
        have hsplit := Finset.add_sum_erase univ ν (mem_univ k0)
        rw [Finset.sum_const, card_erase_of_mem (mem_univ k0), card_univ, Fintype.card_fin,
          smul_eq_mul, mul_one] at hle
        omega
      obtain ⟨k1, hk1⟩ := h2
      have hsplit := Finset.add_sum_erase univ ν (mem_univ k1)
      refine ⟨univ.erase k1, ?_, ?_⟩
      · rw [card_erase_of_mem (mem_univ k1), card_univ, Fintype.card_fin]
        omega
      · omega
    | succ d ih =>
      intro m hmd hm
      obtain ⟨T, hT, hlt⟩ := ih (m + 1) (by omega) (by omega)
      by_cases h : ∃ k ∈ T, 1 ≤ ν k
      · obtain ⟨k, hk, hk1⟩ := h
        have hsplit := Finset.add_sum_erase T ν hk
        refine ⟨T.erase k, ?_, ?_⟩
        · rw [card_erase_of_mem hk, hT]
          omega
        · omega
      · push Not at h
        have hne : T.Nonempty := card_pos.1 (by omega)
        obtain ⟨k, hk⟩ := hne
        have hz : ∑ j ∈ T.erase k, ν j = 0 := Finset.sum_eq_zero fun j hj => by
          have := h j (mem_of_mem_erase hj)
          omega
        refine ⟨T.erase k, ?_, ?_⟩
        · rw [card_erase_of_mem hk, hT]
          omega
        · omega
  exact key (N - m - 1) m (by omega) hm

theorem exists_card_eq_lt_sum (ν : Fin N → ℕ) (hsum : ∑ k, ν k = N) (h0 : ∃ k, ν k = 0)
    {m : ℕ} (hm : 0 < m) (hmN : m < N) :
    ∃ T : Finset (Fin N), T.card = m ∧ m < ∑ k ∈ T, ν k := by
  obtain ⟨T, hT, hlt⟩ := exists_card_eq_sum_lt ν hsum h0 (m := N - m) (by omega) (by omega)
  have hsplit := Finset.sum_add_sum_compl T ν
  refine ⟨Tᶜ, ?_, ?_⟩
  · rw [card_compl, hT, Fintype.card_fin]
    omega
  · omega

theorem exists_perm_image_eq (S T : Finset (Fin N)) (h : T.card = S.card) :
    ∃ σ : Equiv.Perm (Fin N), T.image σ = S := by
  let e : {x // x ∈ T} ≃ {x // x ∈ S} := Finset.equivOfCardEq h
  refine ⟨e.extendSubtype, Finset.eq_of_subset_of_card_le ?_ ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    exact e.extendSubtype_mem x hx
  · rw [Finset.card_image_of_injective _ e.extendSubtype.injective, h]

def CanningsModel.NonDegenerate (M : CanningsModel N Ω) : Prop :=
  ∃ ω, 0 < M.w ω ∧ ∃ k, M.ν ω k ≠ 1

noncomputable def CanningsModel.offspringProb (M : CanningsModel N Ω) (k : Fin N) (m : ℕ) : ℝ :=
  ∑ ω, if M.ν ω k = m then M.w ω else 0

noncomputable def CanningsModel.offspringSqDeviation (M : CanningsModel N Ω) (k : Fin N) : ℝ :=
  ∑ ω, M.w ω * ((M.ν ω k : ℝ) - 1) ^ 2

theorem CanningsModel.offspringProb_eq (M : CanningsModel N Ω) (k l : Fin N) (m : ℕ) :
    CanningsModel.offspringProb M k m = CanningsModel.offspringProb M l m := by
  have h := M.exchangeable (Equiv.swap k l) (fun x => if x k = m then (1 : ℝ) else 0)
  simp only [Equiv.swap_apply_left, mul_ite, mul_one, mul_zero] at h
  exact h.symm

theorem CanningsModel.offspringProb_pos_iff (M : CanningsModel N Ω) (k : Fin N) (m : ℕ) :
    0 < CanningsModel.offspringProb M k m ↔ ∃ ω, 0 < M.w ω ∧ M.ν ω k = m := by
  have hnn : ∀ ω, 0 ≤ (if M.ν ω k = m then M.w ω else 0) := fun ω => by
    split_ifs
    · exact M.w_nonneg ω
    · exact le_rfl
  unfold CanningsModel.offspringProb
  rw [sum_pos_iff_exists_pos hnn]
  constructor
  · rintro ⟨ω, h⟩
    by_cases hm : M.ν ω k = m
    · rw [ite_eq_left hm] at h
      exact ⟨ω, h, hm⟩
    · rw [ite_eq_right hm] at h
      exact absurd h (lt_irrefl _)
  · rintro ⟨ω, hw, hm⟩
    exact ⟨ω, by rw [ite_eq_left hm]; exact hw⟩

theorem CanningsModel.nonDegenerate_iff_exists_zero (M : CanningsModel N Ω) :
    CanningsModel.NonDegenerate M ↔ ∃ ω, 0 < M.w ω ∧ ∃ k, M.ν ω k = 0 := by
  constructor
  · rintro ⟨ω, hw, k, hk⟩
    refine ⟨ω, hw, ?_⟩
    by_contra hcon
    push Not at hcon
    have hge : ∀ j, 1 ≤ M.ν ω j := fun j => Nat.pos_of_ne_zero (hcon j)
    have hsplit := Finset.add_sum_erase univ (M.ν ω) (mem_univ k)
    have hle : ∑ _j ∈ univ.erase k, 1 ≤ ∑ j ∈ univ.erase k, M.ν ω j :=
      Finset.sum_le_sum fun j _ => hge j
    rw [Finset.sum_const, card_erase_of_mem (mem_univ k), card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one] at hle
    have hs := M.sum_ν ω
    have hk1 := hge k
    omega
  · rintro ⟨ω, hw, k, hk⟩
    exact ⟨ω, hw, k, by omega⟩

theorem CanningsModel.nonDegenerate_iff_offspringProb_zero_pos (M : CanningsModel N Ω)
    (k : Fin N) :
    CanningsModel.NonDegenerate M ↔ 0 < CanningsModel.offspringProb M k 0 := by
  rw [CanningsModel.nonDegenerate_iff_exists_zero]
  constructor
  · rintro ⟨ω, hw, l, hl⟩
    rw [CanningsModel.offspringProb_eq M k l]
    exact (CanningsModel.offspringProb_pos_iff M l 0).2 ⟨ω, hw, hl⟩
  · intro h
    obtain ⟨ω, hw, hk⟩ := (CanningsModel.offspringProb_pos_iff M k 0).1 h
    exact ⟨ω, hw, k, hk⟩

theorem CanningsModel.offspringProb_zero_add_one_le (M : CanningsModel N Ω) (k : Fin N) :
    CanningsModel.offspringProb M k 0 + CanningsModel.offspringProb M k 1 ≤ 1 := by
  have h : ∑ ω, ((if M.ν ω k = 0 then M.w ω else 0) + (if M.ν ω k = 1 then M.w ω else 0)) ≤
      ∑ ω, M.w ω := Finset.sum_le_sum fun ω _ => by
    have hw := M.w_nonneg ω
    by_cases h0 : M.ν ω k = 0
    · have h1 : M.ν ω k ≠ 1 := by omega
      rw [ite_eq_left h0, ite_eq_right h1]
      linarith
    · rw [ite_eq_right h0]
      split_ifs <;> linarith
  rw [Finset.sum_add_distrib, M.sum_w] at h
  exact h

theorem CanningsModel.nonDegenerate_iff_offspringProb_one_lt_one (M : CanningsModel N Ω)
    (k : Fin N) :
    CanningsModel.NonDegenerate M ↔ CanningsModel.offspringProb M k 1 < 1 := by
  constructor
  · intro h
    have h0 := (CanningsModel.nonDegenerate_iff_offspringProb_zero_pos M k).1 h
    have hle := CanningsModel.offspringProb_zero_add_one_le M k
    linarith
  · intro h
    by_contra hcon
    have hone : CanningsModel.offspringProb M k 1 = 1 := by
      refine (Finset.sum_congr rfl fun ω _ => ?_).trans M.sum_w
      by_cases h1 : M.ν ω k = 1
      · rw [ite_eq_left h1]
      · rw [ite_eq_right h1]
        have hw : ¬ 0 < M.w ω := fun hw => hcon ⟨ω, hw, k, h1⟩
        linarith [M.w_nonneg ω]
    linarith

theorem CanningsModel.offspringSqDeviation_eq (M : CanningsModel N Ω) (k : Fin N) :
    CanningsModel.offspringSqDeviation M k = ∑ ω, M.w ω * (M.ν ω k : ℝ) ^ 2 - 1 := by
  have h1 : ∑ ω, M.w ω * (M.ν ω k : ℝ) = 1 := M.expected_offspring k
  have hterm : ∀ ω, M.w ω * ((M.ν ω k : ℝ) - 1) ^ 2 =
      M.w ω * (M.ν ω k : ℝ) ^ 2 - 2 * (M.w ω * (M.ν ω k : ℝ)) + M.w ω := fun ω => by ring
  unfold CanningsModel.offspringSqDeviation
  rw [Finset.sum_congr rfl (fun ω _ => hterm ω), Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, h1, M.sum_w]
  ring

theorem CanningsModel.nonDegenerate_iff_offspringVariance_pos (M : CanningsModel N Ω)
    (k : Fin N) :
    CanningsModel.NonDegenerate M ↔ 0 < CanningsModel.offspringSqDeviation M k := by
  have hnn : ∀ ω, 0 ≤ M.w ω * ((M.ν ω k : ℝ) - 1) ^ 2 := fun ω =>
    mul_nonneg (M.w_nonneg ω) (sq_nonneg _)
  unfold CanningsModel.offspringSqDeviation
  rw [sum_pos_iff_exists_pos hnn]
  constructor
  · intro h
    obtain ⟨ω, hw, hk⟩ := (CanningsModel.offspringProb_pos_iff M k 0).1
      ((CanningsModel.nonDegenerate_iff_offspringProb_zero_pos M k).1 h)
    refine ⟨ω, ?_⟩
    rw [hk]
    simpa using hw
  · rintro ⟨ω, hω⟩
    have hw : 0 < M.w ω := by
      rcases (M.w_nonneg ω).lt_or_eq with h | h
      · exact h
      · rw [← h, zero_mul] at hω
        exact absurd hω (lt_irrefl _)
    refine ⟨ω, hw, k, fun h1 => ?_⟩
    rw [h1] at hω
    simp at hω

theorem CanningsModel.countChain_P_apply (M : CanningsModel N Ω) (i j : Fin (N + 1)) :
    M.countChain.P i j = ∑ ω, if (∑ k ∈ Finset.univ.filter (fun k : Fin N => k.val < i.val),
      M.ν ω k) = j.val then M.w ω else 0 := rfl

theorem CanningsModel.sum_subset_law_eq (M : CanningsModel N Ω) (S T : Finset (Fin N))
    (h : S.card = T.card) (g : ℕ → ℝ) :
    ∑ ω, M.w ω * g (∑ k ∈ S, M.ν ω k) = ∑ ω, M.w ω * g (∑ k ∈ T, M.ν ω k) := by
  obtain ⟨σ, hσ⟩ := exists_perm_image_eq T S h
  have hex := M.exchangeable σ (fun x => g (∑ k ∈ S, x k))
  have hsum : ∀ ω, ∑ k ∈ S, M.ν ω (σ k) = ∑ k ∈ T, M.ν ω k := fun ω => by
    rw [← hσ, Finset.sum_image (fun a _ b _ hab => σ.injective hab)]
  simp only [hsum] at hex
  exact hex.symm

theorem CanningsModel.countChain_P_pos_of_subset (M : CanningsModel N Ω) {i j : Fin (N + 1)}
    {ω₀ : Ω} (hw₀ : 0 < M.w ω₀) {T : Finset (Fin N)} (hT : T.card = i.val)
    (hj : ∑ k ∈ T, M.ν ω₀ k = j.val) : 0 < M.countChain.P i j := by
  obtain ⟨I, hI⟩ : ∃ I : Finset (Fin N),
      I = Finset.univ.filter (fun k : Fin N => k.val < i.val) := ⟨_, rfl⟩
  have hc : I.card = i.val := by
    rw [hI, Fin.card_filter_val_lt, min_eq_right (Nat.le_of_lt_succ i.isLt)]
  have hlaw : ∑ ω, M.w ω * (if ∑ k ∈ I, M.ν ω k = j.val then (1 : ℝ) else 0) =
      ∑ ω, M.w ω * (if ∑ k ∈ T, M.ν ω k = j.val then (1 : ℝ) else 0) :=
    CanningsModel.sum_subset_law_eq M I T (hc.trans hT.symm)
      (fun s => if s = j.val then (1 : ℝ) else 0)
  have hterm : ∀ ω, (if ∑ k ∈ I, M.ν ω k = j.val then M.w ω else 0) =
      M.w ω * (if ∑ k ∈ I, M.ν ω k = j.val then (1 : ℝ) else 0) := fun ω => by
    split_ifs <;> simp
  have hnn : ∀ ω, 0 ≤ M.w ω * (if ∑ k ∈ T, M.ν ω k = j.val then (1 : ℝ) else 0) := fun ω =>
    mul_nonneg (M.w_nonneg ω) (by split_ifs <;> norm_num)
  rw [CanningsModel.countChain_P_apply, ← hI, Finset.sum_congr rfl (fun ω _ => hterm ω), hlaw,
    sum_pos_iff_exists_pos hnn]
  refine ⟨ω₀, ?_⟩
  rw [ite_eq_left hj, mul_one]
  exact hw₀

theorem CanningsModel.countChain_exists_lt (M : CanningsModel N Ω)
    (hM : CanningsModel.NonDegenerate M) {i : Fin (N + 1)} (hi0 : 0 < i.val)
    (hiN : i.val < N) :
    ∃ j : Fin (N + 1), j.val < i.val ∧ 0 < M.countChain.P i j := by
  obtain ⟨ω₀, hw₀, hz⟩ := (CanningsModel.nonDegenerate_iff_exists_zero M).1 hM
  obtain ⟨T, hT, hlt⟩ := exists_card_eq_sum_lt (M.ν ω₀) (M.sum_ν ω₀) hz hi0 hiN
  exact ⟨⟨∑ k ∈ T, M.ν ω₀ k, by omega⟩, hlt,
    CanningsModel.countChain_P_pos_of_subset M hw₀ hT rfl⟩

theorem CanningsModel.countChain_exists_gt (M : CanningsModel N Ω)
    (hM : CanningsModel.NonDegenerate M) {i : Fin (N + 1)} (hi0 : 0 < i.val)
    (hiN : i.val < N) :
    ∃ j : Fin (N + 1), i.val < j.val ∧ 0 < M.countChain.P i j := by
  obtain ⟨ω₀, hw₀, hz⟩ := (CanningsModel.nonDegenerate_iff_exists_zero M).1 hM
  obtain ⟨T, hT, hlt⟩ := exists_card_eq_lt_sum (M.ν ω₀) (M.sum_ν ω₀) hz hi0 hiN
  have hle : ∑ k ∈ T, M.ν ω₀ k ≤ N :=
    (Finset.sum_le_sum_of_subset (Finset.subset_univ T)).trans_eq (M.sum_ν ω₀)
  exact ⟨⟨∑ k ∈ T, M.ν ω₀ k, by omega⟩, hlt,
    CanningsModel.countChain_P_pos_of_subset M hw₀ hT rfl⟩

theorem CanningsModel.countChain_reaches (M : CanningsModel N Ω)
    (hM : CanningsModel.NonDegenerate M) : M.countChain.Reaches (fixationBoundary N) :=
  FinChain.reaches_of_rank _ _ (fun i => (i : ℕ)) fun i hi => by
    obtain ⟨h0, hlt⟩ := pos_and_lt_of_notMem_fixationBoundary hi
    obtain ⟨j, hj, hpos⟩ := CanningsModel.countChain_exists_lt M hM h0 hlt
    exact ⟨j, hpos, hj⟩

theorem CanningsModel.countChain_eq_frozenChain (M : CanningsModel N Ω)
    (hM : ¬ CanningsModel.NonDegenerate M) : M.countChain = frozenChain N := by
  apply finChain_eq_of_P_eq
  funext i j
  have hc : (Finset.univ.filter (fun k : Fin N => k.val < i.val)).card = i.val := by
    rw [Fin.card_filter_val_lt, min_eq_right (Nat.le_of_lt_succ i.isLt)]
  have hterm : ∀ ω, (if (∑ k ∈ Finset.univ.filter (fun k : Fin N => k.val < i.val),
      M.ν ω k) = j.val then M.w ω else 0) = if i = j then M.w ω else 0 := by
    intro ω
    by_cases hw : 0 < M.w ω
    · have hone : ∀ k, M.ν ω k = 1 := fun k => by
        by_contra hk
        exact hM ⟨ω, hw, k, hk⟩
      have hs : ∑ k ∈ Finset.univ.filter (fun k : Fin N => k.val < i.val), M.ν ω k = i.val := by
        rw [Finset.sum_congr rfl (fun k _ => hone k), Finset.sum_const, hc, smul_eq_mul,
          mul_one]
      rw [hs]
      simp [Fin.ext_iff]
    · have hw0 : M.w ω = 0 := le_antisymm (not_lt.1 hw) (M.w_nonneg ω)
      rw [hw0]
      simp
  have hRhs : (frozenChain N).P i j = if i = j then 1 else 0 := Matrix.one_apply
  rw [CanningsModel.countChain_P_apply, hRhs, Finset.sum_congr rfl (fun ω _ => hterm ω)]
  by_cases hij : i = j
  · simp [hij, M.sum_w]
  · simp [hij]

theorem CanningsModel.countChain_reaches_iff (M : CanningsModel N Ω) (hN : 2 ≤ N) :
    M.countChain.Reaches (fixationBoundary N) ↔ CanningsModel.NonDegenerate M := by
  constructor
  · intro hR
    by_contra hM
    rw [CanningsModel.countChain_eq_frozenChain M hM] at hR
    exact frozenChain_not_reaches hN hR
  · exact CanningsModel.countChain_reaches M

theorem CanningsModel.not_nonDegenerate_of_le_one (M : CanningsModel N Ω) (hN : N ≤ 1) :
    ¬ CanningsModel.NonDegenerate M := by
  intro h
  obtain ⟨ω, -, k, hk⟩ := (CanningsModel.nonDegenerate_iff_exists_zero M).1 h
  have hsplit := Finset.add_sum_erase univ (M.ν ω) (mem_univ k)
  have hcard : (univ.erase k).card = N - 1 := by
    rw [card_erase_of_mem (mem_univ k), card_univ, Fintype.card_fin]
  have hempty : univ.erase k = ∅ := Finset.card_eq_zero.1 (by omega)
  rw [hempty, Finset.sum_empty, M.sum_ν ω] at hsplit
  have hpos := Fin.pos k
  omega

theorem CanningsModel.countChain_reaches_of_le_one (M : CanningsModel N Ω) (hN : N ≤ 1) :
    M.countChain.Reaches (fixationBoundary N) := by
  intro x
  have hx : x ∈ fixationBoundary N := by
    rw [mem_fixationBoundary]
    by_cases h : x.val = 0
    · exact Or.inl (Fin.ext h)
    · refine Or.inr (Fin.ext ?_)
      have hlt := x.isLt
      rw [Fin.val_last]
      omega
  refine ⟨0, x, hx, ?_⟩
  rw [FinChain.stepN_zero]
  simp

theorem CanningsModel.fixation_real_of_nonDegenerate (hN : 0 < N) (M : CanningsModel N Ω)
    (hM : CanningsModel.NonDegenerate M) (i : Fin (N + 1)) :
    (M.countChain.pathLaw i).real {ω | ∃ n, ω n = Fin.last N} = (i : ℝ) / N :=
  CanningsModel.fixation_real_of_reaches hN M (CanningsModel.countChain_reaches M hM) i

theorem CanningsModel.fixation_real_of_offspringProb_zero_pos (hN : 0 < N)
    (M : CanningsModel N Ω) (k : Fin N) (hk : 0 < CanningsModel.offspringProb M k 0)
    (i : Fin (N + 1)) :
    (M.countChain.pathLaw i).real {ω | ∃ n, ω n = Fin.last N} = (i : ℝ) / N :=
  CanningsModel.fixation_real_of_nonDegenerate hN M
    ((CanningsModel.nonDegenerate_iff_offspringProb_zero_pos M k).2 hk) i

theorem CanningsModel.fixation_real_eventually_of_nonDegenerate (hN : 0 < N)
    (M : CanningsModel N Ω) (hM : CanningsModel.NonDegenerate M) (i : Fin (N + 1)) :
    (M.countChain.pathLaw i).real {ω | ∃ n, ∀ m, n ≤ m → ω m = Fin.last N} = (i : ℝ) / N :=
  fixation_real_eventually_of_martingale hN M.countChain M.countChain_expect_count
    (CanningsModel.countChain_reaches M hM) i

theorem CanningsModel.loss_real_of_nonDegenerate (hN : 0 < N) (M : CanningsModel N Ω)
    (hM : CanningsModel.NonDegenerate M) (i : Fin (N + 1)) :
    (M.countChain.pathLaw i).real {ω | ∃ n, ω n = 0} = 1 - (i : ℝ) / N :=
  loss_real_of_martingale hN M.countChain M.countChain_expect_count
    (CanningsModel.countChain_reaches M hM) i

theorem CanningsModel.fixation_real_of_not_nonDegenerate (M : CanningsModel N Ω)
    (hM : ¬ CanningsModel.NonDegenerate M) {i : Fin (N + 1)} (hi : i ≠ Fin.last N) :
    (M.countChain.pathLaw i).real {ω | ∃ n, ω n = Fin.last N} = 0 := by
  rw [CanningsModel.countChain_eq_frozenChain M hM]
  exact frozenChain_fixation_real N hi

theorem wfModel_nonDegenerate (hN : 2 ≤ N) : CanningsModel.NonDegenerate (wfModel N) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  refine (CanningsModel.nonDegenerate_iff_exists_zero _).2
    ⟨fun _ => ⟨0, by omega⟩, ?_, ⟨1, by omega⟩, ?_⟩
  · rw [wfModel_weight]
    exact one_div_pos.2 (pow_pos hNpos N)
  · rw [wfModel_offspring, wfOffspring, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro t _ h
    have hval := congrArg Fin.val h
    simp at hval

theorem moranModel_nonDegenerate (hN : 2 ≤ N) (h : 0 < N) :
    CanningsModel.NonDegenerate (moranModel N h) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast h
  refine (CanningsModel.nonDegenerate_iff_exists_zero _).2
    ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), ?_, ⟨1, by omega⟩, ?_⟩
  · change 0 < 1 / (N : ℝ) ^ 2
    exact one_div_pos.2 (pow_pos hNpos 2)
  · change moranOffspring N _ _ = 0
    simp [moranOffspring, Fin.ext_iff]

theorem moranModel_fixation_real (hN : 2 ≤ N) (h : 0 < N) (i : Fin (N + 1)) :
    ((moranModel N h).countChain.pathLaw i).real {ω | ∃ n, ω n = Fin.last N} = (i : ℝ) / N :=
  CanningsModel.fixation_real_of_nonDegenerate h _ (moranModel_nonDegenerate hN h) i

end Rhone.MarkovChain
