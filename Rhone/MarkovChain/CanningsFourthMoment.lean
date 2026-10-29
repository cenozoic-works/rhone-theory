/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.CanningsHeterozygosity

/-! # Second and fourth moments of the one-step change of a Cannings count chain -/

@[expose] public section

namespace Rhone.MarkovChain.CanningsModel

open Finset

variable {N : ℕ} {Ω : Type*} [Fintype Ω]

noncomputable def meanOf (M : CanningsModel N Ω) (g : (Fin N → ℕ) → ℝ) : ℝ :=
  ∑ ω, M.w ω * g (M.ν ω)

theorem meanOf_congr (M : CanningsModel N Ω) {g h : (Fin N → ℕ) → ℝ}
    (hgh : ∀ ω, g (M.ν ω) = h (M.ν ω)) : M.meanOf g = M.meanOf h :=
  Finset.sum_congr rfl fun ω _ => by rw [hgh ω]

theorem meanOf_mono (M : CanningsModel N Ω) {g h : (Fin N → ℕ) → ℝ}
    (hgh : ∀ ω, g (M.ν ω) ≤ h (M.ν ω)) : M.meanOf g ≤ M.meanOf h :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hgh ω) (M.w_nonneg ω)

theorem meanOf_nonneg (M : CanningsModel N Ω) {g : (Fin N → ℕ) → ℝ}
    (hg : ∀ ω, 0 ≤ g (M.ν ω)) : 0 ≤ M.meanOf g :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (M.w_nonneg ω) (hg ω)

theorem meanOf_add (M : CanningsModel N Ω) (g h : (Fin N → ℕ) → ℝ) :
    M.meanOf (fun x => g x + h x) = M.meanOf g + M.meanOf h := by
  simp only [meanOf, mul_add, Finset.sum_add_distrib]

theorem meanOf_const_mul (M : CanningsModel N Ω) (c : ℝ) (g : (Fin N → ℕ) → ℝ) :
    M.meanOf (fun x => c * g x) = c * M.meanOf g := by
  simp only [meanOf, Finset.mul_sum]
  exact Finset.sum_congr rfl fun ω _ => by ring

theorem meanOf_neg (M : CanningsModel N Ω) (g : (Fin N → ℕ) → ℝ) :
    M.meanOf (fun x => -g x) = -M.meanOf g := by
  simp only [meanOf, mul_neg, Finset.sum_neg_distrib]

theorem meanOf_sum (M : CanningsModel N Ω) {ι : Type*} (s : Finset ι)
    (g : ι → (Fin N → ℕ) → ℝ) :
    M.meanOf (fun x => ∑ j ∈ s, g j x) = ∑ j ∈ s, M.meanOf (g j) := by
  simp only [meanOf, Finset.mul_sum]
  exact Finset.sum_comm

theorem meanOf_perm (M : CanningsModel N Ω) (σ : Equiv.Perm (Fin N))
    (g : (Fin N → ℕ) → ℝ) : M.meanOf (fun x => g (x ∘ σ)) = M.meanOf g :=
  M.exchangeable σ g

def dev (x : Fin N → ℕ) (j : Fin N) : ℝ := (x j : ℝ) - 1

theorem sum_dev (M : CanningsModel N Ω) (ω : Ω) : ∑ j, dev (M.ν ω) j = 0 := by
  have hs : ∑ c, (M.ν ω c : ℝ) = N := by exact_mod_cast M.sum_ν ω
  simp only [dev, Finset.sum_sub_distrib, hs, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, sub_self]

theorem abs_dev_le (M : CanningsModel N Ω) (ω : Ω) (b : Fin N) : |dev (M.ν ω) b| ≤ N := by
  have h1 : (M.ν ω b : ℝ) ≤ N := by
    have h := Finset.single_le_sum (f := fun c => M.ν ω c) (fun c _ => Nat.zero_le _)
      (Finset.mem_univ b)
    rw [M.sum_ν ω] at h
    exact_mod_cast h
  have h0 : (0 : ℝ) ≤ (M.ν ω b : ℝ) := Nat.cast_nonneg _
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Fin.pos b
  rw [dev, abs_le]
  constructor <;> linarith

theorem sum_abs_dev_le (M : CanningsModel N Ω) (ω : Ω) : ∑ j, |dev (M.ν ω) j| ≤ 2 * N := by
  have hs : ∑ c, (M.ν ω c : ℝ) = N := by exact_mod_cast M.sum_ν ω
  have hle : ∀ j ∈ (Finset.univ : Finset (Fin N)), |dev (M.ν ω) j| ≤ (M.ν ω j : ℝ) + 1 := by
    intro j _
    have h0 : (0 : ℝ) ≤ (M.ν ω j : ℝ) := Nat.cast_nonneg _
    rw [dev, abs_le]
    constructor <;> linarith
  refine (Finset.sum_le_sum hle).trans_eq ?_
  rw [Finset.sum_add_distrib, hs, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  ring

noncomputable def offspringAbsThirdMoment (M : CanningsModel N Ω) (k : Fin N) : ℝ :=
  ∑ ω, M.w ω * |(M.ν ω k : ℝ) - 1| ^ 3

theorem offspringAbsThirdMoment_eq (M : CanningsModel N Ω) (k l : Fin N) :
    M.offspringAbsThirdMoment k = M.offspringAbsThirdMoment l := by
  have h := M.exchangeable (Equiv.swap k l) (fun x => |(x k : ℝ) - 1| ^ 3)
  simp only [Equiv.swap_apply_left] at h
  exact h.symm

theorem offspringAbsThirdMoment_nonneg (M : CanningsModel N Ω) (k : Fin N) :
    0 ≤ M.offspringAbsThirdMoment k :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (M.w_nonneg ω) (by positivity)

theorem offspringVariance_le_offspringAbsThirdMoment (M : CanningsModel N Ω) (k : Fin N) :
    M.offspringVariance k ≤ M.offspringAbsThirdMoment k := by
  refine Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (M.w_nonneg ω)
  have hint : (M.ν ω k : ℝ) - 1 = ((M.ν ω k : ℤ) - 1 : ℤ) := by push_cast; ring
  rw [hint, ← sq_abs]
  obtain ⟨z, hz⟩ : ∃ z : ℤ, z = (M.ν ω k : ℤ) - 1 := ⟨_, rfl⟩
  rw [← hz, ← Int.cast_abs]
  rcases eq_or_ne z 0 with h0 | h0
  · simp [h0]
  · have h1 : (1 : ℝ) ≤ ((|z| : ℤ) : ℝ) := by exact_mod_cast Int.one_le_abs h0
    nlinarith [sq_nonneg ((|z| : ℤ) : ℝ)]

noncomputable def offspringThirdFactorialMoment (M : CanningsModel N Ω) (k : Fin N) : ℝ :=
  ∑ ω, M.w ω * ((M.ν ω k : ℝ) * ((M.ν ω k : ℝ) - 1) * ((M.ν ω k : ℝ) - 2))

theorem abs_natCast_sub_one_pow_three_le (v : ℕ) :
    |(v : ℝ) - 1| ^ 3 ≤
      ((v : ℝ) - 1) ^ 2 + 4 / 3 * ((v : ℝ) * ((v : ℝ) - 1) * ((v : ℝ) - 2)) := by
  rcases v with _ | _ | _ | w
  · norm_num
  · norm_num
  · norm_num
  · have hw : (0 : ℝ) ≤ (w : ℝ) := Nat.cast_nonneg w
    have e : ((w + 1 + 1 + 1 : ℕ) : ℝ) - 1 = (w : ℝ) + 2 := by
      push_cast
      ring
    rw [e, abs_of_nonneg (by linarith)]
    push_cast
    nlinarith [mul_nonneg hw hw, mul_nonneg (mul_nonneg hw hw) hw]

theorem offspringAbsThirdMoment_le (M : CanningsModel N Ω) (k : Fin N) :
    M.offspringAbsThirdMoment k ≤
      M.offspringVariance k + 4 / 3 * M.offspringThirdFactorialMoment k := by
  unfold offspringAbsThirdMoment offspringVariance offspringThirdFactorialMoment
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun ω _ => ?_
  have h := mul_le_mul_of_nonneg_left (abs_natCast_sub_one_pow_three_le (M.ν ω k))
    (M.w_nonneg ω)
  refine h.trans_eq ?_
  ring

theorem two_le_of_offspringVariance_pos (M : CanningsModel N Ω) (k : Fin N)
    (hvar : 0 < M.offspringVariance k) : 2 ≤ N := by
  by_contra h
  have h1 : N = 1 := by
    have := Fin.pos k
    omega
  subst h1
  have hzero : M.offspringVariance k = 0 := by
    refine Finset.sum_eq_zero fun ω _ => ?_
    have h0 := M.sum_dev ω
    rw [Fin.sum_univ_one, Subsingleton.elim (0 : Fin 1) k] at h0
    have h0' : (M.ν ω k : ℝ) - 1 = 0 := h0
    rw [h0']
    simp
  linarith

theorem meanOf_sum_dev_cube_mul_dev_nonpos (M : CanningsModel N Ω) {S : Finset (Fin N)}
    {b : Fin N} (hb : b ∉ S) :
    M.meanOf (fun x => (∑ j ∈ S, dev x j) ^ 3 * dev x b) ≤ 0 := by
  classical
  have heq : ∀ c ∈ Sᶜ, M.meanOf (fun x => (∑ j ∈ S, dev x j) ^ 3 * dev x c) =
      M.meanOf (fun x => (∑ j ∈ S, dev x j) ^ 3 * dev x b) := by
    intro c hc
    have hcS : c ∉ S := Finset.mem_compl.1 hc
    have h := M.meanOf_perm (Equiv.swap b c) (fun x => (∑ j ∈ S, dev x j) ^ 3 * dev x b)
    rw [← h]
    refine congrArg M.meanOf (funext fun x => ?_)
    have hsum : ∑ j ∈ S, dev (x ∘ Equiv.swap b c) j = ∑ j ∈ S, dev x j :=
      Finset.sum_congr rfl fun j hj => by
        have hjb : j ≠ b := fun h => hb (h ▸ hj)
        have hjc : j ≠ c := fun h => hcS (h ▸ hj)
        simp [dev, Equiv.swap_apply_of_ne_of_ne hjb hjc]
    rw [hsum]
    simp [dev]
  have hsum : ∑ c ∈ Sᶜ, M.meanOf (fun x => (∑ j ∈ S, dev x j) ^ 3 * dev x c) =
      -M.meanOf (fun x => (∑ j ∈ S, dev x j) ^ 4) := by
    rw [← M.meanOf_neg]
    refine (M.meanOf_sum Sᶜ (fun c x => (∑ j ∈ S, dev x j) ^ 3 * dev x c)).symm.trans ?_
    refine M.meanOf_congr fun ω => ?_
    have h0 := M.sum_dev ω
    rw [← Finset.sum_add_sum_compl S] at h0
    have hc : ∑ c ∈ Sᶜ, dev (M.ν ω) c = -∑ j ∈ S, dev (M.ν ω) j := by linarith
    rw [← Finset.mul_sum, hc]
    ring
  rw [Finset.sum_congr rfl heq, Finset.sum_const, nsmul_eq_mul] at hsum
  have hpos : (0 : ℝ) < (Sᶜ.card : ℝ) := by
    exact_mod_cast Finset.card_pos.2 ⟨b, Finset.mem_compl.2 hb⟩
  have h4 : 0 ≤ M.meanOf (fun x => (∑ j ∈ S, dev x j) ^ 4) :=
    M.meanOf_nonneg fun ω => by positivity
  by_contra hcon
  have := mul_pos hpos (not_le.1 hcon)
  linarith

theorem sub_one_mul_meanOf_dev_mul_cube (M : CanningsModel N Ω) {j b : Fin N} (hjb : j ≠ b) :
    ((N : ℝ) - 1) * M.meanOf (fun x => dev x j * dev x b ^ 3) =
      -M.meanOf (fun x => dev x b ^ 4) := by
  classical
  have heq : ∀ c ∈ (Finset.univ : Finset (Fin N)).erase b,
      M.meanOf (fun x => dev x c * dev x b ^ 3) =
        M.meanOf (fun x => dev x j * dev x b ^ 3) := by
    intro c hc
    have hcb : c ≠ b := Finset.ne_of_mem_erase hc
    have h := M.meanOf_perm (Equiv.swap j c) (fun x => dev x j * dev x b ^ 3)
    rw [← h]
    refine congrArg M.meanOf (funext fun x => ?_)
    simp [dev, Equiv.swap_apply_of_ne_of_ne hjb.symm hcb.symm]
  have hsum : ∑ c ∈ (Finset.univ : Finset (Fin N)).erase b,
      M.meanOf (fun x => dev x c * dev x b ^ 3) = -M.meanOf (fun x => dev x b ^ 4) := by
    rw [← M.meanOf_neg]
    refine (M.meanOf_sum _ (fun c x => dev x c * dev x b ^ 3)).symm.trans ?_
    refine M.meanOf_congr fun ω => ?_
    have h0 := M.sum_dev ω
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b)] at h0
    have hc : ∑ c ∈ (Finset.univ : Finset (Fin N)).erase b, dev (M.ν ω) c =
        -dev (M.ν ω) b := by linarith
    rw [← Finset.sum_mul, hc]
    ring
  have hcard : (((Finset.univ : Finset (Fin N)).erase b).card : ℝ) = (N : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ b), Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub (Nat.succ_le_of_lt (Fin.pos b)), Nat.cast_one]
  rw [Finset.sum_congr rfl heq, Finset.sum_const, nsmul_eq_mul, hcard] at hsum
  exact hsum

theorem sub_two_mul_meanOf_dev_mul_dev_mul_sq (M : CanningsModel N Ω) {j l b : Fin N}
    (hjl : j ≠ l) (hjb : j ≠ b) (hlb : l ≠ b) :
    ((N : ℝ) - 2) * M.meanOf (fun x => dev x j * dev x l * dev x b ^ 2) =
      -M.meanOf (fun x => dev x j ^ 2 * dev x b ^ 2) -
        M.meanOf (fun x => dev x j * dev x b ^ 3) := by
  classical
  obtain ⟨T, hT⟩ : ∃ T : Finset (Fin N), T = ((Finset.univ : Finset (Fin N)).erase b).erase j :=
    ⟨_, rfl⟩
  have hjmem : j ∈ (Finset.univ : Finset (Fin N)).erase b :=
    Finset.mem_erase.2 ⟨hjb, Finset.mem_univ j⟩
  have heq : ∀ c ∈ T, M.meanOf (fun x => dev x j * dev x c * dev x b ^ 2) =
      M.meanOf (fun x => dev x j * dev x l * dev x b ^ 2) := by
    intro c hc
    rw [hT] at hc
    have hcj : c ≠ j := Finset.ne_of_mem_erase hc
    have hcb : c ≠ b := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hc)
    have h := M.meanOf_perm (Equiv.swap l c) (fun x => dev x j * dev x l * dev x b ^ 2)
    rw [← h]
    refine congrArg M.meanOf (funext fun x => ?_)
    simp [dev, Equiv.swap_apply_of_ne_of_ne hjl hcj.symm,
      Equiv.swap_apply_of_ne_of_ne hlb.symm hcb.symm]
  have hsum : ∑ c ∈ T, M.meanOf (fun x => dev x j * dev x c * dev x b ^ 2) =
      -M.meanOf (fun x => dev x j ^ 2 * dev x b ^ 2) -
        M.meanOf (fun x => dev x j * dev x b ^ 3) := by
    have e : M.meanOf (fun x => ∑ c ∈ T, dev x j * dev x c * dev x b ^ 2) =
        M.meanOf (fun x => -(dev x j ^ 2 * dev x b ^ 2) + -(dev x j * dev x b ^ 3)) := by
      refine M.meanOf_congr fun ω => ?_
      have h0 := M.sum_dev ω
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b),
        ← Finset.add_sum_erase _ _ hjmem, ← hT] at h0
      have hc : ∑ c ∈ T, dev (M.ν ω) c = -dev (M.ν ω) j - dev (M.ν ω) b := by linarith
      have hfac : ∑ c ∈ T, dev (M.ν ω) j * dev (M.ν ω) c * dev (M.ν ω) b ^ 2 =
          dev (M.ν ω) j * (∑ c ∈ T, dev (M.ν ω) c) * dev (M.ν ω) b ^ 2 := by
        rw [Finset.mul_sum, Finset.sum_mul]
      rw [hfac, hc]
      ring
    rw [← M.meanOf_sum T (fun c x => dev x j * dev x c * dev x b ^ 2), e, M.meanOf_add,
      M.meanOf_neg, M.meanOf_neg]
    ring
  have h2 : 2 ≤ N := by
    have h1 := j.isLt
    have h2 := b.isLt
    have h3 : j.val ≠ b.val := Fin.val_ne_of_ne hjb
    omega
  have hcard : (T.card : ℝ) = (N : ℝ) - 2 := by
    rw [hT, Finset.card_erase_of_mem hjmem, Finset.card_erase_of_mem (Finset.mem_univ b),
      Finset.card_univ, Fintype.card_fin, show N - 1 - 1 = N - 2 by omega, Nat.cast_sub h2]
    norm_num
  rw [Finset.sum_congr rfl heq, Finset.sum_const, nsmul_eq_mul, hcard] at hsum
  exact hsum

theorem sub_one_mul_sub_two_mul_meanOf_le (M : CanningsModel N Ω) {j l b : Fin N}
    (hjl : j ≠ l) (hjb : j ≠ b) (hlb : l ≠ b) :
    ((N : ℝ) - 1) * ((N : ℝ) - 2) * M.meanOf (fun x => dev x j * dev x l * dev x b ^ 2) ≤
      M.meanOf (fun x => dev x b ^ 4) := by
  have h3 := M.sub_two_mul_meanOf_dev_mul_dev_mul_sq hjl hjb hlb
  have h2 := M.sub_one_mul_meanOf_dev_mul_cube hjb
  have hq : 0 ≤ M.meanOf (fun x => dev x j ^ 2 * dev x b ^ 2) :=
    M.meanOf_nonneg fun ω => by positivity
  have hN1 : (0 : ℝ) ≤ (N : ℝ) - 1 := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast Fin.pos b
    linarith
  have e : ((N : ℝ) - 1) * ((N : ℝ) - 2) *
      M.meanOf (fun x => dev x j * dev x l * dev x b ^ 2) =
      ((N : ℝ) - 1) * (-M.meanOf (fun x => dev x j ^ 2 * dev x b ^ 2) -
        M.meanOf (fun x => dev x j * dev x b ^ 3)) := by
    rw [mul_assoc, h3]
  have hprod := mul_nonneg hN1 hq
  rw [e]
  linarith

theorem sq_mul_sq_le_abs (a b : ℝ) : a ^ 2 * b ^ 2 ≤ |b| ^ 3 * |a| + |b| * |a| ^ 3 := by
  rw [← sq_abs a, ← sq_abs b]
  have hu := abs_nonneg a
  have hv := abs_nonneg b
  nlinarith [mul_nonneg (mul_nonneg hu hv) (sq_nonneg (|a| - |b|)),
    mul_nonneg (mul_nonneg hu hv) (mul_nonneg hu hv)]

theorem meanOf_abs_dev_mul_sum_cube_le (M : CanningsModel N Ω) (k b : Fin N) :
    M.meanOf (fun x => |dev x b| * ∑ j, |dev x j| ^ 3) ≤
      2 * N * M.offspringAbsThirdMoment k := by
  classical
  have hN : (0 : ℝ) < N := by exact_mod_cast Fin.pos b
  have heq : ∀ c ∈ (Finset.univ : Finset (Fin N)),
      M.meanOf (fun x => |dev x c| * ∑ j, |dev x j| ^ 3) =
        M.meanOf (fun x => |dev x b| * ∑ j, |dev x j| ^ 3) := by
    intro c _
    have h := M.meanOf_perm (Equiv.swap b c) (fun x => |dev x b| * ∑ j, |dev x j| ^ 3)
    rw [← h]
    refine congrArg M.meanOf (funext fun x => ?_)
    have hsum : ∑ j, |dev (x ∘ Equiv.swap b c) j| ^ 3 = ∑ j, |dev x j| ^ 3 :=
      Equiv.sum_comp (Equiv.swap b c) (fun j => |dev x j| ^ 3)
    rw [hsum]
    simp [dev]
  have hG : M.meanOf (fun x => ∑ j, |dev x j| ^ 3) = N * M.offspringAbsThirdMoment k := by
    rw [M.meanOf_sum]
    have hj : ∀ j ∈ (Finset.univ : Finset (Fin N)), M.meanOf (fun x => |dev x j| ^ 3) =
        M.offspringAbsThirdMoment k := fun j _ => M.offspringAbsThirdMoment_eq j k
    rw [Finset.sum_congr rfl hj, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  have hsum : ∑ c, M.meanOf (fun x => |dev x c| * ∑ j, |dev x j| ^ 3) ≤
      2 * N * (N * M.offspringAbsThirdMoment k) := by
    rw [← hG, ← M.meanOf_const_mul,
      ← M.meanOf_sum Finset.univ (fun c x => |dev x c| * ∑ j, |dev x j| ^ 3)]
    refine M.meanOf_mono fun ω => ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (M.sum_abs_dev_le ω)
      (Finset.sum_nonneg fun j _ => by positivity)
  rw [Finset.sum_congr rfl heq, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hsum
  have h3 := M.offspringAbsThirdMoment_nonneg k
  by_contra hcon
  have := mul_lt_mul_of_pos_left (not_le.1 hcon) hN
  linarith

theorem meanOf_sum_sq_mul_sq_le (M : CanningsModel N Ω) (k b : Fin N) :
    M.meanOf (fun x => ∑ j, dev x j ^ 2 * dev x b ^ 2) ≤
      4 * N * M.offspringAbsThirdMoment k := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have h1 : M.meanOf (fun x => ∑ j, dev x j ^ 2 * dev x b ^ 2) ≤
      M.meanOf (fun x => 2 * N * |dev x b| ^ 3 + |dev x b| * ∑ j, |dev x j| ^ 3) := by
    refine M.meanOf_mono fun ω => ?_
    have hterm : ∀ j ∈ (Finset.univ : Finset (Fin N)),
        dev (M.ν ω) j ^ 2 * dev (M.ν ω) b ^ 2 ≤
          |dev (M.ν ω) b| ^ 3 * |dev (M.ν ω) j| + |dev (M.ν ω) b| * |dev (M.ν ω) j| ^ 3 :=
      fun j _ => sq_mul_sq_le_abs _ _
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hA := M.sum_abs_dev_le ω
    have hb3 : 0 ≤ |dev (M.ν ω) b| ^ 3 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hA hb3]
  refine h1.trans ?_
  rw [M.meanOf_add, M.meanOf_const_mul]
  have h2 := M.meanOf_abs_dev_mul_sum_cube_le k b
  have h3 : M.meanOf (fun x => |dev x b| ^ 3) = M.offspringAbsThirdMoment k :=
    M.offspringAbsThirdMoment_eq b k
  rw [h3]
  linarith

theorem meanOf_dev_pow_four_le (M : CanningsModel N Ω) (k b : Fin N) :
    M.meanOf (fun x => dev x b ^ 4) ≤ N * M.offspringAbsThirdMoment k := by
  have h1 : M.meanOf (fun x => dev x b ^ 4) ≤ M.meanOf (fun x => N * |dev x b| ^ 3) := by
    refine M.meanOf_mono fun ω => ?_
    have hle := M.abs_dev_le ω b
    have h3 : 0 ≤ |dev (M.ν ω) b| ^ 3 := by positivity
    have e : dev (M.ν ω) b ^ 4 = |dev (M.ν ω) b| * |dev (M.ν ω) b| ^ 3 := by
      calc dev (M.ν ω) b ^ 4 = (dev (M.ν ω) b ^ 2) ^ 2 := by ring
        _ = (|dev (M.ν ω) b| ^ 2) ^ 2 := by rw [sq_abs]
        _ = |dev (M.ν ω) b| * |dev (M.ν ω) b| ^ 3 := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_right hle h3
  refine h1.trans_eq ?_
  rw [M.meanOf_const_mul]
  exact congrArg _ (M.offspringAbsThirdMoment_eq b k)

theorem meanOf_sum_dev_sq_mul_sq_le (M : CanningsModel N Ω) {S : Finset (Fin N)} {b : Fin N}
    (hb : b ∉ S) :
    M.meanOf (fun x => (∑ j ∈ S, dev x j) ^ 2 * dev x b ^ 2) ≤
      ∑ j ∈ S, M.meanOf (fun x => dev x j ^ 2 * dev x b ^ 2) +
        M.meanOf (fun x => dev x b ^ 4) := by
  classical
  have hm4 : 0 ≤ M.meanOf (fun x => dev x b ^ 4) := M.meanOf_nonneg fun ω => by positivity
  have hexp : M.meanOf (fun x => (∑ j ∈ S, dev x j) ^ 2 * dev x b ^ 2) =
      ∑ j ∈ S, M.meanOf (fun x => dev x j ^ 2 * dev x b ^ 2) +
        ∑ j ∈ S, ∑ l ∈ S.erase j, M.meanOf (fun x => dev x j * dev x l * dev x b ^ 2) := by
    have e : M.meanOf (fun x => (∑ j ∈ S, dev x j) ^ 2 * dev x b ^ 2) =
        M.meanOf (fun x => ∑ j ∈ S, (dev x j ^ 2 * dev x b ^ 2 +
          ∑ l ∈ S.erase j, dev x j * dev x l * dev x b ^ 2)) := by
      refine M.meanOf_congr fun ω => ?_
      rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [← Finset.add_sum_erase S _ hj, add_mul, Finset.sum_mul]
      ring
    rw [e, M.meanOf_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [M.meanOf_add, M.meanOf_sum]
  rw [hexp]
  refine add_le_add le_rfl ?_
  by_cases hcard : S.card ≤ 1
  · have hzero : ∀ j ∈ S, ∑ l ∈ S.erase j,
        M.meanOf (fun x => dev x j * dev x l * dev x b ^ 2) = 0 := by
      intro j hj
      have h0 : (S.erase j).card = 0 := by
        rw [Finset.card_erase_of_mem hj]
        omega
      rw [Finset.card_eq_zero.1 h0, Finset.sum_empty]
    rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero]
    exact hm4
  · have h2 : 2 ≤ S.card := by omega
    have hSN : S.card + 1 ≤ N := by
      have h := Finset.card_le_univ (insert b S)
      rwa [Finset.card_insert_of_notMem hb, Fintype.card_fin] at h
    have hs2 : (2 : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast h2
    have hsN : (S.card : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hSN
    obtain ⟨D, hD⟩ : ∃ D : ℝ, D = ((N : ℝ) - 1) * ((N : ℝ) - 2) := ⟨_, rfl⟩
    have hDpos : 0 < D := by
      rw [hD]
      exact mul_pos (by linarith) (by linarith)
    have hpair : ∀ j ∈ S, ∀ l ∈ S.erase j,
        M.meanOf (fun x => dev x j * dev x l * dev x b ^ 2) ≤
          M.meanOf (fun x => dev x b ^ 4) / D := by
      intro j hj l hl
      have hlj : l ≠ j := Finset.ne_of_mem_erase hl
      have hlS : l ∈ S := Finset.mem_of_mem_erase hl
      have hjb : j ≠ b := fun h => hb (h ▸ hj)
      have hlb : l ≠ b := fun h => hb (h ▸ hlS)
      have h := M.sub_one_mul_sub_two_mul_meanOf_le hlj.symm hjb hlb
      rw [← hD] at h
      rw [le_div_iff₀ hDpos]
      linarith
    have hinner : ∀ j ∈ S, ∑ l ∈ S.erase j,
        M.meanOf (fun x => dev x j * dev x l * dev x b ^ 2) ≤
          ((S.card : ℝ) - 1) * (M.meanOf (fun x => dev x b ^ 4) / D) := by
      intro j hj
      refine (Finset.sum_le_sum (hpair j hj)).trans_eq ?_
      rw [Finset.sum_const, Finset.card_erase_of_mem hj, nsmul_eq_mul,
        Nat.cast_sub (by omega : 1 ≤ S.card), Nat.cast_one]
    refine (Finset.sum_le_sum hinner).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcount : (S.card : ℝ) * ((S.card : ℝ) - 1) ≤ D := by
      rw [hD]
      nlinarith
    have hq : 0 ≤ M.meanOf (fun x => dev x b ^ 4) / D := div_nonneg hm4 hDpos.le
    calc (S.card : ℝ) * (((S.card : ℝ) - 1) * (M.meanOf (fun x => dev x b ^ 4) / D))
        = (S.card : ℝ) * ((S.card : ℝ) - 1) * (M.meanOf (fun x => dev x b ^ 4) / D) := by
          ring
      _ ≤ D * (M.meanOf (fun x => dev x b ^ 4) / D) := mul_le_mul_of_nonneg_right hcount hq
      _ = M.meanOf (fun x => dev x b ^ 4) := mul_div_cancel₀ _ hDpos.ne'

theorem meanOf_sum_dev_pow_four_le (M : CanningsModel N Ω) (k : Fin N) (S : Finset (Fin N)) :
    M.meanOf (fun x => (∑ j ∈ S, dev x j) ^ 4) ≤
      S.card * (31 * N * M.offspringAbsThirdMoment k) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [meanOf]
  | insert b S hb ih =>
    have hexp : M.meanOf (fun x => (∑ j ∈ insert b S, dev x j) ^ 4) =
        M.meanOf (fun x => (∑ j ∈ S, dev x j) ^ 4) +
          4 * M.meanOf (fun x => (∑ j ∈ S, dev x j) ^ 3 * dev x b) +
          6 * M.meanOf (fun x => (∑ j ∈ S, dev x j) ^ 2 * dev x b ^ 2) +
          4 * M.meanOf (fun x => ∑ j ∈ S, dev x j * dev x b ^ 3) +
          M.meanOf (fun x => dev x b ^ 4) := by
      have e : M.meanOf (fun x => (∑ j ∈ insert b S, dev x j) ^ 4) =
          M.meanOf (fun x => (∑ j ∈ S, dev x j) ^ 4 +
            4 * ((∑ j ∈ S, dev x j) ^ 3 * dev x b) +
            6 * ((∑ j ∈ S, dev x j) ^ 2 * dev x b ^ 2) +
            4 * (∑ j ∈ S, dev x j * dev x b ^ 3) + dev x b ^ 4) := by
        refine M.meanOf_congr fun ω => ?_
        rw [Finset.sum_insert hb, ← Finset.sum_mul]
        ring
      rw [e, M.meanOf_add, M.meanOf_add, M.meanOf_add, M.meanOf_add, M.meanOf_const_mul,
        M.meanOf_const_mul, M.meanOf_const_mul]
    have h1 := M.meanOf_sum_dev_cube_mul_dev_nonpos hb
    have h3 : M.meanOf (fun x => ∑ j ∈ S, dev x j * dev x b ^ 3) ≤ 0 := by
      rw [M.meanOf_sum]
      refine Finset.sum_nonpos fun j hj => ?_
      have hjb : j ≠ b := fun h => hb (h ▸ hj)
      have h := M.sub_one_mul_meanOf_dev_mul_cube hjb
      have hm4 : 0 ≤ M.meanOf (fun x => dev x b ^ 4) :=
        M.meanOf_nonneg fun ω => by positivity
      have hN1 : (0 : ℝ) < (N : ℝ) - 1 := by
        have h2 : 2 ≤ N := by
          have h1 := j.isLt
          have h2 := b.isLt
          have h3 : j.val ≠ b.val := Fin.val_ne_of_ne hjb
          omega
        have : (2 : ℝ) ≤ N := by exact_mod_cast h2
        linarith
      by_contra hcon
      have := mul_pos hN1 (not_le.1 hcon)
      linarith
    have h4 := M.meanOf_dev_pow_four_le k b
    have h2 : M.meanOf (fun x => (∑ j ∈ S, dev x j) ^ 2 * dev x b ^ 2) ≤
        4 * N * M.offspringAbsThirdMoment k + N * M.offspringAbsThirdMoment k := by
      refine (M.meanOf_sum_dev_sq_mul_sq_le hb).trans (add_le_add ?_ h4)
      refine le_trans ?_ (M.meanOf_sum_sq_mul_sq_le k b)
      rw [M.meanOf_sum]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        fun j _ _ => M.meanOf_nonneg fun ω => by positivity
    rw [hexp, Finset.card_insert_of_notMem hb]
    push_cast
    linarith

theorem countChain_expect_sq_increment (M : CanningsModel N Ω) (k : Fin N)
    (i : Fin (N + 1)) :
    M.countChain.expect (fun j => (((j : ℕ) : ℝ) - (i : ℕ)) ^ 2) i =
      M.offspringVariance k / ((N : ℝ) - 1) * (((i : ℕ) : ℝ) * ((N : ℝ) - (i : ℕ))) := by
  have hhet := (M.countChain_expect_natFun (fun n => (n : ℝ) * ((N : ℝ) - n)) i).symm.trans
    (M.countChain_expect_hetCount k i)
  have hcount := (M.countChain_expect_natFun (fun n => (n : ℝ)) i).symm.trans
    (M.countChain_expect_count i)
  refine (M.countChain_expect_natFun (fun n => ((n : ℝ) - (i : ℕ)) ^ 2) i).trans ?_
  obtain ⟨X, hX⟩ : ∃ X : Ω → ℕ, X = fun ω =>
      ∑ k ∈ Finset.univ.filter (fun k : Fin N => k.val < i.val), M.ν ω k := ⟨_, rfl⟩
  have hhet' : ∑ ω, M.w ω * ((X ω : ℝ) * ((N : ℝ) - X ω)) =
      (1 - M.offspringVariance k / ((N : ℝ) - 1)) * (((i : ℕ) : ℝ) * ((N : ℝ) - (i : ℕ))) := by
    rw [hX]
    exact hhet
  have hcount' : ∑ ω, M.w ω * (X ω : ℝ) = ((i : ℕ) : ℝ) := by
    rw [hX]
    exact hcount
  have hterm : ∀ ω, M.w ω * (((X ω : ℝ) - (i : ℕ)) ^ 2) =
      -(M.w ω * ((X ω : ℝ) * ((N : ℝ) - X ω))) +
        ((N : ℝ) - 2 * (i : ℕ)) * (M.w ω * (X ω : ℝ)) + ((i : ℕ) : ℝ) ^ 2 * M.w ω :=
    fun ω => by ring
  subst hX
  change ∑ ω, M.w ω * ((((∑ k ∈ Finset.univ.filter (fun k : Fin N => k.val < i.val),
    M.ν ω k : ℕ) : ℝ) - (i : ℕ)) ^ 2) = _
  rw [Finset.sum_congr rfl fun ω _ => hterm ω, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hhet', hcount', M.sum_w]
  ring

theorem countChain_expect_fourth_increment_le (M : CanningsModel N Ω) (k : Fin N)
    (i : Fin (N + 1)) :
    M.countChain.expect (fun j => (((j : ℕ) : ℝ) - (i : ℕ)) ^ 4) i ≤
      31 * (N : ℝ) ^ 2 * M.offspringAbsThirdMoment k := by
  have hiN : (i : ℕ) ≤ N := Nat.le_of_lt_succ i.isLt
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin N),
      S = Finset.univ.filter (fun k : Fin N => k.val < i.val) := ⟨_, rfl⟩
  have hc : (S.card : ℝ) = ((i : ℕ) : ℝ) := by
    rw [hS, Fin.card_filter_val_lt, min_eq_right hiN]
  have hpt : ∀ ω, ((∑ k ∈ S, M.ν ω k : ℕ) : ℝ) - (i : ℕ) = ∑ j ∈ S, dev (M.ν ω) j := by
    intro ω
    simp only [dev, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, hc,
      Nat.cast_sum]
  refine (M.countChain_expect_natFun (fun n => ((n : ℝ) - (i : ℕ)) ^ 4) i).trans_le ?_
  rw [← hS]
  have hmean : ∑ ω, M.w ω * (((∑ k ∈ S, M.ν ω k : ℕ) : ℝ) - (i : ℕ)) ^ 4 =
      M.meanOf (fun x => (∑ j ∈ S, dev x j) ^ 4) :=
    Finset.sum_congr rfl fun ω _ => by rw [hpt ω]
  refine (hmean.le.trans (M.meanOf_sum_dev_pow_four_le k S)).trans ?_
  rw [hc]
  have h3 := M.offspringAbsThirdMoment_nonneg k
  have hi : ((i : ℕ) : ℝ) ≤ N := by exact_mod_cast hiN
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right hi (mul_nonneg hN h3)]

end Rhone.MarkovChain.CanningsModel
