/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.EffectiveSize
public import Rhone.MarkovChain.InbreedingEffectiveSampling
public import Rhone.MarkovChain.CanningsHeterozygosity
public import Rhone.MarkovChain.CanningsFourthMoment
public import Rhone.Coalescent.CanningsAncestral

/-!
# Inbreeding effective size of a Cannings model

Source: ewens2004, sec. 3.3, sec. 3.7; cannings1974, sec. 3, p. 266; mohle_sagitov2001, p. 1548, eq.
(4). -/

@[expose] public section

open Finset

namespace Rhone.MarkovChain.CanningsModel

open EffectiveSize

variable {N : ℕ} {Ω : Type*} [Fintype Ω]

noncomputable def offspringCopyEquiv (M : CanningsModel N Ω) (ω : Ω) :
    (Σ k : Fin N, Fin (M.ν ω k)) ≃ Fin N :=
  Fintype.equivFinOfCardEq
    (by rw [Fintype.card_sigma]; simp only [Fintype.card_fin]; exact M.sum_ν ω)

noncomputable def offspringLabel {A : Type*} (M : CanningsModel N Ω) (g : Fin N → A) (ω : Ω)
    (j : Fin N) : A :=
  g ((M.offspringCopyEquiv ω).symm j).1

noncomputable def offspringDistinctIbd {A : Type*} [DecidableEq A] (M : CanningsModel N Ω)
    (g : Fin N → A) : ℝ :=
  ∑ ω, M.w ω * distinctCopyIbd N (M.offspringLabel g ω)

end Rhone.MarkovChain.CanningsModel

namespace Rhone.Coalescent.EffectiveSize

theorem distinctCopyIbd_eq_sum_sub {A : Type*} [DecidableEq A] (K : ℕ) (h : Fin K → A) :
    MarkovChain.EffectiveSize.distinctCopyIbd K h =
      ((∑ x : Fin K, ∑ y : Fin K, if h x = h y then (1 : ℝ) else 0) - K) *
        (1 / ((K : ℝ) * (K - 1 : ℕ))) := by
  unfold MarkovChain.EffectiveSize.distinctCopyIbd
  set C : ℝ := 1 / ((K : ℝ) * (K - 1 : ℕ))
  have hpt : ∀ x y : Fin K, (if x ≠ y ∧ h x = h y then C else 0) =
      (if h x = h y then (1 : ℝ) else 0) * C - (if x = y then (1 : ℝ) else 0) * C := by
    intro x y
    by_cases hxy : x = y
    · subst hxy; simp
    · by_cases hh : h x = h y <;> simp [hxy, hh]
  have hdiag : (∑ x : Fin K, ∑ y : Fin K, if x = y then (1 : ℝ) else 0) = K := by simp
  calc ∑ ab : Fin K × Fin K, (if ab.1 ≠ ab.2 ∧ h ab.1 = h ab.2 then C else 0)
      = ∑ x : Fin K, ∑ y : Fin K,
          ((if h x = h y then (1 : ℝ) else 0) * C - (if x = y then (1 : ℝ) else 0) * C) := by
        rw [Fintype.sum_prod_type]
        exact Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => hpt x y))
    _ = (∑ x : Fin K, ∑ y : Fin K, if h x = h y then (1 : ℝ) else 0) * C -
          (∑ x : Fin K, ∑ y : Fin K, if x = y then (1 : ℝ) else 0) * C := by
        simp only [Finset.sum_sub_distrib, Finset.sum_mul]
    _ = _ := by rw [hdiag, sub_mul]

end Rhone.Coalescent.EffectiveSize

namespace Rhone.MarkovChain.CanningsModel

open Coalescent.EffectiveSize EffectiveSize

variable {N : ℕ} {Ω : Type*} [Fintype Ω]

theorem sum_offspringLabel_eq {A : Type*} [DecidableEq A] (M : CanningsModel N Ω)
    (g : Fin N → A) (ω : Ω) :
    (∑ x : Fin N, ∑ y : Fin N,
        if M.offspringLabel g ω x = M.offspringLabel g ω y then (1 : ℝ) else 0) =
      ∑ a, ∑ b, if g a = g b then (M.ν ω a : ℝ) * (M.ν ω b : ℝ) else 0 := by
  have h1 : (∑ x : Fin N, ∑ y : Fin N,
        if M.offspringLabel g ω x = M.offspringLabel g ω y then (1 : ℝ) else 0) =
      ∑ s : (Σ k : Fin N, Fin (M.ν ω k)), ∑ t : (Σ k : Fin N, Fin (M.ν ω k)),
        if g s.1 = g t.1 then (1 : ℝ) else 0 :=
    Fintype.sum_equiv (M.offspringCopyEquiv ω).symm _ _ (fun x =>
      Fintype.sum_equiv (M.offspringCopyEquiv ω).symm _ _ (fun y => rfl))
  have hsig : ∀ c : A, (∑ t : (Σ k : Fin N, Fin (M.ν ω k)),
      if c = g t.1 then (1 : ℝ) else 0) = ∑ b, if c = g b then (M.ν ω b : ℝ) else 0 := by
    intro c
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    change (∑ _y : Fin (M.ν ω b), if c = g b then (1 : ℝ) else 0) = _
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    by_cases hcb : c = g b <;> simp [hcb]
  rw [h1]
  simp_rw [hsig]
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  change (∑ _x : Fin (M.ν ω a), ∑ b, if g a = g b then (M.ν ω b : ℝ) else 0) = _
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  by_cases hab : g a = g b <;> simp [hab]

/-- Source: ewens2004, sec. 3.3. -/
theorem sum_w_mul_offspring_sq (M : CanningsModel N Ω) (k a : Fin N) :
    ∑ ω, M.w ω * ((M.ν ω a : ℝ) * (M.ν ω a : ℝ)) = M.offspringVariance k + 1 := by
  have hmean : ∑ ω, M.w ω * (M.ν ω a : ℝ) = 1 := M.expected_offspring a
  have hterm : ∀ ω, M.w ω * ((M.ν ω a : ℝ) * (M.ν ω a : ℝ)) =
      M.w ω * ((M.ν ω a : ℝ) - 1) ^ 2 + 2 * (M.w ω * (M.ν ω a : ℝ)) - M.w ω :=
    fun ω => by ring
  rw [Finset.sum_congr rfl fun ω _ => hterm ω, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, hmean, M.sum_w, ← M.offspringVariance_eq a k]
  unfold offspringVariance
  ring

/-- Source: ewens2004, secs. 3.3, 3.7. -/
theorem offspringDistinctIbd_recursion {A : Type*} [DecidableEq A] (M : CanningsModel N Ω)
    (k : Fin N) (hN : 2 ≤ N) (g : Fin N → A) :
    M.offspringDistinctIbd g = M.offspringVariance k / ((N : ℝ) - 1) +
      (1 - M.offspringVariance k / ((N : ℝ) - 1)) * distinctCopyIbd N g := by
  have hNr : (N : ℝ) ≠ 0 := by
    have : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    exact this.ne'
  have hN1 : (N : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hNm : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hpair : ∀ a b : Fin N, (∑ ω, M.w ω * ((M.ν ω a : ℝ) * (M.ν ω b : ℝ))) =
      (1 - M.offspringVariance k / ((N : ℝ) - 1)) +
        (if a = b then M.offspringVariance k * N / ((N : ℝ) - 1) else 0) := by
    intro a b
    by_cases hab : a = b
    · subst hab
      have hif : (if a = a then M.offspringVariance k * N / ((N : ℝ) - 1) else 0) =
          M.offspringVariance k * N / ((N : ℝ) - 1) := by simp
      rw [hif, M.sum_w_mul_offspring_sq k a]
      field_simp
      ring
    · have hif : (if a = b then M.offspringVariance k * N / ((N : ℝ) - 1) else 0) = 0 := by
        simp [hab]
      rw [hif, add_zero]
      have h := M.sub_one_mul_sum_offspring_mul hab
      rw [M.offspringVariance_eq a k] at h
      have he : ∑ ω, M.w ω * ((M.ν ω a : ℝ) * (M.ν ω b : ℝ)) =
          ((N : ℝ) - 1 - M.offspringVariance k) / ((N : ℝ) - 1) := by
        rw [eq_div_iff hN1]
        linarith [h]
      rw [he, sub_div, div_self hN1]
  have hES : ∑ ω, M.w ω * (∑ a, ∑ b, if g a = g b then (M.ν ω a : ℝ) * (M.ν ω b : ℝ) else 0) =
      ∑ a, ∑ b, if g a = g b then (∑ ω, M.w ω * ((M.ν ω a : ℝ) * (M.ν ω b : ℝ))) else 0 := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    split_ifs <;> simp
  have hES2 : (∑ a, ∑ b, if g a = g b then (∑ ω, M.w ω * ((M.ν ω a : ℝ) * (M.ν ω b : ℝ)))
        else 0) =
      (1 - M.offspringVariance k / ((N : ℝ) - 1)) *
          (∑ x : Fin N, ∑ y : Fin N, if g x = g y then (1 : ℝ) else 0) +
        N * (M.offspringVariance k * N / ((N : ℝ) - 1)) := by
    simp_rw [hpair]
    have hsplit : ∀ a b : Fin N, (if g a = g b then (1 - M.offspringVariance k / ((N : ℝ) - 1)) +
          (if a = b then M.offspringVariance k * N / ((N : ℝ) - 1) else 0) else 0) =
        (1 - M.offspringVariance k / ((N : ℝ) - 1)) * (if g a = g b then (1 : ℝ) else 0) +
          (if a = b then M.offspringVariance k * N / ((N : ℝ) - 1) else 0) := by
      intro a b
      by_cases hab : a = b
      · subst hab; simp
      · by_cases hg : g a = g b <;> simp [hab, hg]
    simp_rw [hsplit, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp
  have hlin : ∀ (X : Ω → ℝ) (c : ℝ),
      ∑ ω, M.w ω * ((X ω - N) * c) = ((∑ ω, M.w ω * X ω) - N) * c := by
    intro X c
    have h : ∀ ω, M.w ω * ((X ω - N) * c) = M.w ω * X ω * c - M.w ω * (N * c) :=
      fun ω => by ring
    rw [Finset.sum_congr rfl (fun ω _ => h ω), Finset.sum_sub_distrib, ← Finset.sum_mul,
      ← Finset.sum_mul, M.sum_w]
    ring
  unfold offspringDistinctIbd
  simp_rw [distinctCopyIbd_eq_sum_sub, sum_offspringLabel_eq]
  rw [hlin (fun ω => ∑ a, ∑ b, if g a = g b then (M.ν ω a : ℝ) * (M.ν ω b : ℝ) else 0),
    hES, hES2, hNm]
  field_simp
  ring

/-- Source: ewens2004, sec. 3.3; mohle_sagitov2001, p. 1548, eq. (4). -/
theorem pairCoalProb_eq_offspringVariance (M : CanningsModel N Ω) (k : Fin N) :
    M.pairCoalProb = M.offspringVariance k / ((N : ℝ) - 1) := by
  rw [M.pairCoalProb_eq k]
  congr 1
  have h := M.sum_w_mul_offspring_sq k k
  have hmean : ∑ ω, M.w ω * (M.ν ω k : ℝ) = 1 := M.expected_offspring k
  have hsplit : ∀ ω, M.w ω * ((M.ν ω k : ℝ) * ((M.ν ω k : ℝ) - 1)) =
      M.w ω * ((M.ν ω k : ℝ) * (M.ν ω k : ℝ)) - M.w ω * (M.ν ω k : ℝ) :=
    fun ω => by ring
  rw [Finset.sum_congr rfl fun ω _ => hsplit ω, Finset.sum_sub_distrib, h, hmean]
  ring

/-- Source: ewens2004, secs. 3.3, 3.7. -/
theorem offspringDistinctIbd_eq_pairCoalProb {A : Type*} [DecidableEq A]
    (M : CanningsModel N Ω) (hN : 2 ≤ N) (g : Fin N → A) :
    M.offspringDistinctIbd g =
      M.pairCoalProb + (1 - M.pairCoalProb) * distinctCopyIbd N g := by
  have k : Fin N := ⟨0, by omega⟩
  rw [M.offspringDistinctIbd_recursion k hN g, M.pairCoalProb_eq_offspringVariance k]

end Rhone.MarkovChain.CanningsModel

namespace Rhone.Coalescent.EffectiveSize

open Rhone.Combinatorics MarkovChain

variable {N : ℕ} {Ω : Type*} [Fintype Ω]

/-- Source: ewens2004, secs. 3.3, 3.7. -/
theorem inbreeding_effective_cannings {A : Type*} [DecidableEq A] (M : CanningsModel N Ω)
    (k : Fin N) (hN : 2 ≤ N) (g : Fin N → A) (hF : EffectiveSize.distinctCopyIbd N g ≠ 1) :
    EffectiveSize.inbreedingEffective (EffectiveSize.distinctCopyIbd N g)
        (M.offspringDistinctIbd g) =
      ((N : ℝ) - 1) / (2 * M.offspringVariance k) := by
  have hD : 1 - EffectiveSize.distinctCopyIbd N g ≠ 0 := sub_ne_zero.mpr (Ne.symm hF)
  unfold EffectiveSize.inbreedingEffective EffectiveSize.coalescenceEffective
  rw [M.offspringDistinctIbd_recursion k hN g]
  have hrate : (M.offspringVariance k / ((N : ℝ) - 1) +
      (1 - M.offspringVariance k / ((N : ℝ) - 1)) * EffectiveSize.distinctCopyIbd N g -
        EffectiveSize.distinctCopyIbd N g) / (1 - EffectiveSize.distinctCopyIbd N g) =
      M.offspringVariance k / ((N : ℝ) - 1) := by
    rw [div_eq_iff hD]
    ring
  rw [hrate, mul_div_assoc', one_div_div]

/-- Source: ewens2004, sec. 3.7. -/
theorem inbreeding_effective_cannings_eq_eigenvalue {A : Type*} [DecidableEq A]
    (M : CanningsModel N Ω) (k : Fin N) (hN : 2 ≤ N) (g : Fin N → A)
    (hF : EffectiveSize.distinctCopyIbd N g ≠ 1) :
    EffectiveSize.inbreedingEffective (EffectiveSize.distinctCopyIbd N g)
        (M.offspringDistinctIbd g) =
      EffectiveSize.eigenvalueEffective (1 - M.offspringVariance k / ((N : ℝ) - 1)) := by
  rw [inbreeding_effective_cannings M k hN g hF]
  unfold EffectiveSize.eigenvalueEffective EffectiveSize.coalescenceEffective
  rw [sub_sub_cancel, mul_div_assoc', one_div_div]

/-- Source: ewens2004, secs. 3.3, 3.7. -/
theorem inbreeding_effective_cannings_het (M : CanningsModel N Ω) (k : Fin N)
    (i : Fin (N + 1)) (hi0 : 0 < i.val) (hi1 : i.val < N) :
    EffectiveSize.inbreedingEffective
        (1 - 2 / ((N : ℝ) * ((N : ℝ) - 1)) * ((i : ℝ) * ((N : ℝ) - i)))
        (1 - M.countChain.expect
          (fun j => 2 / ((N : ℝ) * ((N : ℝ) - 1)) * ((j : ℝ) * ((N : ℝ) - j))) i) =
      ((N : ℝ) - 1) / (2 * M.offspringVariance k) := by
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast (show 2 ≤ N by omega)
  have hNr : (N : ℝ) ≠ 0 := by linarith
  have hN1 : (N : ℝ) - 1 ≠ 0 := by linarith
  have hi : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi0
  have hi' : (i : ℝ) < N := by exact_mod_cast hi1
  have hh : 2 / ((N : ℝ) * ((N : ℝ) - 1)) * ((i : ℝ) * ((N : ℝ) - i)) ≠ 0 :=
    mul_ne_zero (div_ne_zero two_ne_zero (mul_ne_zero hNr hN1))
      (mul_ne_zero hi.ne' (by linarith))
  have hE : M.countChain.expect
        (fun j => 2 / ((N : ℝ) * ((N : ℝ) - 1)) * ((j : ℝ) * ((N : ℝ) - j))) i =
      2 / ((N : ℝ) * ((N : ℝ) - 1)) *
        ((1 - M.offspringVariance k / ((N : ℝ) - 1)) * ((i : ℝ) * ((N : ℝ) - i))) := by
    have h := M.countChain_expect_hetCount k i
    change M.countKernel.expect (fun j => (j : ℝ) * ((N : ℝ) - j)) i = _ at h
    change M.countKernel.expect
      (fun j => 2 / ((N : ℝ) * ((N : ℝ) - 1)) * ((j : ℝ) * ((N : ℝ) - j))) i = _
    rw [CountKernel.expect_const_mul, h]
  unfold EffectiveSize.inbreedingEffective EffectiveSize.coalescenceEffective
  rw [hE]
  have hD : 1 - (1 - 2 / ((N : ℝ) * ((N : ℝ) - 1)) * ((i : ℝ) * ((N : ℝ) - i))) ≠ 0 := by
    rw [sub_sub_cancel]; exact hh
  have hrate : (1 - 2 / ((N : ℝ) * ((N : ℝ) - 1)) *
        ((1 - M.offspringVariance k / ((N : ℝ) - 1)) * ((i : ℝ) * ((N : ℝ) - i))) -
        (1 - 2 / ((N : ℝ) * ((N : ℝ) - 1)) * ((i : ℝ) * ((N : ℝ) - i)))) /
      (1 - (1 - 2 / ((N : ℝ) * ((N : ℝ) - 1)) * ((i : ℝ) * ((N : ℝ) - i)))) =
      M.offspringVariance k / ((N : ℝ) - 1) := by
    rw [div_eq_iff hD]
    ring
  rw [hrate, mul_div_assoc', one_div_div]

/-- Source: ewens2004, secs. 3.3, 3.7. -/
theorem inbreeding_effective_cannings_wf {A : Type*} [DecidableEq A] {N : ℕ} (hN : 0 < N)
    (g : Fin (2 * N) → A) (hF : EffectiveSize.distinctCopyIbd (2 * N) g ≠ 1) :
    EffectiveSize.inbreedingEffective (EffectiveSize.distinctCopyIbd (2 * N) g)
        ((wfModel (2 * N)).offspringDistinctIbd g) =
      (N : ℝ) := by
  have k : Fin (2 * N) := ⟨0, by omega⟩
  rw [inbreeding_effective_cannings (wfModel (2 * N)) k (by omega) g hF,
    wfModel_offspringVariance (2 * N) k]
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := by linarith
  push_cast
  have h1 : 2 * (1 - 1 / (2 * (N : ℝ))) = (2 * (N : ℝ) - 1) * 1 / N := by
    field_simp
  have h2 : 2 * (N : ℝ) - 1 ≠ 0 := by linarith
  rw [h1, div_div_eq_mul_div, mul_div_mul_left _ _ h2, div_one]

/-- Source: ewens2004, sec. 3.3. -/
theorem offspringDistinctIbd_wf_eq_offspringCopyIbd {A : Type*} [DecidableEq A] {K : ℕ}
    (hK : 2 ≤ K) (g : Fin K → A) :
    (wfModel K).offspringDistinctIbd g = EffectiveSize.offspringCopyIbd K g := by
  have k : Fin K := ⟨0, by omega⟩
  have hK2 : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hK0 : (K : ℝ) ≠ 0 := by linarith
  have hK1 : (K : ℝ) - 1 ≠ 0 := by linarith
  rw [(wfModel K).offspringDistinctIbd_recursion k hK g, wfModel_offspringVariance K k,
    EffectiveSize.offspring_copy_ibd_recursion K hK g]
  have hc : (1 - 1 / (K : ℝ)) / ((K : ℝ) - 1) = 1 / (K : ℝ) := by
    rw [div_eq_iff hK1]
    field_simp
  rw [hc]

/-- Source: ewens2004, secs. 3.4, 3.7. -/
theorem inbreeding_effective_cannings_moran {A : Type*} [DecidableEq A] {N : ℕ} (hN : 0 < N)
    (hN2 : 2 ≤ N) (g : Fin N → A) (hF : EffectiveSize.distinctCopyIbd N g ≠ 1) :
    EffectiveSize.inbreedingEffective (EffectiveSize.distinctCopyIbd N g)
        ((moranModel N hN).offspringDistinctIbd g) =
      (N : ℝ) ^ 2 / 4 := by
  have k : Fin N := ⟨0, hN⟩
  rw [inbreeding_effective_cannings (moranModel N hN) k hN2 g hF,
    moranModel_offspringVariance N hN k]
  have hN2' : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hN1 : (N : ℝ) - 1 ≠ 0 := by linarith
  have h1 : 2 * (2 * ((N : ℝ) - 1) / (N : ℝ) ^ 2) = ((N : ℝ) - 1) * 4 / (N : ℝ) ^ 2 := by
    ring
  rw [h1, div_div_eq_mul_div, mul_div_mul_left _ _ hN1]

/-- Source: ewens2004, sec. 3.3; cannings1974, sec. 3, p. 266. -/
private theorem cannings_frequency_variance (M : CanningsModel N Ω) (k : Fin N)
    (i : Fin (N + 1)) :
    M.countChain.expect (fun j => ((j : ℝ) / N - (i : ℝ) / N) ^ 2) i =
      M.offspringVariance k / ((N : ℝ) - 1) * ((i : ℝ) / N) * (1 - (i : ℝ) / N) := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Fin.pos k).ne'
  have hscale : (fun j : Fin (N + 1) => ((j : ℝ) / N - (i : ℝ) / N) ^ 2) =
      fun j : Fin (N + 1) => (1 / (N : ℝ) ^ 2) * (((j : ℝ) - i) ^ 2) := by
    funext j
    rw [div_sub_div_same, div_pow]
    ring
  rw [hscale]
  have h := M.countChain_expect_sq_increment k i
  change M.countKernel.expect (fun j => ((j : ℝ) - i) ^ 2) i = _ at h
  change M.countKernel.expect (fun j => (1 / (N : ℝ) ^ 2) * (((j : ℝ) - i) ^ 2)) i = _
  rw [CountKernel.expect_const_mul, h]
  have e : (1 : ℝ) - (i : ℝ) / N = ((N : ℝ) - i) / N := by
    rw [sub_div, div_self hN]
  rw [e]
  ring

/-- Source: ewens2004, sec. 3.7. -/
theorem inbreeding_effective_cannings_eq_variance {A : Type*} [DecidableEq A]
    (M : CanningsModel N Ω) (k : Fin N) (g : Fin N → A) (hF : EffectiveSize.distinctCopyIbd N g ≠ 1)
    (i : Fin (N + 1)) (hi0 : 0 < i.val) (hi1 : i.val < N) :
    EffectiveSize.inbreedingEffective (EffectiveSize.distinctCopyIbd N g)
        (M.offspringDistinctIbd g) =
      EffectiveSize.varianceEffective ((i : ℝ) / N)
        (M.countChain.expect (fun j => ((j : ℝ) / N - (i : ℝ) / N) ^ 2) i) := by
  rw [inbreeding_effective_cannings M k (by omega) g hF, cannings_frequency_variance M k i]
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hi0' : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi0
  have hi1' : (i : ℝ) < N := by exact_mod_cast hi1
  have hp0 : (0 : ℝ) < (i : ℝ) / N := div_pos hi0' hN
  have hp1 : (i : ℝ) / N < 1 := (div_lt_one hN).mpr hi1'
  have hpq : (i : ℝ) / N * (1 - (i : ℝ) / N) ≠ 0 := (mul_pos hp0 (by linarith)).ne'
  unfold EffectiveSize.varianceEffective
  have h1 : 2 * (M.offspringVariance k / ((N : ℝ) - 1) * ((i : ℝ) / N) * (1 - (i : ℝ) / N)) =
      (i : ℝ) / N * (1 - (i : ℝ) / N) * (2 * M.offspringVariance k) / ((N : ℝ) - 1) := by
    ring
  rw [h1, div_div_eq_mul_div, mul_div_mul_left _ _ hpq]

end Rhone.Coalescent.EffectiveSize
