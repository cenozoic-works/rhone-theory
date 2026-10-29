/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.InfiniteAlleles.Boundary

/-!
# The `ρ = 0` Golding–Ewens collapse

Source: golding1984, pp. 263–264. -/

@[expose] public section

namespace Rhone.Probability.InfiniteAlleles

open Finset LinearAlgebra.Recursion LinearAlgebra.Recursion.Config

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] {θA θB : F}

def cfgC (m : ℕ) : Config 1 1 := ⟨fun _ => 0, fun _ => 0, fun _ _ => m⟩

@[simp] theorem cfgC_a (m : ℕ) (i : Fin 1) : (cfgC m).a i = 0 := rfl

@[simp] theorem cfgC_b (m : ℕ) (j : Fin 1) : (cfgC m).b j = 0 := rfl

@[simp] theorem cfgC_c (m : ℕ) (i : Fin 1) (j : Fin 1) : (cfgC m).c i j = m := rfl

@[simp] theorem cfgC_t (m : ℕ) : (cfgC m).t = m := by
  simp [Rhone.LinearAlgebra.Recursion.Config.t]

@[simp] theorem cfgC_sumA (m : ℕ) : (cfgC m).sumA = 0 := by simp [Config.sumA]

@[simp] theorem cfgC_sumB (m : ℕ) : (cfgC m).sumB = 0 := by simp [Config.sumB]

@[simp] theorem cfgC_nA (m : ℕ) : (cfgC m).nA = m :=
    by simp [Rhone.LinearAlgebra.Recursion.Config.nA]

@[simp] theorem cfgC_nB (m : ℕ) : (cfgC m).nB = m :=
    by simp [Rhone.LinearAlgebra.Recursion.Config.nB]

@[simp] theorem cfgC_n (m : ℕ) : (cfgC m).n = m := by simp [Rhone.LinearAlgebra.Recursion.Config.n]

@[simp] theorem cfgC_cRow (m : ℕ) (i : Fin 1) : (cfgC m).cRow i = m := by simp [Config.cRow]

@[simp] theorem cfgC_cCol (m : ℕ) (j : Fin 1) : (cfgC m).cCol j = m := by simp [Config.cCol]

@[simp] theorem cfgC_mA (m : ℕ) (i : Fin 1) : (cfgC m).mA i = m := by simp [Config.mA]

@[simp] theorem cfgC_mB (m : ℕ) (j : Fin 1) : (cfgC m).mB j = m := by simp [Config.mB]

theorem dropC_cfgC (m : ℕ) : (cfgC m).dropC 0 0 = cfgC (m - 1) := by
  refine Config.ext rfl rfl (funext fun i' => funext fun j' => ?_)
  have hi : i' = 0 := Subsingleton.elim _ _
  have hj : j' = 0 := Subsingleton.elim _ _
  subst hi; subst hj
  simp [Config.dropC, cfgC, decC, decf]

theorem cfgC_one : cfgC 1 = Config.eC 0 0 := by
  refine Config.ext rfl rfl (funext fun i' => funext fun j' => ?_)
  have hi : i' = 0 := Subsingleton.elim _ _
  have hj : j' = 0 := Subsingleton.elim _ _
  subst hi; subst hj
  simp [cfgC, Config.eC, incC, incf]

theorem rhsIA_cfgC {m : ℕ} (hm : 2 ≤ m) (q : Config 1 1 → F) :
    rhsIA θA θB 0 q (cfgC m) = ((m * (m - 1) : ℕ) : F) * q (cfgC (m - 1)) := by
  have hk : ∀ i j : Fin 1, killIndA (cfgC m) i j = 0 := by
    intro i j; simp only [killIndA, cfgC_mA]; simp; omega
  have hk' : ∀ i j : Fin 1, killIndB (cfgC m) i j = 0 := by
    intro i j; simp only [killIndB, cfgC_mB]; simp; omega
  simp only [rhsIA, Fin.sum_univ_one, Config.coalA, Config.coalB, Config.coalC, Config.coalAB,
    dropIndA, dropIndB, cfgC_a, cfgC_b, cfgC_c, cfgC_cRow, cfgC_cCol, hk, hk', dropC_cfgC]
  norm_num

theorem step_rho_zero {q : Config 1 1 → F}
    (h : IsSolutionIA θA θB 0 q) (n : ℕ) (hn : 1 ≤ n) :
    ((n : F) + θA + θB) * q (cfgC (n + 1)) = (n : F) * q (cfgC n) := by
  have hrec := h.recursion (cfgC (n + 1)) (by simp; omega)
  rw [rhsIA_cfgC (by omega)] at hrec
  simp only [Rhone.LinearAlgebra.Recursion.diag, cfgC_n, cfgC_nA, cfgC_nB, cfgC_t,
    Nat.add_sub_cancel] at hrec
  have hne : ((n : F) + 1) ≠ 0 := by positivity
  have hkey : ((n : F) + 1) * (((n : F) + θA + θB) * q (cfgC (n + 1)))
      = ((n : F) + 1) * ((n : F) * q (cfgC n)) := by
    push_cast at hrec ⊢
    linear_combination hrec
  exact mul_left_cancel₀ hne hkey

/-- Source: golding1984, p. 264. -/
theorem golding_rho_zero (hθA : 0 < θA) (hθB : 0 < θB) {q : Config 1 1 → F}
    (h : IsSolutionIA θA θB 0 q) : ∀ n : ℕ, 1 ≤ n →
      q (cfgC n) = ∏ i ∈ Finset.Ico 1 n, ((i : F) / ((i : F) + θA + θB)) := by
  intro n
  induction n with
  | zero => intro hn; omega
  | succ n ih =>
    intro _
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [cfgC_one, eC_eq_one hθA hθB le_rfl h]
      simp
    · have hstep := step_rho_zero h n hn
      have hne : ((n : F) + θA + θB) ≠ 0 := by positivity
      rw [Finset.prod_Ico_succ_top hn, ← ih hn]
      field_simp
      linarith [hstep]

theorem PIA_golding_rho_zero (hθA : 0 < θA) (hθB : 0 < θB) (n : ℕ) (hn : 1 ≤ n) :
    PIA (KA := 1) (KB := 1) hθA hθB (le_refl (0 : F)) (cfgC n)
      = ∏ i ∈ Finset.Ico 1 n, ((i : F) / ((i : F) + θA + θB)) :=
  golding_rho_zero hθA hθB (PIA_isSolutionIA hθA hθB (le_refl (0 : F))) n hn

end Rhone.Probability.InfiniteAlleles
