/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.GeneralMutation.Exist

/-! # The one-locus general-mutation-matrix system over an arbitrary finite alphabet -/

@[expose] public section

namespace Rhone.MarkovChain.GeneralMutation

open Finset LinearAlgebra.Recursion

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θ : F} {ν : ι → F} {P : ι → ι → F}

structure IsSolutionOneG (θ : F) (ν : ι → F) (P : ι → ι → F) (q : (ι → ℕ) → F) : Prop where
  empty : q (fun _ => 0) = 1
  bdry : ∀ x, q (incf (fun _ => 0) x) = ν x
  recursion : ∀ m : ι → ℕ, 2 ≤ ∑ x, m x →
    ((((∑ x, m x) * ((∑ x, m x) - 1) : ℕ) : F) + θ * ((∑ x, m x : ℕ) : F)) * q m
      = (∑ x, ((m x * (m x - 1) : ℕ) : F) * q (decf m x))
        + θ * ∑ x, ∑ y, P y x * ((m x : ℕ) : F) * q (incf (decf m x) y)

def wtI (ν : ι → F) (m : ι → ℕ) : F := ∏ x, ν x ^ m x

omit [DecidableEq ι] in
theorem wtI_pos (hν : ∀ x, 0 < ν x) (m : ι → ℕ) : 0 < wtI ν m :=
  Finset.prod_pos fun x _ => pow_pos (hν x) _

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem wtI_incf (ν : ι → F) (m : ι → ℕ) (y : ι) : wtI ν (incf m y) = wtI ν m * ν y := by
  have hsplit : ∀ g : ι → ℕ,
      (∏ x, ν x ^ g x) = ν y ^ g y * ∏ x ∈ Finset.univ.erase y, ν x ^ g x :=
    fun g => (Finset.mul_prod_erase _ _ (Finset.mem_univ y)).symm
  have herase : ∀ x ∈ Finset.univ.erase y, ν x ^ incf m y x = ν x ^ m x := by
    intro x hx
    rw [incf_of_ne _ (Finset.mem_erase.mp hx).1]
  rw [wtI, wtI, hsplit (incf m y), hsplit m, Finset.prod_congr rfl herase, incf_self, pow_succ]
  ring

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem wtI_decf {m : ι → ℕ} {x : ι} (h : m x ≠ 0) : wtI ν (decf m x) * ν x = wtI ν m := by
  have hsplit : ∀ g : ι → ℕ,
      (∏ z, ν z ^ g z) = ν x ^ g x * ∏ z ∈ Finset.univ.erase x, ν z ^ g z :=
    fun g => (Finset.mul_prod_erase _ _ (Finset.mem_univ x)).symm
  have herase : ∀ z ∈ Finset.univ.erase x, ν z ^ decf m x z = ν z ^ m z := by
    intro z hz
    rw [decf_of_ne _ (Finset.mem_erase.mp hz).1]
  obtain ⟨p, hp⟩ : ∃ p, m x = p + 1 := ⟨m x - 1, by omega⟩
  rw [wtI, wtI, hsplit (decf m x), hsplit m, Finset.prod_congr rfl herase, decf_self, hp]
  simp only [Nat.add_sub_cancel, pow_succ]
  ring

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem wtI_incf_decf {m : ι → ℕ} {x : ι} (y : ι) (h : m x ≠ 0) :
    wtI ν (incf (decf m x) y) * ν x = wtI ν m * ν y := by
  rw [wtI_incf, mul_right_comm, wtI_decf h]

omit [DecidableEq ι] in
theorem finite_levelI (N : ℕ) : {m : ι → ℕ | ∑ x, m x = N}.Finite := by
  have h : {f : ι → ℕ | ∀ x, f x ≤ N}.Finite := Set.Finite.pi' fun _ => Set.finite_Iic N
  refine h.subset fun m hm x => ?_
  have h1 : m x ≤ ∑ z, m z :=
    Finset.single_le_sum (f := m) (fun _ _ => Nat.zero_le _) (Finset.mem_univ x)
  have h2 : ∑ z, m z = N := hm
  omega

theorem homogeneous_one_eq_zero (hθ : 0 < θ) (hP : ∀ y x, 0 ≤ P y x) (hν : ∀ x, 0 < ν x)
    (hst : ∀ x, ∑ y, ν y * P y x = ν x) {h : (ι → ℕ) → F}
    (hbd : ∀ m : ι → ℕ, (∑ x, m x) ≤ 1 → h m = 0)
    (hrec : ∀ m : ι → ℕ, 2 ≤ ∑ x, m x →
      ((((∑ x, m x) * ((∑ x, m x) - 1) : ℕ) : F) + θ * ((∑ x, m x : ℕ) : F)) * h m
        = (∑ x, ((m x * (m x - 1) : ℕ) : F) * h (decf m x))
          + θ * ∑ x, ∑ y, P y x * ((m x : ℕ) : F) * h (incf (decf m x) y)) :
    ∀ m : ι → ℕ, h m = 0 := by
  suffices H : ∀ N : ℕ, ∀ m : ι → ℕ, ∑ x, m x = N → h m = 0 from fun m => H _ m rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IH =>
    intro m₁ hm₁
    rcases Nat.lt_or_ge N 2 with hlt | hge
    · exact hbd m₁ (by omega)
    obtain ⟨m₀, hm₀S, hm₀max⟩ :=
      Set.exists_max_image {m : ι → ℕ | ∑ x, m x = N} (fun m => |h m| / wtI ν m)
        (finite_levelI N) ⟨m₁, hm₁⟩
    have hm₀ : ∑ x, m₀ x = N := hm₀S
    set M : F := |h m₀| / wtI ν m₀ with hMdef
    have hW : 0 < wtI ν m₀ := wtI_pos hν m₀
    have hMnn : 0 ≤ M := div_nonneg (abs_nonneg _) hW.le
    have hMW : M * wtI ν m₀ = |h m₀| := by rw [hMdef]; field_simp
    have hmax : ∀ m : ι → ℕ, ∑ x, m x = N → |h m| ≤ M * wtI ν m :=
      fun m hm => (div_le_iff₀ (wtI_pos hν m)).mp (hm₀max m hm)
    have hcoal : (∑ x, ((m₀ x * (m₀ x - 1) : ℕ) : F) * h (decf m₀ x)) = 0 := by
      refine Finset.sum_eq_zero fun x _ => ?_
      by_cases hx : m₀ x = 0
      · rw [hx]; norm_num
      · have hlev : ∑ z, decf m₀ x z = N - 1 := by
          have := sum_decf (f := m₀) (i := x) hx
          omega
        rw [IH (N - 1) (by omega) (decf m₀ x) hlev, mul_zero]
    have heq := hrec m₀ (by omega)
    rw [hm₀, hcoal, zero_add] at heq
    have hmut : |∑ x, ∑ y, P y x * ((m₀ x : ℕ) : F) * h (incf (decf m₀ x) y)|
        ≤ ((N : ℕ) : F) * (M * wtI ν m₀) := by
      calc |∑ x, ∑ y, P y x * ((m₀ x : ℕ) : F) * h (incf (decf m₀ x) y)|
          ≤ ∑ x, ((m₀ x : ℕ) : F) * (M * wtI ν m₀) := by
            refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun x _ => ?_)
            refine mut_cell_bound hP hν hst x (m₀ x) ?_
            intro hx y
            have hlev : ∑ z, incf (decf m₀ x) y z = N := by
              have h2 := sum_decf (f := m₀) (i := x) hx
              have h3 := sum_incf (decf m₀ x) y
              omega
            have hle := hmax (incf (decf m₀ x) y) hlev
            calc |h (incf (decf m₀ x) y)| * ν x
                ≤ (M * wtI ν (incf (decf m₀ x) y)) * ν x :=
                  mul_le_mul_of_nonneg_right hle (hν x).le
              _ = M * (wtI ν (incf (decf m₀ x) y) * ν x) := by ring
              _ = M * (wtI ν m₀ * ν y) := by rw [wtI_incf_decf y hx]
        _ = ((N : ℕ) : F) * (M * wtI ν m₀) := by
            rw [← Finset.sum_mul, ← Nat.cast_sum, hm₀]
    have hD : (0 : F) < ((N * (N - 1) : ℕ) : F) + θ * ((N : ℕ) : F) := by
      have hc1 : (0 : F) ≤ ((N * (N - 1) : ℕ) : F) := Nat.cast_nonneg _
      have hc2 : (0 : F) < ((N : ℕ) : F) := by exact_mod_cast (by omega : 0 < N)
      nlinarith
    have hNN : (0 : F) < ((N * (N - 1) : ℕ) : F) := by
      have : 0 < N * (N - 1) := Nat.mul_pos (by omega) (by omega)
      exact_mod_cast this
    have hchain : (((N * (N - 1) : ℕ) : F) + θ * ((N : ℕ) : F)) * (M * wtI ν m₀)
        ≤ θ * (((N : ℕ) : F) * (M * wtI ν m₀)) := by
      have hstart : (((N * (N - 1) : ℕ) : F) + θ * ((N : ℕ) : F)) * (M * wtI ν m₀)
          = |(((N * (N - 1) : ℕ) : F) + θ * ((N : ℕ) : F)) * h m₀| := by
        rw [hMW, abs_mul, abs_of_pos hD]
      rw [hstart, heq, abs_mul, abs_of_pos hθ]
      exact mul_le_mul_of_nonneg_left hmut hθ.le
    have hM0 : M = 0 := by
      by_contra hne
      have hMpos : 0 < M := lt_of_le_of_ne hMnn (Ne.symm hne)
      nlinarith [hchain, hNN, hMpos, hW, mul_pos hMpos hW]
    have hle := hm₀max m₁ hm₁
    rw [hM0] at hle
    have hw1 : 0 < wtI ν m₁ := wtI_pos hν m₁
    have hfin : |h m₁| ≤ 0 := by
      have := (div_le_iff₀ hw1).mp hle
      linarith
    exact abs_eq_zero.mp (le_antisymm hfin (abs_nonneg _))

theorem IsSolutionOneG.unique (hθ : 0 < θ) (hP : ∀ y x, 0 ≤ P y x) (hν : ∀ x, 0 < ν x)
    (hst : ∀ x, ∑ y, ν y * P y x = ν x) {q₁ q₂ : (ι → ℕ) → F}
    (h₁ : IsSolutionOneG θ ν P q₁) (h₂ : IsSolutionOneG θ ν P q₂) : q₁ = q₂ := by
  have hbd : ∀ m : ι → ℕ, (∑ x, m x) ≤ 1 → q₁ m - q₂ m = 0 := by
    intro m hm
    rcases Nat.lt_or_ge (∑ x, m x) 1 with hlt | hge
    · have hz : m = fun _ => 0 := by
        funext x
        exact Finset.sum_eq_zero_iff.mp (by omega : ∑ z, m z = 0) x (Finset.mem_univ x)
      rw [hz, h₁.empty, h₂.empty, sub_self]
    · obtain ⟨x, rfl⟩ := Config.exists_incf_of_sum_eq_one (f := m) (by omega)
      rw [h₁.bdry, h₂.bdry, sub_self]
  have hrec : ∀ m : ι → ℕ, 2 ≤ ∑ x, m x →
      ((((∑ x, m x) * ((∑ x, m x) - 1) : ℕ) : F) + θ * ((∑ x, m x : ℕ) : F)) * (q₁ m - q₂ m)
        = (∑ x, ((m x * (m x - 1) : ℕ) : F) * (q₁ (decf m x) - q₂ (decf m x)))
          + θ * ∑ x, ∑ y, P y x * ((m x : ℕ) : F)
              * (q₁ (incf (decf m x) y) - q₂ (incf (decf m x) y)) := by
    intro m hm
    have e₁ := h₁.recursion m hm
    have e₂ := h₂.recursion m hm
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [e₁, e₂]
    ring
  funext m
  have := homogeneous_one_eq_zero (ν := ν) (P := P) hθ hP hν hst hbd hrec m
  linarith [this]

theorem IsSolutionOneG.isSolutionOneGen {K : ℕ} {νF : Fin K → F} {PF : Fin K → Fin K → F}
    (hν : ∑ x, νF x = 1) (hst : ∀ x, ∑ y, νF y * PF y x = νF x) {q : (Fin K → ℕ) → F}
    (hq : IsSolutionOneG θ νF PF q) : Biallelic.IsSolutionOneGen θ PF q where
  empty := hq.empty
  norm := by
    rw [Finset.sum_congr rfl fun x (_ : x ∈ Finset.univ) => hq.bdry x]
    exact hν
  recursion m := by
    have hconv : (∑ x, ∑ y, ((m x : ℕ) : F) * PF y x * q (incf (decf m x) y))
        = ∑ x, ∑ y, PF y x * ((m x : ℕ) : F) * q (incf (decf m x) y) :=
      Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
    rw [hconv]
    rcases Nat.lt_or_ge (∑ x, m x) 2 with hlt | hge
    · rcases Nat.lt_or_ge (∑ x, m x) 1 with h0 | h1
      · have hz : m = fun _ => 0 := by
          funext z
          exact Finset.sum_eq_zero_iff.mp (by omega : ∑ w, m w = 0) z (Finset.mem_univ z)
        subst hz
        simp
      · obtain ⟨x, rfl⟩ := Config.exists_incf_of_sum_eq_one (f := m) (by omega)
        have hs : ∑ z, incf (fun _ => (0 : ℕ)) x z = 1 := by rw [sum_incf]; simp
        have hd : decf (incf (fun _ => (0 : ℕ)) x) x = fun _ => 0 := by
          funext z
          by_cases hz : z = x
          · subst hz; rw [decf_self, incf_self]
          · rw [decf_of_ne _ hz, incf_of_ne _ hz]
        have hcoal : (∑ z, ((incf (fun _ => (0 : ℕ)) x z
            * (incf (fun _ => (0 : ℕ)) x z - 1) : ℕ) : F)
            * q (decf (incf (fun _ => 0) x) z)) = 0 := by
          refine Finset.sum_eq_zero fun z _ => ?_
          by_cases hz : z = x
          · subst hz; rw [incf_self]; norm_num
          · rw [incf_of_ne _ hz]; norm_num
        have hmut : (∑ z, ∑ y, PF y z * ((incf (fun _ => (0 : ℕ)) x z : ℕ) : F)
            * q (incf (decf (incf (fun _ => 0) x) z) y)) = νF x := by
          rw [Finset.sum_eq_single_of_mem x (Finset.mem_univ x)]
          · rw [hd, incf_self, ← hst x]
            refine Finset.sum_congr rfl fun y _ => ?_
            rw [hq.bdry y]
            push_cast
            ring
          · intro z _ hz
            rw [incf_of_ne _ hz]
            simp
        rw [hs, hcoal, hmut, hq.bdry x]
        push_cast
        ring
    · exact hq.recursion m hge

end Rhone.MarkovChain.GeneralMutation
