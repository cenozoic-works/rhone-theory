/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.Biallelic.OneLocus
public import Rhone.LinearAlgebra.Recursion.Finite

/-! # Well-posedness of the one-locus general-mutation-matrix system -/

@[expose] public section

namespace Rhone.MarkovChain.Biallelic

open Finset LinearAlgebra.Recursion

variable {K : ℕ} {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θ : F} {π : Fin K → F}

def wt (π : Fin K → F) (m : Fin K → ℕ) : F := ∏ i, π i ^ m i

theorem wt_pos (hπ : ∀ i, 0 < π i) (m : Fin K → ℕ) : 0 < wt π m :=
  Finset.prod_pos fun i _ => pow_pos (hπ i) _

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem wt_incf (π : Fin K → F) (m : Fin K → ℕ) (k : Fin K) :
    wt π (incf m k) = wt π m * π k := by
  have hsplit : ∀ g : Fin K → ℕ,
      (∏ i, π i ^ g i) = π k ^ g k * ∏ i ∈ Finset.univ.erase k, π i ^ g i :=
    fun g => (Finset.mul_prod_erase _ _ (Finset.mem_univ k)).symm
  have herase : ∀ i ∈ Finset.univ.erase k, π i ^ incf m k i = π i ^ m i := by
    intro i hi
    rw [incf_of_ne _ (Finset.mem_erase.mp hi).1]
  rw [wt, wt, hsplit (incf m k), hsplit m, Finset.prod_congr rfl herase, incf_self, pow_succ]
  ring

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem wt_decf {m : Fin K → ℕ} {i : Fin K} (h : m i ≠ 0) :
    wt π (decf m i) * π i = wt π m := by
  have hsplit : ∀ g : Fin K → ℕ,
      (∏ l, π l ^ g l) = π i ^ g i * ∏ l ∈ Finset.univ.erase i, π l ^ g l :=
    fun g => (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
  have herase : ∀ l ∈ Finset.univ.erase i, π l ^ decf m i l = π l ^ m l := by
    intro l hl
    rw [decf_of_ne _ (Finset.mem_erase.mp hl).1]
  obtain ⟨p, hp⟩ : ∃ p, m i = p + 1 := ⟨m i - 1, by omega⟩
  rw [wt, wt, hsplit (decf m i), hsplit m, Finset.prod_congr rfl herase, decf_self, hp]
  simp only [Nat.add_sub_cancel, pow_succ]
  ring

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem wt_incf_decf {m : Fin K → ℕ} {i : Fin K} (k : Fin K) (h : m i ≠ 0) :
    wt π (incf (decf m i) k) * π i = wt π m * π k := by
  rw [wt_incf, mul_right_comm, wt_decf h]

theorem finite_level (N : ℕ) : {m : Fin K → ℕ | ∑ i, m i = N}.Finite := by
  have h : {f : Fin K → ℕ | ∀ i, f i ≤ N}.Finite := Set.Finite.pi' fun _ => Set.finite_Iic N
  refine h.subset fun m hm i => ?_
  have h1 : m i ≤ ∑ j, m j :=
    Finset.single_le_sum (f := m) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have h2 : ∑ j, m j = N := hm
  omega

theorem homogeneous_eq_zero (hθ : 0 < θ) (hπpos : ∀ i, 0 < π i) (hπ : ∑ i, π i = 1)
    {h : (Fin K → ℕ) → F} (h0 : h (fun _ => 0) = 0)
    (h1 : ∑ i, h (incf (fun _ => 0) i) = 0)
    (hrec : ∀ m : Fin K → ℕ,
      ((((∑ k, m k) * ((∑ k, m k) - 1) : ℕ) : F) + θ * ((∑ k, m k : ℕ) : F)) * h m
        = (∑ i, ((m i * (m i - 1) : ℕ) : F) * h (decf m i))
          + θ * ∑ i, ∑ k, ((m i : ℕ) : F) * π i * h (incf (decf m i) k)) :
    ∀ m : Fin K → ℕ, h m = 0 := by
  suffices H : ∀ N : ℕ, ∀ m : Fin K → ℕ, ∑ i, m i = N → h m = 0 from fun m => H _ m rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IH =>
    intro m₁ hm₁
    rcases Nat.lt_or_ge N 2 with hlt | hge
    · rcases Nat.lt_or_ge N 1 with hz | ho
      · have : m₁ = fun _ => 0 := by
          funext i
          exact Finset.sum_eq_zero_iff.mp (hm₁.trans (by omega)) i (Finset.mem_univ i)
        rw [this, h0]
      · obtain ⟨i, rfl⟩ := Config.exists_incf_of_sum_eq_one (f := m₁) (by omega)
        have hr := hrec (incf (fun _ => 0) i)
        have hsum : ∑ k, incf (fun _ => (0 : ℕ)) i k = 1 := by simp [sum_incf]
        rw [hsum] at hr
        have hcoal : (∑ l, ((incf (fun _ => (0 : ℕ)) i l * (incf (fun _ => (0 : ℕ)) i l - 1) :
            ℕ) : F) * h (decf (incf (fun _ => 0) i) l)) = 0 := by
          refine Finset.sum_eq_zero fun l _ => ?_
          by_cases hl : l = i
          · subst hl; rw [incf_self]; norm_num
          · rw [incf_of_ne _ hl]; norm_num
        have hmut : (∑ l, ∑ k, ((incf (fun _ => (0 : ℕ)) i l : ℕ) : F) * π l
            * h (incf (decf (incf (fun _ => 0) i) l) k))
            = π i * ∑ k, h (incf (fun _ => 0) k) := by
          rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
          · have hd : decf (incf (fun _ => (0 : ℕ)) i) i = fun _ => 0 := by
              funext l
              by_cases hl : l = i
              · subst hl; rw [decf_self, incf_self]
              · rw [decf_of_ne _ hl, incf_of_ne _ hl]
            rw [incf_self, hd, Finset.mul_sum]
            exact Finset.sum_congr rfl fun k _ => by push_cast; ring
          · intro l _ hl
            rw [incf_of_ne _ hl]
            simp
        rw [hcoal, hmut] at hr
        rw [h1, mul_zero, mul_zero, zero_add] at hr
        norm_num at hr
        rcases hr with hr | hr
        · exact absurd hr hθ.ne'
        · exact hr
    obtain ⟨m₀, hm₀S, hm₀max⟩ :=
      Set.exists_max_image {m : Fin K → ℕ | ∑ i, m i = N} (fun m => |h m| / wt π m)
        (finite_level N) ⟨m₁, hm₁⟩
    have hm₀ : ∑ i, m₀ i = N := hm₀S
    set M : F := |h m₀| / wt π m₀ with hMdef
    have hwt₀ : 0 < wt π m₀ := wt_pos hπpos m₀
    have hMnn : 0 ≤ M := div_nonneg (abs_nonneg _) hwt₀.le
    have hcoal : (∑ i, ((m₀ i * (m₀ i - 1) : ℕ) : F) * h (decf m₀ i)) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases hi : m₀ i = 0
      · rw [hi]; norm_num
      · have hlev : ∑ k, decf m₀ i k = N - 1 := by
          have := sum_decf (f := m₀) (i := i) hi
          omega
        rw [IH (N - 1) (by omega) (decf m₀ i) hlev, mul_zero]
    have hr := hrec m₀
    rw [hm₀, hcoal, zero_add] at hr
    have hbound : ∀ (i : Fin K) (k : Fin K),
        |((m₀ i : ℕ) : F) * π i * h (incf (decf m₀ i) k)|
          ≤ ((m₀ i : ℕ) : F) * (M * (wt π m₀ * π k)) := by
      intro i k
      by_cases hi : m₀ i = 0
      · rw [hi]; norm_num
      have hlev : ∑ l, incf (decf m₀ i) k l = N := by
        have h2 := sum_decf (f := m₀) (i := i) hi
        have h3 := sum_incf (decf m₀ i) k
        omega
      have hz : |h (incf (decf m₀ i) k)| ≤ M * wt π (incf (decf m₀ i) k) := by
        have hlt : |h (incf (decf m₀ i) k)| / wt π (incf (decf m₀ i) k) ≤ M :=
          hm₀max _ (show ∑ l, incf (decf m₀ i) k l = N from hlev)
        have hw : 0 < wt π (incf (decf m₀ i) k) := wt_pos hπpos _
        rw [div_le_iff₀ hw] at hlt
        exact hlt
      have hwi := wt_incf_decf (π := π) (m := m₀) (i := i) k hi
      have hπi : 0 < π i := hπpos i
      have hcast : (0 : F) ≤ ((m₀ i : ℕ) : F) := Nat.cast_nonneg _
      calc |((m₀ i : ℕ) : F) * π i * h (incf (decf m₀ i) k)|
          = ((m₀ i : ℕ) : F) * π i * |h (incf (decf m₀ i) k)| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hcast, abs_of_nonneg hπi.le]
        _ ≤ ((m₀ i : ℕ) : F) * π i * (M * wt π (incf (decf m₀ i) k)) := by
            exact mul_le_mul_of_nonneg_left hz (by positivity)
        _ = ((m₀ i : ℕ) : F) * (M * (wt π (incf (decf m₀ i) k) * π i)) := by ring
        _ = ((m₀ i : ℕ) : F) * (M * (wt π m₀ * π k)) := by rw [hwi]
    have hsum : |∑ i, ∑ k, ((m₀ i : ℕ) : F) * π i * h (incf (decf m₀ i) k)|
        ≤ ((N : ℕ) : F) * (M * wt π m₀) := by
      calc |∑ i, ∑ k, ((m₀ i : ℕ) : F) * π i * h (incf (decf m₀ i) k)|
          ≤ ∑ i, |∑ k, ((m₀ i : ℕ) : F) * π i * h (incf (decf m₀ i) k)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, ∑ k, ((m₀ i : ℕ) : F) * (M * (wt π m₀ * π k)) := by
            refine Finset.sum_le_sum fun i _ => ?_
            exact le_trans (Finset.abs_sum_le_sum_abs _ _)
              (Finset.sum_le_sum fun k _ => hbound i k)
        _ = ((N : ℕ) : F) * (M * wt π m₀) := by
            have e1 : ∀ i : Fin K, (∑ k, ((m₀ i : ℕ) : F) * (M * (wt π m₀ * π k)))
                = ((m₀ i : ℕ) : F) * (M * wt π m₀) := by
              intro i
              rw [← Finset.mul_sum]
              have : (∑ k, M * (wt π m₀ * π k)) = M * wt π m₀ := by
                rw [← Finset.mul_sum, ← Finset.mul_sum, hπ, mul_one]
              rw [this]
            rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => e1 i, ← Finset.sum_mul,
              ← Nat.cast_sum, hm₀]
    have hlhs : (((N * (N - 1) : ℕ) : F) + θ * ((N : ℕ) : F)) * M * wt π m₀
        = |(((N * (N - 1) : ℕ) : F) + θ * ((N : ℕ) : F)) * h m₀| := by
      have hD : (0 : F) < ((N * (N - 1) : ℕ) : F) + θ * ((N : ℕ) : F) := by
        have hc1 : (0 : F) ≤ ((N * (N - 1) : ℕ) : F) := Nat.cast_nonneg _
        have hc2 : (0 : F) < ((N : ℕ) : F) := by exact_mod_cast (by omega : 0 < N)
        nlinarith
      rw [abs_mul, abs_of_pos hD, hMdef]
      field_simp
    have hchain : (((N * (N - 1) : ℕ) : F) + θ * ((N : ℕ) : F)) * M * wt π m₀
        ≤ θ * (((N : ℕ) : F) * (M * wt π m₀)) := by
      rw [hlhs, hr, abs_mul, abs_of_pos hθ]
      exact mul_le_mul_of_nonneg_left hsum hθ.le
    have hNN : (0 : F) < ((N * (N - 1) : ℕ) : F) := by
      have : 0 < N * (N - 1) := by
        have : 2 ≤ N := hge
        exact Nat.mul_pos (by omega) (by omega)
      exact_mod_cast this
    have hM0 : M = 0 := by
      by_contra hne
      have hMpos : 0 < M := lt_of_le_of_ne hMnn (Ne.symm hne)
      nlinarith [hchain, hNN, hMpos, hwt₀, mul_pos hMpos hwt₀]
    have hle : |h m₁| / wt π m₁ ≤ M := hm₀max m₁ hm₁
    rw [hM0] at hle
    have hw1 : 0 < wt π m₁ := wt_pos hπpos m₁
    have hfin : |h m₁| ≤ 0 := by
      have := (div_le_iff₀ hw1).mp hle
      linarith
    exact abs_eq_zero.mp (le_antisymm hfin (abs_nonneg _))

theorem IsSolutionOneGen.unique (hθ : 0 < θ) (hπpos : ∀ i, 0 < π i) (hπ : ∑ i, π i = 1)
    {q₁ q₂ : (Fin K → ℕ) → F} (h₁ : IsSolutionOneGen θ (fun _ j => π j) q₁)
    (h₂ : IsSolutionOneGen θ (fun _ j => π j) q₂) : q₁ = q₂ := by
  have key := homogeneous_eq_zero (θ := θ) (π := π) hθ hπpos hπ
    (h := fun m => q₁ m - q₂ m) (by rw [h₁.empty, h₂.empty, sub_self])
    (by
      simp only [Finset.sum_sub_distrib]
      rw [h₁.norm, h₂.norm, sub_self])
    (by
      intro m
      have e₁ := h₁.recursion m
      have e₂ := h₂.recursion m
      simp only [Finset.sum_sub_distrib, mul_sub]
      rw [e₁, e₂]
      ring)
  funext m
  have := key m
  linarith [this]

theorem biallelic_unique {u12 u21 : F} (h12 : 0 < u12) (h21 : 0 < u21)
    {q : (Fin 2 → ℕ) → F}
    (hq : IsSolutionOneGen (thetaOf u12 u21) (jump (thetaOf u12 u21) (rate2 u12 u21)) q) :
    q = qOne (thetaOf u12 u21) (piOf u12 u21) := by
  have h2 : (2 : F) ≠ 0 := by norm_num
  have hs : u12 + u21 ≠ 0 := by positivity
  have hpos : 0 < u12 + u21 := by linarith
  have hπpos : ∀ i, 0 < piOf u12 u21 i := by
    have key : ∀ i : Fin 2, 0 < piOf u12 u21 i := by
      rw [Fin.forall_fin_two, piOf_zero, piOf_one]
      exact ⟨div_pos h21 hpos, div_pos h12 hpos⟩
    exact key
  rw [jump_rate2 h2 hs] at hq
  exact IsSolutionOneGen.unique (thetaOf_pos h12.le h21.le hs) hπpos (sum_piOf hs) hq
    (qOne_isSolutionOneGen (thetaOf_pos h12.le h21.le hs) (sum_piOf hs))

end Rhone.MarkovChain.Biallelic
