/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.InfiniteAlleles.Rescale
public import Rhone.Probability.InfiniteAlleles.Boundary

/-! # Rescaled sampling probability converges to the parent-independent-mutation limit, `K → ∞` -/

@[expose] public section

namespace Rhone.Probability.InfiniteAlleles

open Finset Filter Topology LinearAlgebra.Recursion LinearAlgebra.Recursion.Config

variable {KA KB : ℕ}

section Low

variable {F : Type*} [CommRing F]

def lowIA (θA θB : F) (h : Config KA KB → F) (ξ : Config KA KB) : F :=
  (∑ i, ((ξ.coalA i : ℕ) : F) * h (ξ.dropA i))
    + (∑ j, ((ξ.coalB j : ℕ) : F) * h (ξ.dropB j))
    + (∑ i, ∑ j, ((ξ.coalC i j : ℕ) : F) * h (ξ.dropC i j))
    + θA * ∑ i, (((dropIndA ξ i : ℕ) : F) * h (ξ.dropA i)
        + ∑ j, ((killIndA ξ i j : ℕ) : F) * h (ξ.killA i j))
    + θB * ∑ j, (((dropIndB ξ j : ℕ) : F) * h (ξ.dropB j)
        + ∑ i, ((killIndB ξ i j : ℕ) : F) * h (ξ.killB i j))

theorem rhsIA_eq_lowIA_add (θA θB ρ : F) (h : Config KA KB → F) (ξ : Config KA KB) :
    rhsIA θA θB ρ h ξ = lowIA θA θB h ξ
      + ((∑ i, ∑ j, ((ξ.coalAB i j : ℕ) : F) * h (ξ.mergeAB i j))
        + ρ * ∑ i, ∑ j, ((ξ.c i j : ℕ) : F) * h (ξ.split i j)) := by
  simp only [rhsIA, lowIA]
  ring

end Low

section Bound

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] {θA θB ρ : F}

theorem level_abs_bound (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    {h : Config KA KB → F} {γ : F} {L : ℕ} (hγ : 0 ≤ γ)
    (hbd : ∀ ζ : Config KA KB, ζ.n ≤ 1 → h ζ = 0)
    (hrec : ∀ ζ : Config KA KB, 2 ≤ ζ.n → ζ.nA + ζ.nB = L →
      |diag θA θB ρ ζ * h ζ
        - ((∑ i, ∑ j, ((ζ.coalAB i j : ℕ) : F) * h (ζ.mergeAB i j))
          + ρ * ∑ i, ∑ j, ((ζ.c i j : ℕ) : F) * h (ζ.split i j))| ≤ γ) :
    ∀ ξ : Config KA KB, ξ.nA + ξ.nB = L → |h ξ| * (min θA θB * (L : F)) ≤ γ := by
  intro ξ hξ
  obtain ⟨ζ, hζS, hζmax⟩ :=
    Set.exists_max_image {ζ : Config KA KB | ζ.nA + ζ.nB = L} (fun ζ => |h ζ|)
      (Config.finite_level L) ⟨ξ, hξ⟩
  have hζlev : ζ.nA + ζ.nB = L := hζS
  have hle : |h ξ| ≤ |h ζ| := hζmax ξ hξ
  have hMnn : (0 : F) ≤ |h ζ| := abs_nonneg _
  have hminpos : (0 : F) < min θA θB := lt_min hθA hθB
  have hLnn : (0 : F) ≤ (L : F) := Nat.cast_nonneg _
  by_cases hn : ζ.n ≤ 1
  · have hz : h ζ = 0 := hbd ζ hn
    rw [hz, abs_zero] at hle
    have hzero : |h ξ| = 0 := le_antisymm hle (abs_nonneg _)
    rw [hzero, zero_mul]
    exact hγ
  · have hn2 : 2 ≤ ζ.n := by omega
    set M : F := |h ζ| with hMdef
    have hA : |∑ i, ∑ j, ((ζ.coalAB i j : ℕ) : F) * h (ζ.mergeAB i j)|
        ≤ ((2 * (ζ.sumA * ζ.sumB) : ℕ) : F) * M := by
      calc |∑ i, ∑ j, ((ζ.coalAB i j : ℕ) : F) * h (ζ.mergeAB i j)|
          ≤ ∑ i, |∑ j, ((ζ.coalAB i j : ℕ) : F) * h (ζ.mergeAB i j)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, ∑ j, ((ζ.coalAB i j : ℕ) : F) * M := by
            refine Finset.sum_le_sum fun i _ => ?_
            refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
            rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
            by_cases ha : ζ.a i = 0
            · rw [ζ.coalAB_eq_zero_left j ha]; simp
            by_cases hb : ζ.b j = 0
            · rw [ζ.coalAB_eq_zero_right i hb]; simp
            obtain ⟨e1, e2⟩ := ζ.mergeAB_same ha hb
            refine mul_le_mul_of_nonneg_left (hζmax _ ?_) (Nat.cast_nonneg _)
            change (ζ.mergeAB i j).nA + (ζ.mergeAB i j).nB = L
            omega
        _ = ((2 * (ζ.sumA * ζ.sumB) : ℕ) : F) * M := by
            rw [← ζ.sum_coalAB]
            push_cast
            simp [Finset.sum_mul]
    have hB : |∑ i, ∑ j, ((ζ.c i j : ℕ) : F) * h (ζ.split i j)| ≤ ((ζ.t : ℕ) : F) * M := by
      calc |∑ i, ∑ j, ((ζ.c i j : ℕ) : F) * h (ζ.split i j)|
          ≤ ∑ i, |∑ j, ((ζ.c i j : ℕ) : F) * h (ζ.split i j)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, ∑ j, ((ζ.c i j : ℕ) : F) * M := by
            refine Finset.sum_le_sum fun i _ => ?_
            refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
            rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
            by_cases hc : ζ.c i j = 0
            · rw [hc]; simp
            obtain ⟨e1, e2⟩ := ζ.split_same hc
            refine mul_le_mul_of_nonneg_left (hζmax _ ?_) (Nat.cast_nonneg _)
            change (ζ.split i j).nA + (ζ.split i j).nB = L
            omega
        _ = ((ζ.t : ℕ) : F) * M := by
            rw [← ζ.sum_c]
            push_cast
            simp [Finset.sum_mul]
    have hDpos : 0 < diag θA θB ρ ζ := diag_pos hθA hθB hρ (by omega)
    have hdefect := hrec ζ hn2 hζlev
    have hthin : |(∑ i, ∑ j, ((ζ.coalAB i j : ℕ) : F) * h (ζ.mergeAB i j))
        + ρ * ∑ i, ∑ j, ((ζ.c i j : ℕ) : F) * h (ζ.split i j)|
        ≤ ((2 * (ζ.sumA * ζ.sumB) : ℕ) : F) * M + ρ * (((ζ.t : ℕ) : F) * M) := by
      refine le_trans (abs_add_le _ _) ?_
      rw [abs_mul, abs_of_nonneg hρ]
      exact add_le_add hA (mul_le_mul_of_nonneg_left hB hρ)
    have hDM : diag θA θB ρ ζ * M
        ≤ ((2 * (ζ.sumA * ζ.sumB) : ℕ) : F) * M + ρ * (((ζ.t : ℕ) : F) * M) + γ := by
      have habs : diag θA θB ρ ζ * M = |diag θA θB ρ ζ * h ζ| := by
        rw [abs_mul, abs_of_pos hDpos]
      rw [habs]
      calc |diag θA θB ρ ζ * h ζ|
          ≤ |diag θA θB ρ ζ * h ζ
              - ((∑ i, ∑ j, ((ζ.coalAB i j : ℕ) : F) * h (ζ.mergeAB i j))
                + ρ * ∑ i, ∑ j, ((ζ.c i j : ℕ) : F) * h (ζ.split i j))|
            + |(∑ i, ∑ j, ((ζ.coalAB i j : ℕ) : F) * h (ζ.mergeAB i j))
                + ρ * ∑ i, ∑ j, ((ζ.c i j : ℕ) : F) * h (ζ.split i j)| := by
            simpa using abs_add_le
              (diag θA θB ρ ζ * h ζ
                - ((∑ i, ∑ j, ((ζ.coalAB i j : ℕ) : F) * h (ζ.mergeAB i j))
                  + ρ * ∑ i, ∑ j, ((ζ.c i j : ℕ) : F) * h (ζ.split i j)))
              ((∑ i, ∑ j, ((ζ.coalAB i j : ℕ) : F) * h (ζ.mergeAB i j))
                + ρ * ∑ i, ∑ j, ((ζ.c i j : ℕ) : F) * h (ζ.split i j))
        _ ≤ γ + (((2 * (ζ.sumA * ζ.sumB) : ℕ) : F) * M + ρ * (((ζ.t : ℕ) : F) * M)) :=
            add_le_add hdefect hthin
        _ = ((2 * (ζ.sumA * ζ.sumB) : ℕ) : F) * M + ρ * (((ζ.t : ℕ) : F) * M) + γ := by ring
    have hdexp : diag θA θB ρ ζ * M
        = ((ζ.n * (ζ.n - 1) : ℕ) : F) * M + θA * ((ζ.nA : ℕ) : F) * M
          + θB * ((ζ.nB : ℕ) : F) * M + ρ * (((ζ.t : ℕ) : F) * M) := by
      simp only [Rhone.LinearAlgebra.Recursion.diag]
      ring
    have hc1 : ((2 * (ζ.sumA * ζ.sumB) : ℕ) : F) ≤ ((ζ.n * (ζ.n - 1) : ℕ) : F) := by
      exact_mod_cast ζ.two_mul_sumA_mul_sumB_le
    have hc1M : ((2 * (ζ.sumA * ζ.sumB) : ℕ) : F) * M ≤ ((ζ.n * (ζ.n - 1) : ℕ) : F) * M :=
      mul_le_mul_of_nonneg_right hc1 hMnn
    have hminA : min θA θB * ((ζ.nA : ℕ) : F) ≤ θA * ((ζ.nA : ℕ) : F) :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _)
    have hminB : min θA θB * ((ζ.nB : ℕ) : F) ≤ θB * ((ζ.nB : ℕ) : F) :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg _)
    have hminAM : (min θA θB * ((ζ.nA : ℕ) : F)) * M ≤ (θA * ((ζ.nA : ℕ) : F)) * M :=
      mul_le_mul_of_nonneg_right hminA hMnn
    have hminBM : (min θA θB * ((ζ.nB : ℕ) : F)) * M ≤ (θB * ((ζ.nB : ℕ) : F)) * M :=
      mul_le_mul_of_nonneg_right hminB hMnn
    have hLcast : ((L : ℕ) : F) = ((ζ.nA : ℕ) : F) + ((ζ.nB : ℕ) : F) := by
      rw [← hζlev]; push_cast; ring
    have hstep : M * (min θA θB * (L : F)) ≤ γ := by
      rw [hLcast]
      nlinarith [hDM, hdexp, hc1M, hminAM, hminBM]
    have hfin : |h ξ| * (min θA θB * (L : F)) ≤ M * (min θA θB * (L : F)) :=
      mul_le_mul_of_nonneg_right hle (mul_nonneg hminpos.le hLnn)
    exact le_trans hfin hstep

end Bound

variable {θA θB ρ : ℝ}

noncomputable def Qresc (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (x : ℝ)
    (ξ : Config KA KB) : ℝ :=
  resc x (LinearAlgebra.Recursion.q (πA := fun _ => x) (πB := fun _ => x) hθA hθB hρ) ξ

theorem Qresc_boundary (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) {x : ℝ} (hx : x ≠ 0)
    (ζ : Config KA KB) (hn : ζ.n ≤ 1) : Qresc hθA hθB hρ x ζ = 1 :=
  resc_boundary hx (LinearAlgebra.Recursion.q_isSolution hθA hθB hρ) ζ hn

theorem Qresc_recursion (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) {x : ℝ} (hx : x ≠ 0)
    (ξ : Config KA KB) (hn : 2 ≤ ξ.n) :
    diag θA θB ρ ξ * Qresc hθA hθB hρ x ξ
      = rhsIA θA θB ρ (Qresc hθA hθB hρ x) ξ
        + x * (θA * errA (Qresc hθA hθB hρ x) ξ + θB * errB (Qresc hθA hθB hρ x) ξ) :=
  rescaled_recursion hx (LinearAlgebra.Recursion.q_isSolution hθA hθB hρ) ξ hn

theorem PIA_eq_one_of_n_le_one (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    {ζ : Config KA KB} (hn : ζ.n ≤ 1) : PIA hθA hθB hρ ζ = 1 := by
  rcases Nat.lt_or_ge ζ.n 1 with h0 | h0
  · have hz : ζ = 0 := ζ.eq_zero_of_n_eq_zero (by omega)
    subst hz
    exact (PIA_isSolutionIA hθA hθB hρ).empty
  · rcases ζ.exists_e_of_n_eq_one (by omega) with ⟨i, rfl⟩ | ⟨j, rfl⟩ | ⟨i, j, rfl⟩
    · exact (PIA_isSolutionIA hθA hθB hρ).bdryA i
    · exact (PIA_isSolutionIA hθA hθB hρ).bdryB j
    · exact PIA_eC hθA hθB hρ i j

theorem tendsto_Qresc (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (ξ : Config KA KB) :
    Tendsto (fun x : ℝ => Qresc hθA hθB hρ x ξ) (𝓝[>] (0 : ℝ))
      (𝓝 (PIA hθA hθB hρ ξ)) := by
  suffices H : ∀ L : ℕ, ∀ η : Config KA KB, η.nA + η.nB = L →
      Tendsto (fun x : ℝ => Qresc hθA hθB hρ x η) (𝓝[>] (0 : ℝ))
        (𝓝 (PIA hθA hθB hρ η)) from H _ ξ rfl
  intro L
  induction L using Nat.strong_induction_on with
  | _ L IH =>
    intro ξ hξ
    have IH' : ∀ η : Config KA KB, η.nA + η.nB < L →
        Tendsto (fun x : ℝ => Qresc hθA hθB hρ x η) (𝓝[>] (0 : ℝ))
          (𝓝 (PIA hθA hθB hρ η)) := fun η hη => IH _ hη η rfl
    have key : ∀ (w : ℝ) (η : Config KA KB), (w ≠ 0 → η.nA + η.nB < L) →
        Tendsto (fun x : ℝ => w * Qresc hθA hθB hρ x η) (𝓝[>] (0 : ℝ))
          (𝓝 (w * PIA hθA hθB hρ η)) := by
      intro w η hw
      by_cases h : w = 0
      · simp only [h, zero_mul]
        exact tendsto_const_nhds
      · exact (IH' η (hw h)).const_mul w
    have hxpos : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), (0 : ℝ) < x := self_mem_nhdsWithin
    by_cases hn : ξ.n ≤ 1
    · rw [PIA_eq_one_of_n_le_one hθA hθB hρ hn]
      refine Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [hxpos] with x hx
      exact (Qresc_boundary hθA hθB hρ (ne_of_gt hx) ξ hn).symm
    have hn2 : 2 ≤ ξ.n := by omega
    have hLevel : 2 ≤ L := by
      have := ξ.n_add_t
      omega
    have hLpos : (0 : ℝ) < (L : ℝ) := by
      have : (2 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hLevel
      linarith
    have hδpos : (0 : ℝ) < min θA θB * (L : ℝ) := mul_pos (lt_min hθA hθB) hLpos
    have hlow : ∀ ζ : Config KA KB, ζ.nA + ζ.nB = L →
        Tendsto (fun x : ℝ => lowIA θA θB (Qresc hθA hθB hρ x) ζ) (𝓝[>] (0 : ℝ))
          (𝓝 (lowIA θA θB (PIA hθA hθB hρ) ζ)) := by
      intro ζ hζ
      have hlvl : ∀ (w : ℝ) (η : Config KA KB), (w ≠ 0 → η.nA + η.nB < ζ.nA + ζ.nB) →
          Tendsto (fun x : ℝ => w * Qresc hθA hθB hρ x η) (𝓝[>] (0 : ℝ))
            (𝓝 (w * PIA hθA hθB hρ η)) := fun w η hw => key w η (fun h => hζ ▸ hw h)
      simp only [lowIA]
      refine Tendsto.add (Tendsto.add (Tendsto.add (Tendsto.add ?_ ?_) ?_) ?_) ?_
      · refine tendsto_finsetSum _ fun i _ => hlvl _ _ fun hw => ?_
        have h0 : ζ.coalA i ≠ 0 := fun hz => hw (by rw [hz]; simp)
        have ha : ζ.a i ≠ 0 := fun hz => h0 (ζ.coalA_eq_zero_of hz)
        obtain ⟨e1, e2⟩ := ζ.dropA_lt ha
        omega
      · refine tendsto_finsetSum _ fun j _ => hlvl _ _ fun hw => ?_
        have h0 : ζ.coalB j ≠ 0 := fun hz => hw (by rw [hz]; simp)
        have hb : ζ.b j ≠ 0 := fun hz => h0 (ζ.coalB_eq_zero_of hz)
        obtain ⟨e1, e2⟩ := ζ.dropB_lt hb
        omega
      · refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => hlvl _ _ ?_
        intro hw
        have h0 : ζ.coalC i j ≠ 0 := fun hz => hw (by rw [hz]; simp)
        have hc : ζ.c i j ≠ 0 := fun hz => h0 (ζ.coalC_eq_zero_of hz)
        obtain ⟨e1, e2⟩ := ζ.dropC_lt hc
        omega
      · refine Tendsto.const_mul _ (tendsto_finsetSum _ fun i _ => Tendsto.add ?_ ?_)
        · refine hlvl _ _ fun hw => ?_
          have h0 : dropIndA ζ i ≠ 0 := fun hz => hw (by rw [hz]; simp)
          have ha : ζ.a i ≠ 0 := fun hz => h0 (dropIndA_eq_zero_of ζ hz)
          obtain ⟨e1, e2⟩ := ζ.dropA_lt ha
          omega
        · refine tendsto_finsetSum _ fun j _ => hlvl _ _ fun hw => ?_
          have h0 : killIndA ζ i j ≠ 0 := fun hz => hw (by rw [hz]; simp)
          have hc : ζ.c i j ≠ 0 := fun hz => h0 (killIndA_eq_zero_of ζ hz)
          obtain ⟨e1, e2⟩ := ζ.killA_lt hc
          omega
      · refine Tendsto.const_mul _ (tendsto_finsetSum _ fun j _ => Tendsto.add ?_ ?_)
        · refine hlvl _ _ fun hw => ?_
          have h0 : dropIndB ζ j ≠ 0 := fun hz => hw (by rw [hz]; simp)
          have hb : ζ.b j ≠ 0 := fun hz => h0 (dropIndB_eq_zero_of ζ hz)
          obtain ⟨e1, e2⟩ := ζ.dropB_lt hb
          omega
        · refine tendsto_finsetSum _ fun i _ => hlvl _ _ fun hw => ?_
          have h0 : killIndB ζ i j ≠ 0 := fun hz => hw (by rw [hz]; simp)
          have hc : ζ.c i j ≠ 0 := fun hz => h0 (killIndB_eq_zero_of ζ hz)
          obtain ⟨e1, e2⟩ := ζ.killB_lt hc
          omega
    have herrA : ∀ ζ : Config KA KB, ζ.nA + ζ.nB = L →
        Tendsto (fun x : ℝ => errA (Qresc hθA hθB hρ x) ζ) (𝓝[>] (0 : ℝ))
          (𝓝 (errA (PIA hθA hθB hρ) ζ)) := by
      intro ζ hζ
      have hlvl : ∀ (w : ℝ) (η : Config KA KB), (w ≠ 0 → η.nA + η.nB < ζ.nA + ζ.nB) →
          Tendsto (fun x : ℝ => w * Qresc hθA hθB hρ x η) (𝓝[>] (0 : ℝ))
            (𝓝 (w * PIA hθA hθB hρ η)) := fun w η hw => key w η (fun h => hζ ▸ hw h)
      simp only [errA]
      refine tendsto_finsetSum _ fun i _ => ?_
      by_cases hm : ζ.mA i = 1
      · simp only [hm]
        exact tendsto_const_nhds
      · simp only [ite_eq_right hm]
        refine Tendsto.add (hlvl _ _ fun hw => ?_) (tendsto_finsetSum _ fun j _ =>
          hlvl _ _ fun hw => ?_)
        · have ha : ζ.a i ≠ 0 := fun hz => hw (by rw [hz]; simp)
          obtain ⟨e1, e2⟩ := ζ.dropA_lt ha
          omega
        · have hc : ζ.c i j ≠ 0 := fun hz => hw (by rw [hz]; simp)
          obtain ⟨e1, e2⟩ := ζ.killA_lt hc
          omega
    have herrB : ∀ ζ : Config KA KB, ζ.nA + ζ.nB = L →
        Tendsto (fun x : ℝ => errB (Qresc hθA hθB hρ x) ζ) (𝓝[>] (0 : ℝ))
          (𝓝 (errB (PIA hθA hθB hρ) ζ)) := by
      intro ζ hζ
      have hlvl : ∀ (w : ℝ) (η : Config KA KB), (w ≠ 0 → η.nA + η.nB < ζ.nA + ζ.nB) →
          Tendsto (fun x : ℝ => w * Qresc hθA hθB hρ x η) (𝓝[>] (0 : ℝ))
            (𝓝 (w * PIA hθA hθB hρ η)) := fun w η hw => key w η (fun h => hζ ▸ hw h)
      simp only [errB]
      refine tendsto_finsetSum _ fun j _ => ?_
      by_cases hm : ζ.mB j = 1
      · simp only [hm]
        exact tendsto_const_nhds
      · simp only [ite_eq_right hm]
        refine Tendsto.add (hlvl _ _ fun hw => ?_) (tendsto_finsetSum _ fun i _ =>
          hlvl _ _ fun hw => ?_)
        · have hb : ζ.b j ≠ 0 := fun hz => hw (by rw [hz]; simp)
          obtain ⟨e1, e2⟩ := ζ.dropB_lt hb
          omega
        · have hc : ζ.c i j ≠ 0 := fun hz => hw (by rw [hz]; simp)
          obtain ⟨e1, e2⟩ := ζ.killB_lt hc
          omega
    have hdef : ∀ ζ : Config KA KB, ζ.nA + ζ.nB = L → 2 ≤ ζ.n →
        Tendsto (fun x : ℝ =>
          diag θA θB ρ ζ * (Qresc hθA hθB hρ x ζ - PIA hθA hθB hρ ζ)
            - ((∑ i, ∑ j, ((ζ.coalAB i j : ℕ) : ℝ)
                  * (Qresc hθA hθB hρ x (ζ.mergeAB i j) - PIA hθA hθB hρ (ζ.mergeAB i j)))
              + ρ * ∑ i, ∑ j, ((ζ.c i j : ℕ) : ℝ)
                  * (Qresc hθA hθB hρ x (ζ.split i j) - PIA hθA hθB hρ (ζ.split i j))))
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      intro ζ hζ hζn
      have hid : ∀ x : ℝ, x ≠ 0 →
          diag θA θB ρ ζ * (Qresc hθA hθB hρ x ζ - PIA hθA hθB hρ ζ)
            - ((∑ i, ∑ j, ((ζ.coalAB i j : ℕ) : ℝ)
                  * (Qresc hθA hθB hρ x (ζ.mergeAB i j) - PIA hθA hθB hρ (ζ.mergeAB i j)))
              + ρ * ∑ i, ∑ j, ((ζ.c i j : ℕ) : ℝ)
                  * (Qresc hθA hθB hρ x (ζ.split i j) - PIA hθA hθB hρ (ζ.split i j)))
            = (lowIA θA θB (Qresc hθA hθB hρ x) ζ - lowIA θA θB (PIA hθA hθB hρ) ζ)
              + x * (θA * errA (Qresc hθA hθB hρ x) ζ + θB * errB (Qresc hθA hθB hρ x) ζ) := by
        intro x hx
        have h1 := Qresc_recursion hθA hθB hρ hx ζ hζn
        have h2 := (PIA_isSolutionIA hθA hθB hρ).recursion ζ (by omega)
        rw [rhsIA_eq_lowIA_add] at h1 h2
        simp only [lowIA] at h1 h2 ⊢
        simp only [mul_sub, Finset.sum_sub_distrib, sub_add_sub_comm]
        linarith [h1, h2]
      have hlim : Tendsto (fun x : ℝ =>
          (lowIA θA θB (Qresc hθA hθB hρ x) ζ - lowIA θA θB (PIA hθA hθB hρ) ζ)
            + x * (θA * errA (Qresc hθA hθB hρ x) ζ + θB * errB (Qresc hθA hθB hρ x) ζ))
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        have t1 : Tendsto (fun x : ℝ =>
            lowIA θA θB (Qresc hθA hθB hρ x) ζ - lowIA θA θB (PIA hθA hθB hρ) ζ)
            (𝓝[>] (0 : ℝ)) (𝓝 0) := by
          have := (hlow ζ hζ).sub (tendsto_const_nhds
            (x := lowIA θA θB (PIA hθA hθB hρ) ζ) (f := 𝓝[>] (0 : ℝ)))
          simpa using this
        have t0 : Tendsto (fun x : ℝ => x) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
          tendsto_id.mono_left nhdsWithin_le_nhds
        have t2 : Tendsto (fun x : ℝ =>
            x * (θA * errA (Qresc hθA hθB hρ x) ζ + θB * errB (Qresc hθA hθB hρ x) ζ))
            (𝓝[>] (0 : ℝ)) (𝓝 0) := by
          have := t0.mul (((herrA ζ hζ).const_mul θA).add ((herrB ζ hζ).const_mul θB))
          simpa using this
        simpa using t1.add t2
      refine Tendsto.congr' ?_ hlim
      filter_upwards [hxpos] with x hx
      exact (hid x (ne_of_gt hx)).symm
    rw [Metric.tendsto_nhds]
    intro ε hε
    set γ : ℝ := (ε / 2) * (min θA θB * (L : ℝ)) with hγdef
    have hγpos : 0 < γ := mul_pos (by linarith) hδpos
    set S : Finset (Config KA KB) :=
      (Config.finite_level (KA := KA) (KB := KB) L).toFinset.filter (fun ζ => 2 ≤ ζ.n) with hS
    have hall : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), ∀ ζ ∈ S,
        |diag θA θB ρ ζ * (Qresc hθA hθB hρ x ζ - PIA hθA hθB hρ ζ)
          - ((∑ i, ∑ j, ((ζ.coalAB i j : ℕ) : ℝ)
                * (Qresc hθA hθB hρ x (ζ.mergeAB i j) - PIA hθA hθB hρ (ζ.mergeAB i j)))
            + ρ * ∑ i, ∑ j, ((ζ.c i j : ℕ) : ℝ)
                * (Qresc hθA hθB hρ x (ζ.split i j) - PIA hθA hθB hρ (ζ.split i j)))| ≤ γ := by
      rw [Filter.eventually_all_finset]
      intro ζ hζS
      rw [hS, Finset.mem_filter, Set.Finite.mem_toFinset] at hζS
      have hlev : ζ.nA + ζ.nB = L := hζS.1
      have hn' : 2 ≤ ζ.n := hζS.2
      have := (hdef ζ hlev hn').abs
      have habs : Tendsto (fun x : ℝ =>
          |diag θA θB ρ ζ * (Qresc hθA hθB hρ x ζ - PIA hθA hθB hρ ζ)
            - ((∑ i, ∑ j, ((ζ.coalAB i j : ℕ) : ℝ)
                  * (Qresc hθA hθB hρ x (ζ.mergeAB i j) - PIA hθA hθB hρ (ζ.mergeAB i j)))
              + ρ * ∑ i, ∑ j, ((ζ.c i j : ℕ) : ℝ)
                  * (Qresc hθA hθB hρ x (ζ.split i j) - PIA hθA hθB hρ (ζ.split i j)))|)
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by simpa using this
      exact Filter.Tendsto.eventually_le_const hγpos habs
    filter_upwards [hall, hxpos] with x hx hxp
    have hxne : x ≠ 0 := ne_of_gt hxp
    have hbd : ∀ ζ : Config KA KB, ζ.n ≤ 1 →
        (fun η => Qresc hθA hθB hρ x η - PIA hθA hθB hρ η) ζ = 0 := by
      intro ζ hζ
      simp only
      rw [Qresc_boundary hθA hθB hρ hxne ζ hζ, PIA_eq_one_of_n_le_one hθA hθB hρ hζ, sub_self]
    have hrec : ∀ ζ : Config KA KB, 2 ≤ ζ.n → ζ.nA + ζ.nB = L →
        |diag θA θB ρ ζ * (Qresc hθA hθB hρ x ζ - PIA hθA hθB hρ ζ)
          - ((∑ i, ∑ j, ((ζ.coalAB i j : ℕ) : ℝ)
                * (Qresc hθA hθB hρ x (ζ.mergeAB i j) - PIA hθA hθB hρ (ζ.mergeAB i j)))
            + ρ * ∑ i, ∑ j, ((ζ.c i j : ℕ) : ℝ)
                * (Qresc hθA hθB hρ x (ζ.split i j) - PIA hθA hθB hρ (ζ.split i j)))| ≤ γ := by
      intro ζ hn' hlev
      refine hx ζ ?_
      rw [hS, Finset.mem_filter, Set.Finite.mem_toFinset]
      exact ⟨hlev, hn'⟩
    have hbound := level_abs_bound (h := fun η => Qresc hθA hθB hρ x η - PIA hθA hθB hρ η)
      hθA hθB hρ hγpos.le hbd hrec ξ hξ
    rw [Real.dist_eq]
    have hlt : |Qresc hθA hθB hρ x ξ - PIA hθA hθB hρ ξ| ≤ ε / 2 := by
      rw [hγdef] at hbound
      exact le_of_mul_le_mul_right (by linarith [hbound]) hδpos
    linarith

theorem tendsto_Qresc_nat (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (ξ : Config KA KB) :
    Tendsto (fun K : ℕ => Qresc hθA hθB hρ ((K : ℝ)⁻¹) ξ) atTop
      (𝓝 (PIA hθA hθB hρ ξ)) := by
  refine (tendsto_Qresc hθA hθB hρ ξ).comp ?_
  rw [tendsto_nhdsWithin_iff]
  constructor
  · exact tendsto_inv_atTop_nhds_zero_nat
  · filter_upwards [eventually_gt_atTop 0] with K hK
    simp only [Set.mem_Ioi, inv_pos]
    exact_mod_cast hK

theorem tendsto_Qresc_of_isSolutionIA (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    {q : Config KA KB → ℝ} (hq : IsSolutionIA θA θB ρ q) (ξ : Config KA KB) :
    Tendsto (fun K : ℕ => Qresc hθA hθB hρ ((K : ℝ)⁻¹) ξ) atTop (𝓝 (q ξ)) := by
  rw [congrFun (PIA_unique hθA hθB hρ hq) ξ]
  exact tendsto_Qresc_nat hθA hθB hρ ξ

end Rhone.Probability.InfiniteAlleles
