/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.ChainIncrements
public import Rhone.Diffusion.PathModulus

/-! # Tightness of rescaled paths of harmonic functions of chains -/
set_option linter.style.longLine false

@[expose] public section

namespace Rhone

open MeasureTheory Filter Set Analysis MarkovChain
open scoped NNReal ENNReal

namespace MarkovChain.FinChain

variable {S : Type*} [Fintype S] [MeasurableSpace S] [DiscreteMeasurableSpace S] (C : FinChain S)

theorem measureReal_not_block_le {g : S → ℝ} (hg : C.IsHarmonic g)
    (hg01 : ∀ y, g y ∈ Set.Icc (0 : ℝ) 1) {v q : ℝ}
    (hv : ∀ y, C.expect (fun z => (g z - g y) ^ 2) y ≤ v)
    (hq : ∀ y, C.expect (fun z => (g z - g y) ^ 4) y ≤ q) (x : S) (b L : ℕ) {ε : ℝ}
    (hε : 0 < ε) :
    (C.pathLaw x).real {ω | ¬ ∀ i ≤ L, ∀ k ≤ b, |g (ω (i * b + k)) - g (ω (i * b))| ≤ ε} ≤
      (L + 1) * ((4 * (b : ℝ) ^ 2 * v ^ 2 + 3 * b * q) / ε ^ 4) := by
  have hsub : {ω : ℕ → S | ¬ ∀ i ≤ L, ∀ k ≤ b, |g (ω (i * b + k)) - g (ω (i * b))| ≤ ε} ⊆
      ⋃ i ∈ Finset.range (L + 1), {ω | ∃ k ≤ b, ε ≤ |incr g (i * b) k ω|} := by
    intro ω hω
    simp only [mem_ofPred_eq, not_forall, not_le] at hω
    obtain ⟨i, hi, k, hk, hlt⟩ := hω
    simp only [mem_iUnion, Finset.mem_range, mem_ofPred_eq]
    exact ⟨i, Nat.lt_succ_of_le hi, k, hk, hlt.le⟩
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans
    ((measureReal_biUnion_finset_le _ _).trans ?_)
  have hone : ∀ i ∈ Finset.range (L + 1),
      (C.pathLaw x).real {ω | ∃ k ≤ b, ε ≤ |incr g (i * b) k ω|} ≤
        (4 * (b : ℝ) ^ 2 * v ^ 2 + 3 * b * q) / ε ^ 4 := by
    intro i _
    refine (C.measureReal_exists_abs_incr_ge_le hg hg01 x (i * b) b hε).trans ?_
    gcongr
    exact C.integral_incr_pow_four_le hg hg01 hv hq x (i * b) b
  refine (Finset.sum_le_sum hone).trans ?_
  simp

end MarkovChain.FinChain

variable {Sₙ : ℕ → Type*} [∀ n, Fintype (Sₙ n)] [∀ n, MeasurableSpace (Sₙ n)]
  [∀ n, DiscreteMeasurableSpace (Sₙ n)]

theorem Diffusion.modulusAt_rescaledPath_of_nonpos (a : ℕ → ℝ) {τ : ℝ} (hτ : τ ≤ 0) (j : ℕ)
    (d : ℝ) :
    ModulusAt j d (Diffusion.rescaledPath τ a) := by
  intro s t _ _ _
  have hs : τ * s ≤ 0 := mul_nonpos_iff.2 (Or.inr ⟨hτ, NNReal.coe_nonneg s⟩)
  have ht : τ * t ≤ 0 := mul_nonpos_iff.2 (Or.inr ⟨hτ, NNReal.coe_nonneg t⟩)
  rw [Diffusion.rescaledPath_apply, Diffusion.rescaledPath_apply, Diffusion.interpolate_of_nonpos a
      hs,
    Diffusion.interpolate_of_nonpos a ht, dist_self]
  positivity

theorem Diffusion.block_bound_le {t d0 v q c e ρ K A : ℝ} {j b L : ℕ} (ht : 0 < t) (hd01 : d0 ≤ 1)
    (htd : 2 ≤ t * d0) (hbge : t * d0 ≤ b) (hblt : (b : ℝ) < t * d0 + 1)
    (hLlt : (L : ℝ) < t * ((j : ℝ) + 1) / b + 1) (hA : A = 2 * ((j : ℝ) + 1) + 4)
    (hq0 : 0 ≤ q) (htv : t * v = c) (htq : t * q = e) (hK : 0 < K)
    (hc : 8 * A * d0 * c ^ 2 ≤ ρ * K / 2) (he : 3 * A * e ≤ ρ * K / 2) :
    ((L : ℝ) + 1) * ((4 * (b : ℝ) ^ 2 * v ^ 2 + 3 * b * q) / K) ≤ ρ := by
  have hbpos : (0 : ℝ) < b := by linarith
  have hb2t : (b : ℝ) ≤ 2 * (t * d0) := by linarith
  have hj0 : (0 : ℝ) ≤ t * ((j : ℝ) + 1) := by positivity
  have htA : t * A = 2 * (t * ((j : ℝ) + 1)) + 4 * t := by rw [hA]; ring
  have htd1 : t * d0 ≤ t := mul_le_of_le_one_right ht.le hd01
  have hX : ((L : ℝ) + 1) * b ≤ t * A := by
    have h1 : ((L : ℝ) + 1) * b ≤ (t * ((j : ℝ) + 1) / b + 2) * b :=
      mul_le_mul_of_nonneg_right (by linarith) hbpos.le
    have h2 : (t * ((j : ℝ) + 1) / b + 2) * b = t * ((j : ℝ) + 1) + 2 * b := by
      field_simp
    linarith
  have hY : 4 * (b : ℝ) * v ^ 2 + 3 * q ≤ 4 * (2 * (t * d0)) * v ^ 2 + 3 * q := by
    have := mul_le_mul_of_nonneg_right hb2t (sq_nonneg v)
    linarith
  have hY0 : 0 ≤ 4 * (b : ℝ) * v ^ 2 + 3 * q := by positivity
  have hXY : (((L : ℝ) + 1) * b) * (4 * b * v ^ 2 + 3 * q) ≤
      (t * A) * (4 * (2 * (t * d0)) * v ^ 2 + 3 * q) :=
    mul_le_mul hX hY hY0 (by rw [htA]; positivity)
  have e2 : (t * A) * (4 * (2 * (t * d0)) * v ^ 2 + 3 * q) =
      8 * A * d0 * (t * v) ^ 2 + 3 * A * (t * q) := by ring
  rw [htv, htq] at e2
  have e1 : ((L : ℝ) + 1) * ((4 * (b : ℝ) ^ 2 * v ^ 2 + 3 * b * q) / K) =
      (((L : ℝ) + 1) * b) * (4 * b * v ^ 2 + 3 * q) / K := by ring
  rw [e1, div_le_iff₀ hK]
  linarith

theorem Diffusion.exists_modulusAt_of_moments (C : ∀ n, FinChain (Sₙ n)) (y : ∀ n, Sₙ n → ℝ)
    (τ : ℕ → ℝ) (x : ∀ n, Sₙ n) (hy : ∀ n, (C n).IsHarmonic (y n))
    (hy01 : ∀ n z, y n z ∈ Icc (0 : ℝ) 1) (hτ : Tendsto τ atTop atTop) (c : ℝ) (e : ℕ → ℝ)
    (hv : ∀ᶠ n in atTop, ∀ z, (C n).expect (fun w => (y n w - y n z) ^ 2) z ≤ c / τ n)
    (hq : ∀ᶠ n in atTop, ∀ z, (C n).expect (fun w => (y n w - y n z) ^ 4) z ≤ e n / τ n)
    (he : Tendsto e atTop (nhds 0)) (j : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ d > 0, ∀ n, (C n).pathLaw (x n)
      {ω | ¬ ModulusAt j d (Diffusion.rescaledPath (τ n) fun m => y n (ω m))} ≤ ENNReal.ofReal ρ :=
          by
  set ε : ℝ := 1 / (5 * ((j : ℝ) + 1)) with hε_def
  have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hε : 0 < ε := by positivity
  set K : ℝ := ε ^ 4 with hK_def
  have hK : 0 < K := by positivity
  set A : ℝ := 2 * ((j : ℝ) + 1) + 4 with hA_def
  have hA : 0 < A := by positivity
  set d0 : ℝ := min 1 (ρ * K / (16 * A * (c ^ 2 + 1))) with hd0_def
  have hd0 : 0 < d0 := lt_min one_pos (by positivity)
  have hd01 : d0 ≤ 1 := min_le_left _ _
  have hd0c : 8 * A * d0 * c ^ 2 ≤ ρ * K / 2 := by
    have h1 : d0 ≤ ρ * K / (16 * A * (c ^ 2 + 1)) := min_le_right _ _
    have h2 : 8 * A * d0 * c ^ 2 ≤ 8 * A * (ρ * K / (16 * A * (c ^ 2 + 1))) * c ^ 2 := by
      gcongr
    have h3 : 8 * A * (ρ * K / (16 * A * (c ^ 2 + 1))) * c ^ 2 =
        ρ * K / 2 * (c ^ 2 / (c ^ 2 + 1)) := by
      field_simp
      ring
    have h4 : c ^ 2 / (c ^ 2 + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    have h5 : 0 ≤ ρ * K / 2 := by positivity
    linarith [mul_le_of_le_one_right h5 h4]
  have hev := (hv.and hq).and ((hτ.eventually_ge_atTop (2 / d0)).and
    (he.eventually (gt_mem_nhds (show (0 : ℝ) < ρ * K / (6 * A) by positivity))))
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hev
  set M : ℝ := ∑ n ∈ Finset.range N0, |τ n| with hM_def
  have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set d : ℝ := min d0 (1 / (((j : ℝ) + 1) * (M + 1))) with hd_def
  refine ⟨d, lt_min hd0 (by positivity), fun n => ?_⟩
  rcases le_or_gt N0 n with hn | hn
  · obtain ⟨⟨hvn, hqn⟩, hτn, hen⟩ := hN0 n hn
    set t := τ n with ht_def
    have htd : 2 ≤ t * d0 := by
      have := (div_le_iff₀ hd0).1 hτn
      linarith
    have ht : 0 < t := by
      by_contra h
      push Not at h
      have := mul_nonpos_iff.2 (Or.inr ⟨h, hd0.le⟩)
      linarith
    set b : ℕ := ⌈t * d0⌉₊ with hb_def
    set L : ℕ := ⌈t * ((j : ℝ) + 1) / b⌉₊ with hL_def
    have hbge : t * d0 ≤ b := Nat.le_ceil _
    have hblt : (b : ℝ) < t * d0 + 1 := Nat.ceil_lt_add_one (by positivity)
    have hb2 : 2 ≤ b := by exact_mod_cast htd.trans hbge
    have hbpos : (0 : ℝ) < b := by linarith
    have hLge : t * ((j : ℝ) + 1) / b ≤ L := Nat.le_ceil _
    have hLlt : (L : ℝ) < t * ((j : ℝ) + 1) / b + 1 := Nat.ceil_lt_add_one (by positivity)
    have hLb_ge : t * ((j : ℝ) + 1) + 1 ≤ (((L + 1) * b : ℕ) : ℝ) := by
      have h1 := (div_le_iff₀ hbpos).1 hLge
      have h2 : (((L + 1) * b : ℕ) : ℝ) = (L : ℝ) * b + b := by push_cast; ring
      rw [h2]
      linarith
    have h5ε : 5 * ε ≤ 1 / ((j : ℝ) + 1) := by
      have h : 5 * ε = 1 / ((j : ℝ) + 1) := by
        rw [hε_def]
        field_simp
      exact h.le
    have hsub : {ω : ℕ → Sₙ n | ¬ ModulusAt j d (Diffusion.rescaledPath t fun m => y n (ω m))} ⊆
        {ω | ¬ ∀ i ≤ L, ∀ k ≤ b, |y n (ω (i * b + k)) - y n (ω (i * b))| ≤ ε} := by
      intro ω hω hblock
      exact hω ((Diffusion.modulusAt_rescaledPath_of_block ht.le hb2 hbge hLb_ge h5ε hblock).mono
        (min_le_left _ _))
    have hprob := (C n).measureReal_not_block_le (hy n) (hy01 n) hvn hqn (x n) b L hε
    have hq0 : 0 ≤ e n / t := by
      refine le_trans ?_ (hqn (x n))
      rw [FinChain.expect_apply]
      exact Finset.sum_nonneg fun z _ => mul_nonneg ((C n).nonneg _ z) (by positivity)
    have hct : t * (c / t) = c := by field_simp
    have het : t * (e n / t) = e n := by field_simp
    have i2 : 3 * A * e n ≤ ρ * K / 2 := by
      have := (lt_div_iff₀ (by positivity : (0 : ℝ) < 6 * A)).1 hen
      linarith
    have hbound := Diffusion.block_bound_le ht hd01 htd hbge hblt hLlt hA_def hq0 hct het hK hd0c i2
    calc (C n).pathLaw (x n) {ω | ¬ ModulusAt j d (Diffusion.rescaledPath t fun m => y n (ω m))}
        ≤ (C n).pathLaw (x n)
            {ω | ¬ ∀ i ≤ L, ∀ k ≤ b, |y n (ω (i * b + k)) - y n (ω (i * b))| ≤ ε} :=
          measure_mono hsub
      _ = ENNReal.ofReal (((C n).pathLaw (x n)).real
            {ω | ¬ ∀ i ≤ L, ∀ k ≤ b, |y n (ω (i * b + k)) - y n (ω (i * b))| ≤ ε}) :=
          (ofReal_measureReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal ρ := ENNReal.ofReal_le_ofReal (hprob.trans hbound)
  · have hall : ∀ ω : ℕ → Sₙ n, ModulusAt j d (Diffusion.rescaledPath (τ n) fun m => y n (ω m)) :=
      by
      intro ω
      rcases le_or_gt (τ n) 0 with hτn | hτn
      · exact Diffusion.modulusAt_rescaledPath_of_nonpos _ hτn j d
      · refine Diffusion.modulusAt_rescaledPath_of_step (fun m => ?_) hτn.le ?_
        · have h1 := hy01 n (ω (m + 1))
          have h2 := hy01 n (ω m)
          rw [abs_le]
          constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
        · have hτM : τ n ≤ M := by
            have := Finset.single_le_sum (f := fun k => |τ k|) (fun _ _ => abs_nonneg _)
              (Finset.mem_range.2 hn)
            exact (le_abs_self _).trans this
          have hdle : d ≤ 1 / (((j : ℝ) + 1) * (M + 1)) := min_le_right _ _
          calc τ n * d ≤ τ n * (1 / (((j : ℝ) + 1) * (M + 1))) := by gcongr
            _ ≤ 1 / ((j : ℝ) + 1) := by
                rw [mul_one_div, div_le_div_iff₀ (by positivity) hj1]
                nlinarith
    have hempty : {ω : ℕ → Sₙ n | ¬ ModulusAt j d (Diffusion.rescaledPath (τ n) fun m => y n (ω m))} =
        ∅ := by
      ext ω
      simp [hall ω]
    rw [hempty, measure_empty]
    exact zero_le

theorem Diffusion.exists_unitModulus_of_moments (C : ∀ n, FinChain (Sₙ n)) (y : ∀ n, Sₙ n → ℝ)
    (τ : ℕ → ℝ) (x : ∀ n, Sₙ n) (hy : ∀ n, (C n).IsHarmonic (y n))
    (hy01 : ∀ n z, y n z ∈ Icc (0 : ℝ) 1) (hτ : Tendsto τ atTop atTop) (c : ℝ) (e : ℕ → ℝ)
    (hv : ∀ᶠ n in atTop, ∀ z, (C n).expect (fun w => (y n w - y n z) ^ 2) z ≤ c / τ n)
    (hq : ∀ᶠ n in atTop, ∀ z, (C n).expect (fun w => (y n w - y n z) ^ 4) z ≤ e n / τ n)
    (he : Tendsto e atTop (nhds 0)) {η : ℝ≥0∞} (hη : η ≠ 0) :
    ∃ δ : ℕ → ℝ, (∀ j, 0 < δ j) ∧ ∀ n, (C n).pathLaw (x n)
      {ω | ¬ UnitModulus δ (Diffusion.rescaledPath (τ n) fun m => y n (ω m))} ≤ η := by
  obtain ⟨ρ, hρ, hρη⟩ := ENNReal.exists_pos_sum_of_countable hη ℕ
  have hj := fun j => Diffusion.exists_modulusAt_of_moments C y τ x hy hy01 hτ c e hv hq he j (hρ j)
  choose δ hδ hδn using hj
  refine ⟨δ, hδ, fun n => ?_⟩
  have hsub : {ω : ℕ → Sₙ n | ¬ UnitModulus δ (Diffusion.rescaledPath (τ n) fun m => y n (ω m))} ⊆
      ⋃ j, {ω | ¬ ModulusAt j (δ j) (Diffusion.rescaledPath (τ n) fun m => y n (ω m))} := by
    intro ω hω
    simp only [mem_ofPred_eq, mem_iUnion]
    by_contra h
    push Not at h
    exact hω ⟨fun t => Diffusion.rescaledPath_mem_Icc (fun m => hy01 n (ω m)) _ t, h⟩
  calc (C n).pathLaw (x n) {ω | ¬ UnitModulus δ (Diffusion.rescaledPath (τ n) fun m => y n (ω m))}
      ≤ ∑' j, (C n).pathLaw (x n)
          {ω | ¬ ModulusAt j (δ j) (Diffusion.rescaledPath (τ n) fun m => y n (ω m))} :=
        (measure_mono hsub).trans (measure_iUnion_le _)
    _ ≤ ∑' j, (ρ j : ℝ≥0∞) := by
        exact ENNReal.tsum_le_tsum fun j => (hδn j n).trans (le_of_eq ENNReal.ofReal_coe_nnreal)
    _ ≤ η := hρη.le

end Rhone
