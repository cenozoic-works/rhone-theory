/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Diffusion.ChainDrift
public import Rhone.MarkovChain.StationaryLaw
public import Rhone.Diffusion.ChainPathLimit

/-!
# Limits of vector-valued chain paths with stationary starts

Source: ethier_kurtz1986, ch. 4, sec. 8, ch. 4, sec. 9. -/

@[expose] public section

namespace Rhone.Diffusion

open MeasureTheory Filter Topology Set MarkovChain Analysis Probability
open scoped NNReal BoundedContinuousFunction ENNReal

variable {G : Type*}

noncomputable def vint (a : ℕ → G → ℝ) (u : ℝ) : G → ℝ := fun i => interpolate (fun m => a m i) u

noncomputable def vecPath (τ : ℝ) (a : ℕ → G → ℝ) : C(ℝ≥0, G → ℝ) where
  toFun t := vint a (τ * t)
  continuous_toFun := continuous_pi fun i => (rescaledPath τ fun m => a m i).continuous

theorem vecPath_apply (τ : ℝ) (a : ℕ → G → ℝ) (t : ℝ≥0) : vecPath τ a t = vint a (τ * t) :=
  rfl

theorem continuous_vint (a : ℕ → G → ℝ) : Continuous (vint a) :=
  continuous_pi fun _ => continuous_interpolate _

def cube (G : Type*) : Set (G → ℝ) := Set.pi univ fun _ => Icc (0 : ℝ) 1

theorem isCompact_cube : IsCompact (cube G) := isCompact_univ_pi fun _ => isCompact_Icc

noncomputable def clampVec (x : G → ℝ) : G → ℝ := fun i => clampUnit (x i)

theorem continuous_clampVec : Continuous (clampVec (G := G)) :=
  continuous_pi fun i => continuous_clampUnit.comp (continuous_apply i)

theorem clampVec_mem (x : G → ℝ) : clampVec x ∈ cube G := fun i _ => clampUnit_mem (x i)

theorem clampVec_of_mem {x : G → ℝ} (hx : x ∈ cube G) : clampVec x = x :=
  funext fun i => clampUnit_of_mem (hx i (mem_univ i))

theorem vint_mem_cube {a : ℕ → G → ℝ} (ha : ∀ m, a m ∈ cube G) (u : ℝ) : vint a u ∈ cube G :=
  fun i _ => interpolate_mem_Icc (fun m => ha m i (mem_univ i)) u

theorem vint_mem {K : Set (G → ℝ)} (hK : Convex ℝ K) {a : ℕ → G → ℝ} (ha : ∀ m, a m ∈ K)
    (u : ℝ) : vint a u ∈ K := by
  rcases le_or_gt u 0 with hu | hu
  · have : vint a u = a 0 := funext fun i => interpolate_of_nonpos _ hu
    rw [this]
    exact ha 0
  · have hθ0 : 0 ≤ u - ⌊u⌋₊ := sub_nonneg.2 (Nat.floor_le hu.le)
    have hθ1 : u - ⌊u⌋₊ ≤ 1 := by linarith [Nat.lt_floor_add_one u]
    have e : vint a u = (1 - (u - ⌊u⌋₊)) • a ⌊u⌋₊ + (u - ⌊u⌋₊) • a (⌊u⌋₊ + 1) := by
      funext i
      simp only [vint, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [interpolate_eq_floor _ hu.le]
      ring
    rw [e]
    exact hK (ha _) (ha _) (by linarith) hθ0 (by ring)

variable [Fintype G]

theorem dist_vint_ceil_le {a : ℕ → G → ℝ} {η : ℝ} (hη : 0 ≤ η) {u : ℝ}
    (hstep : ∀ l < ⌈u⌉₊, dist (a (l + 1)) (a l) ≤ η) : dist (vint a u) (a ⌈u⌉₊) ≤ η := by
  refine (dist_pi_le_iff hη).2 fun i => ?_
  rw [Real.dist_eq]
  exact abs_interpolate_sub_ceil_le hη fun l hl => by
    have := (dist_le_pi_dist (a (l + 1)) (a l) i).trans (hstep l hl)
    rwa [Real.dist_eq] at this

theorem dist_vint_cell_le (a : ℕ → G → ℝ) {l : ℕ} {u : ℝ} (h1 : (l : ℝ) ≤ u)
    (h2 : u ≤ (l : ℝ) + 1) : dist (vint a u) (a l) ≤ dist (a (l + 1)) (a l) := by
  refine (dist_pi_le_iff dist_nonneg).2 fun i => ?_
  have hX := interpolate_add (fun m => a m i) l (θ := u - l) (by linarith) (by linarith)
  rw [show (l : ℝ) + (u - l) = u by ring] at hX
  rw [Real.dist_eq]
  change |interpolate (fun m => a m i) u - a l i| ≤ _
  rw [hX, add_sub_cancel_left, abs_mul]
  have hθ : |u - l| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  calc |u - l| * |a (l + 1) i - a l i| ≤ 1 * |a (l + 1) i - a l i| :=
        mul_le_mul_of_nonneg_right hθ (abs_nonneg _)
    _ = dist (a (l + 1) i) (a l i) := by rw [one_mul, Real.dist_eq]
    _ ≤ dist (a (l + 1)) (a l) := dist_le_pi_dist _ _ i

theorem abs_integral_cell_sub_le' {φ : ℝ → ℝ} (hφ : Continuous φ) {τ : ℝ} (hτ : 0 < τ) {l : ℕ}
    {b ε : ℝ} (hcell : ∀ u, (l : ℝ) / τ ≤ u → u ≤ ((l : ℝ) + 1) / τ → |φ u - b| ≤ ε) :
    |(∫ u in (l : ℝ) / τ..((l + 1 : ℕ) : ℝ) / τ, φ u) - b / τ| ≤ ε / τ := by
  have hlt : (l : ℝ) / τ ≤ ((l + 1 : ℕ) : ℝ) / τ := by
    push_cast
    exact div_le_div_of_nonneg_right (by linarith) hτ.le
  have hdiff : ((l + 1 : ℕ) : ℝ) / τ - (l : ℝ) / τ = 1 / τ := by
    rw [div_sub_div_same]
    push_cast
    ring_nf
  have hconst : ∫ _u in (l : ℝ) / τ..((l + 1 : ℕ) : ℝ) / τ, b = b / τ := by
    rw [intervalIntegral.integral_const, smul_eq_mul, hdiff, one_div_mul_eq_div]
  rw [← hconst, ← intervalIntegral.integral_sub (hφ.intervalIntegrable _ _)
    intervalIntegrable_const]
  have hb : |((l + 1 : ℕ) : ℝ) / τ - (l : ℝ) / τ| = 1 / τ := by
    rw [hdiff, abs_of_pos (one_div_pos.2 hτ)]
  have key := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (l : ℝ) / τ) (b := ((l + 1 : ℕ) : ℝ) / τ) (C := ε)
    (f := fun u => φ u - b) (fun u hu => ?_)
  · rw [Real.norm_eq_abs, hb] at key
    calc _ ≤ ε * (1 / τ) := key
      _ = ε / τ := by ring
  · rw [uIoc_of_le hlt] at hu
    rw [Real.norm_eq_abs]
    exact hcell u hu.1.le (by have := hu.2; push_cast at this; exact this)

theorem abs_integral_sub_riemann_le {φ : ℝ → ℝ} (hφ : Continuous φ) {b : ℕ → ℝ} {τ : ℝ}
    (hτ : 0 < τ) {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) {ε B : ℝ} (hB : ∀ u, |φ u| ≤ B)
    (hcell : ∀ l < ⌈τ * t⌉₊, ∀ u, (l : ℝ) / τ ≤ u → u ≤ ((l : ℝ) + 1) / τ → |φ u - b l| ≤ ε) :
    |(∫ u in s..t, φ u) - (∑ l ∈ Finset.Ico ⌈τ * s⌉₊ ⌈τ * t⌉₊, b l) / τ| ≤
      ((⌈τ * t⌉₊ : ℝ) - ⌈τ * s⌉₊) * ε / τ + 2 * B / τ := by
  set k := ⌈τ * s⌉₊ with hk
  set m := ⌈τ * t⌉₊ with hm
  have hτs : 0 ≤ τ * s := mul_nonneg hτ.le hs0
  have hτt : 0 ≤ τ * t := mul_nonneg hτ.le (hs0.trans hst)
  have hkm : k ≤ m := Nat.ceil_mono (mul_le_mul_of_nonneg_left hst hτ.le)
  have hk1 : τ * s ≤ k := Nat.le_ceil _
  have hk2 : (k : ℝ) < τ * s + 1 := Nat.ceil_lt_add_one hτs
  have hm1 : τ * t ≤ m := Nat.le_ceil _
  have hm2 : (m : ℝ) < τ * t + 1 := Nat.ceil_lt_add_one hτt
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
    (f := φ) (a := fun i : ℕ => ((k + i : ℕ) : ℝ) / τ) (n := m - k)
    (fun i _ => hφ.intervalIntegrable _ _)
  simp only [add_zero] at hsum
  have hblock : |(∫ u in (k : ℝ) / τ..((k + (m - k) : ℕ) : ℝ) / τ, φ u) -
      (∑ i ∈ Finset.range (m - k), b (k + i)) / τ| ≤ ((m - k : ℕ) : ℝ) * ε / τ := by
    rw [← hsum, Finset.sum_div, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i ∈ Finset.range (m - k), |(∫ u in ((k + i : ℕ) : ℝ) / τ..((k + (i + 1) : ℕ) : ℝ) / τ,
          φ u) - b (k + i) / τ|
        ≤ ∑ _i ∈ Finset.range (m - k), ε / τ := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' := Finset.mem_range.1 hi
          have h := abs_integral_cell_sub_le' hφ hτ (l := k + i) (b := b (k + i)) (ε := ε)
            (fun u hu1 hu2 => hcell (k + i) (by omega) u (by exact_mod_cast hu1)
              (by exact_mod_cast hu2))
          rwa [show k + (i + 1) = k + i + 1 by ring]
      _ = ((m - k : ℕ) : ℝ) * ε / τ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  rw [show k + (m - k) = m by omega] at hblock
  have hsumeq : ∑ l ∈ Finset.Ico k m, b l = ∑ i ∈ Finset.range (m - k), b (k + i) :=
    Finset.sum_Ico_eq_sum_range _ _ _
  have hcast : ((m - k : ℕ) : ℝ) = (m : ℝ) - k := Nat.cast_sub hkm
  have hbound : ∀ u, ‖φ u‖ ≤ B := fun u => by rw [Real.norm_eq_abs]; exact hB u
  have hleft := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := s) (b := (k : ℝ) / τ) (C := B) (f := φ) (fun u _ => hbound u)
  have hright := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (m : ℝ) / τ) (b := t) (C := B) (f := φ) (fun u _ => hbound u)
  have hl1 : |(k : ℝ) / τ - s| ≤ 1 / τ := by
    have e : (k : ℝ) / τ - s = ((k : ℝ) - τ * s) / τ := by field_simp
    rw [e, abs_div, abs_of_pos hτ, div_le_div_iff_of_pos_right hτ, abs_le]
    constructor <;> linarith
  have hr1 : |t - (m : ℝ) / τ| ≤ 1 / τ := by
    have e : t - (m : ℝ) / τ = (τ * t - m) / τ := by field_simp
    rw [e, abs_div, abs_of_pos hτ, div_le_div_iff_of_pos_right hτ, abs_le]
    constructor <;> linarith
  have hsplit : (∫ u in s..t, φ u) = (∫ u in s..(k : ℝ) / τ, φ u) +
      (∫ u in (k : ℝ) / τ..(m : ℝ) / τ, φ u) + (∫ u in (m : ℝ) / τ..t, φ u) := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hφ.intervalIntegrable _ _)
      (hφ.intervalIntegrable _ _),
      intervalIntegral.integral_add_adjacent_intervals (hφ.intervalIntegrable _ _)
      (hφ.intervalIntegrable _ _)]
  rw [Real.norm_eq_abs] at hleft hright
  rw [hsplit, hsumeq]
  rw [hcast] at hblock
  have hL : |∫ u in s..(k : ℝ) / τ, φ u| ≤ B / τ := by
    calc _ ≤ B * |(k : ℝ) / τ - s| := hleft
      _ ≤ B * (1 / τ) := mul_le_mul_of_nonneg_left hl1 hB0
      _ = B / τ := by ring
  have hR : |∫ u in (m : ℝ) / τ..t, φ u| ≤ B / τ := by
    calc _ ≤ B * |t - (m : ℝ) / τ| := hright
      _ ≤ B * (1 / τ) := mul_le_mul_of_nonneg_left hr1 hB0
      _ = B / τ := by ring
  have e : ∀ A B C D : ℝ, A + B + C - D = A + (B - D) + C := fun A B C D => by ring
  rw [e]
  refine (abs_add_three _ _ _).trans ?_
  have h2 : 2 * B / τ = B / τ + B / τ := by ring
  rw [h2]
  linarith

theorem abs_vec_defect_le {a : ℕ → G → ℝ} (ha : ∀ m, a m ∈ cube G) {τ : ℝ} (hτ : 1 ≤ τ)
    {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) {η ε Bg : ℝ} (hη : 0 ≤ η) (hε : 0 ≤ ε)
    {f g : (G → ℝ) → ℝ} (hgc : Continuous g) (hBg : ∀ x ∈ cube G, |g x| ≤ Bg)
    (hBgτ : 2 * Bg / τ ≤ ε)
    (hf : ∀ x ∈ cube G, ∀ y ∈ cube G, dist x y ≤ η → |f x - f y| ≤ ε)
    (hg : ∀ x ∈ cube G, ∀ y ∈ cube G, dist x y ≤ η → |g x - g y| ≤ ε)
    (hstep : ∀ l < ⌈τ * t⌉₊, dist (a (l + 1)) (a l) ≤ η) (err : ℕ → ℝ)
    (herr : ∀ l, |err l| ≤ ε) :
    |(f (vint a (τ * t)) - f (vint a (τ * s)) - ∫ u in s..t, g (vint a (τ * u))) -
      (f (a ⌈τ * t⌉₊) - f (a ⌈τ * s⌉₊) -
        ∑ l ∈ Finset.Ico ⌈τ * s⌉₊ ⌈τ * t⌉₊, (g (a l) + err l) / τ)| ≤ (2 * t + 5) * ε := by
  set k := ⌈τ * s⌉₊ with hk
  set m := ⌈τ * t⌉₊ with hm
  have hτ0 : 0 < τ := by linarith
  have ht0 : 0 ≤ t := hs0.trans hst
  have hτt : 0 ≤ τ * t := mul_nonneg hτ0.le ht0
  have hkm : k ≤ m := Nat.ceil_mono (mul_le_mul_of_nonneg_left hst hτ0.le)
  have hm2 : (m : ℝ) < τ * t + 1 := Nat.ceil_lt_add_one hτt
  have hk1 : τ * s ≤ k := Nat.le_ceil _
  have hmk : ((m : ℝ) - k) / τ ≤ t + 1 := by
    rw [div_le_iff₀ hτ0]
    have e : (t + 1) * τ = τ * t + τ := by ring
    have : τ * s ≥ 0 := mul_nonneg hτ0.le hs0
    linarith
  have hcard : ((Finset.Ico k m).card : ℝ) = (m : ℝ) - k := by
    rw [Nat.card_Ico, Nat.cast_sub hkm]
  have hsplit : ∑ l ∈ Finset.Ico k m, (g (a l) + err l) / τ =
      (∑ l ∈ Finset.Ico k m, g (a l)) / τ + (∑ l ∈ Finset.Ico k m, err l) / τ := by
    rw [← add_div, ← Finset.sum_add_distrib, Finset.sum_div]
  have hT4 : |(∑ l ∈ Finset.Ico k m, err l) / τ| ≤ (t + 1) * ε := by
    rw [abs_div, abs_of_pos hτ0]
    have h1 : |∑ l ∈ Finset.Ico k m, err l| ≤ ((m : ℝ) - k) * ε := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ l ∈ Finset.Ico k m, |err l| ≤ ∑ _l ∈ Finset.Ico k m, ε :=
            Finset.sum_le_sum fun l _ => herr l
        _ = ((m : ℝ) - k) * ε := by rw [Finset.sum_const, nsmul_eq_mul, hcard]
    calc |∑ l ∈ Finset.Ico k m, err l| / τ ≤ ((m : ℝ) - k) * ε / τ :=
          div_le_div_of_nonneg_right h1 hτ0.le
      _ = ((m : ℝ) - k) / τ * ε := by ring
      _ ≤ (t + 1) * ε := mul_le_mul_of_nonneg_right hmk hε
  have hXt := vint_mem_cube ha (τ * t)
  have hXs := vint_mem_cube ha (τ * s)
  rw [hsplit]
  have h1 : |f (vint a (τ * t)) - f (a m)| ≤ ε :=
    hf _ hXt _ (ha m) (dist_vint_ceil_le hη hstep)
  have h2 : |f (vint a (τ * s)) - f (a k)| ≤ ε :=
    hf _ hXs _ (ha k) (dist_vint_ceil_le hη fun l hl => hstep l (lt_of_lt_of_le hl hkm))
  have hφ : Continuous fun u => g (vint a (τ * u)) :=
    hgc.comp ((continuous_vint a).comp (continuous_const.mul continuous_id))
  have h3 := abs_integral_sub_riemann_le hφ (b := fun l => g (a l)) hτ0 hs0 hst
    (ε := ε) (B := Bg) (fun u => hBg _ (vint_mem_cube ha _))
    (fun l hl u hu1 hu2 => by
      refine hg _ (vint_mem_cube ha _) _ (ha l) ?_
      refine (dist_vint_cell_le a ?_ ?_).trans (hstep l hl)
      · rwa [div_le_iff₀' hτ0] at hu1
      · rwa [le_div_iff₀' hτ0] at hu2)
  have h3' : ((m : ℝ) - k) * ε / τ ≤ (t + 1) * ε := by
    rw [mul_div_right_comm]
    exact mul_le_mul_of_nonneg_right hmk hε
  have hT3 : |(∫ u in s..t, g (vint a (τ * u))) - (∑ l ∈ Finset.Ico k m, g (a l)) / τ| ≤
      (t + 1) * ε + ε := by linarith
  have e : (f (vint a (τ * t)) - f (vint a (τ * s)) - ∫ u in s..t, g (vint a (τ * u))) -
      (f (a m) - f (a k) - ((∑ l ∈ Finset.Ico k m, g (a l)) / τ +
        (∑ l ∈ Finset.Ico k m, err l) / τ)) =
      (f (vint a (τ * t)) - f (a m)) - (f (vint a (τ * s)) - f (a k)) -
        ((∫ u in s..t, g (vint a (τ * u))) - (∑ l ∈ Finset.Ico k m, g (a l)) / τ) +
        (∑ l ∈ Finset.Ico k m, err l) / τ := by ring
  rw [e]
  obtain ⟨a1, b1⟩ := abs_le.1 h1
  obtain ⟨a2, b2⟩ := abs_le.1 h2
  obtain ⟨a3, b3⟩ := abs_le.1 hT3
  obtain ⟨a4, b4⟩ := abs_le.1 hT4
  rw [abs_le]
  constructor <;> linarith

noncomputable def vecTest (f g : (G → ℝ) → ℝ) (s t : ℝ≥0) {k : ℕ} (r : Fin k → ℝ≥0)
    (h : (Fin k → G → ℝ) →ᵇ ℝ) (w : C(ℝ≥0, G → ℝ)) : ℝ :=
  (f (clampVec (w t)) - f (clampVec (w s)) -
    ∫ u in (s : ℝ)..t, g (clampVec (w u.toNNReal))) * h (fun j => w (r j))

omit [Fintype G] in
theorem continuous_vecTest {f g : (G → ℝ) → ℝ} (hf : Continuous f) (hg : Continuous g)
    (s t : ℝ≥0) {k : ℕ} (r : Fin k → ℝ≥0) (h : (Fin k → G → ℝ) →ᵇ ℝ) :
    Continuous (vecTest f g s t r h) := by
  unfold vecTest
  have hev : ∀ v : ℝ≥0, Continuous fun w : C(ℝ≥0, G → ℝ) => w v :=
    fun v => continuous_eval_const v
  have hjoint : Continuous fun p : C(ℝ≥0, G → ℝ) × ℝ => g (clampVec (p.1 p.2.toNNReal)) :=
    hg.comp (continuous_clampVec.comp (continuous_eval.comp
      (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))))
  have hint : Continuous fun w : C(ℝ≥0, G → ℝ) =>
      ∫ u in (s : ℝ)..t, g (clampVec (w u.toNNReal)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (w : C(ℝ≥0, G → ℝ)) (u : ℝ) => g (clampVec (w u.toNNReal))) hjoint _ _
  refine (((hf.comp (continuous_clampVec.comp (hev t))).sub
    (hf.comp (continuous_clampVec.comp (hev s)))).sub hint).mul ?_
  exact h.continuous.comp (continuous_pi fun j => hev (r j))

omit [Fintype G] in
theorem exists_bound_vecTest {f g : (G → ℝ) → ℝ} (hf : Continuous f) (hg : Continuous g)
    (s t : ℝ≥0) {k : ℕ} (r : Fin k → ℝ≥0) (h : (Fin k → G → ℝ) →ᵇ ℝ) :
    ∃ B, ∀ w, ‖vecTest f g s t r h w‖ ≤ B := by
  obtain ⟨Bf, hBf⟩ := isCompact_cube.exists_bound_of_continuousOn (hf.continuousOn (s := cube G))
  obtain ⟨Bg, hBg⟩ := isCompact_cube.exists_bound_of_continuousOn (hg.continuousOn (s := cube G))
  refine ⟨(2 * Bf + Bg * |(t : ℝ) - s|) * ‖h‖, fun w => ?_⟩
  unfold vecTest
  rw [norm_mul]
  refine mul_le_mul ?_ (h.norm_coe_le_norm _) (norm_nonneg _) ?_
  · have hi := intervalIntegral.norm_integral_le_of_norm_le_const (a := (s : ℝ)) (b := t)
      (C := Bg) (f := fun u => g (clampVec (w u.toNNReal))) (fun u _ => hBg _ (clampVec_mem _))
    have h1 := hBf _ (clampVec_mem (w t))
    have h2 := hBf _ (clampVec_mem (w s))
    calc _ ≤ ‖f (clampVec (w t))‖ + ‖f (clampVec (w s))‖ +
          ‖∫ u in (s : ℝ)..t, g (clampVec (w u.toNNReal))‖ :=
        (norm_sub_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
      _ ≤ 2 * Bf + Bg * |(t : ℝ) - s| := by linarith
  · have h0 := (norm_nonneg _).trans (hBf _ (clampVec_mem 0))
    have h1 := (norm_nonneg _).trans (hBg _ (clampVec_mem 0))
    positivity

noncomputable def vecTestBCF {f g : (G → ℝ) → ℝ} (hf : Continuous f) (hg : Continuous g)
    (s t : ℝ≥0) {k : ℕ} (r : Fin k → ℝ≥0) (h : (Fin k → G → ℝ) →ᵇ ℝ) :
    C(ℝ≥0, G → ℝ) →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (vecTest f g s t r h)
    (continuous_vecTest hf hg s t r h) _ (exists_bound_vecTest hf hg s t r h).choose_spec

omit [Fintype G] in
theorem vecTestBCF_apply {f g : (G → ℝ) → ℝ} (hf : Continuous f) (hg : Continuous g)
    (s t : ℝ≥0) {k : ℕ} (r : Fin k → ℝ≥0) (h : (Fin k → G → ℝ) →ᵇ ℝ) (w : C(ℝ≥0, G → ℝ)) :
    vecTestBCF hf hg s t r h w = vecTest f g s t r h w := rfl

omit [Fintype G] in
theorem vecTest_vecPath (f g : (G → ℝ) → ℝ) (s t : ℝ≥0) {k : ℕ} (r : Fin k → ℝ≥0)
    (h : (Fin k → G → ℝ) →ᵇ ℝ) {a : ℕ → G → ℝ} (ha : ∀ m, a m ∈ cube G) (τ : ℝ) :
    vecTest f g s t r h (vecPath τ a) =
      (f (vint a (τ * t)) - f (vint a (τ * s)) - ∫ u in (s : ℝ)..t, g (vint a (τ * u))) *
        h (fun j => vint a (τ * r j)) := by
  have hc : ∀ u, clampVec (vint a u) = vint a u := fun u => clampVec_of_mem (vint_mem_cube ha u)
  unfold vecTest
  simp only [vecPath_apply, hc]
  congr 2
  refine intervalIntegral.integral_congr fun u hu => ?_
  have hu0 : 0 ≤ u := (le_min s.2 t.2).trans hu.1
  simp only [Real.coe_toNNReal u hu0]

section Chains

variable {S : Type*} [Fintype S] [MeasurableSpace S] [DiscreteMeasurableSpace S]

theorem ae_transition_ne_zero (C : FinChain S) (x : S) :
    ∀ᵐ ω ∂C.pathLaw x, ∀ l, C.P (ω l) (ω (l + 1)) ≠ 0 := by
  classical
  refine ae_all_iff.2 fun l => ?_
  set F : S → S → ℝ := fun y z => if C.P y z = 0 then 1 else 0 with hF
  have h1 := C.integral_mul_eval_succ_two x l F (h := fun _ => 1) stronglyMeasurable_const
    (B := 1) (fun _ => by simp)
  have h0 : ∀ y, C.expect (F y) y = 0 := fun y => by
    rw [FinChain.expect_apply]
    exact Finset.sum_eq_zero fun z _ => by by_cases hz : C.P y z = 0 <;> simp [F, hz]
  simp only [one_mul, h0, integral_zero] at h1
  have hint : Integrable (fun ω : ℕ → S => F (ω l) (ω (l + 1))) (C.pathLaw x) :=
    C.integrable_three x (fun a b _ => F a b) l (l + 1) 0
  have hnn : 0 ≤ fun ω : ℕ → S => F (ω l) (ω (l + 1)) := fun ω => by
    by_cases hz : C.P (ω l) (ω (l + 1)) = 0 <;> simp [F, hz]
  rw [integral_eq_zero_iff_of_nonneg hnn hint] at h1
  filter_upwards [h1] with ω hω
  intro hz
  simp [F, hz] at hω

omit [Fintype G] [Fintype S] in
theorem measurable_vecPath [Finite G] (Y : S → G → ℝ) (τ : ℝ) :
    Measurable fun ω : ℕ → S => vecPath τ fun m => Y (ω m) :=
  ContinuousMap.measurable_iff_eval.2 fun _ =>
    measurable_pi_iff.2 fun i => measurable_interpolate (fun z => Y z i) _

end Chains

variable {Sₙ : ℕ → Type*} [∀ n, Fintype (Sₙ n)] [∀ n, MeasurableSpace (Sₙ n)]
  [∀ n, DiscreteMeasurableSpace (Sₙ n)]

theorem eventually_abs_integral_vecTest_le (C : ∀ n, FinChain (Sₙ n))
    (Y : ∀ n, Sₙ n → G → ℝ) (τ : ℕ → ℝ) (hY : ∀ n z, Y n z ∈ cube G)
    (hτ : Tendsto τ atTop atTop) (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hstep : ∀ᶠ n in atTop, ∀ z z', (C n).P z z' ≠ 0 → dist (Y n z') (Y n z) ≤ δ n)
    {F AF : (G → ℝ) → ℝ} (hF : Continuous F) (hAF : Continuous AF)
    (hgen : ∀ ε > 0, ∀ᶠ n in atTop, ∀ z,
      |τ n * ((C n).expect (F ∘ Y n) z - F (Y n z)) - AF (Y n z)| ≤ ε)
    {s t : ℝ≥0} (hst : s ≤ t) {k : ℕ} (r : Fin k → ℝ≥0) (hr : ∀ j, r j ≤ s)
    (h : (Fin k → G → ℝ) →ᵇ ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ x : Sₙ n, |∫ ω, vecTest F AF s t r h (vecPath (τ n) fun m => Y n (ω m))
      ∂(C n).pathLaw x| ≤ ‖h‖ * ((2 * t + 5) * ε) := by
  obtain ⟨Bg, hBg'⟩ := isCompact_cube.exists_bound_of_continuousOn
    (hAF.continuousOn (s := cube G))
  have hBg : ∀ z ∈ cube G, |AF z| ≤ Bg := fun z hz => by
    rw [← Real.norm_eq_abs]; exact hBg' z hz
  have hfu := isCompact_cube.uniformContinuousOn_of_continuous (hF.continuousOn (s := cube G))
  have hgu := isCompact_cube.uniformContinuousOn_of_continuous (hAF.continuousOn (s := cube G))
  rw [Metric.uniformContinuousOn_iff_le] at hfu hgu
  obtain ⟨η1, hη1, hf1⟩ := hfu ε hε
  obtain ⟨η2, hη2, hg2⟩ := hgu ε hε
  set η := min η1 η2 with hη_def
  have hη : 0 < η := lt_min hη1 hη2
  have hfη : ∀ z ∈ cube G, ∀ w ∈ cube G, dist z w ≤ η → |F z - F w| ≤ ε :=
    fun z hz w hw hzw => by
      have := hf1 z hz w hw (hzw.trans (min_le_left _ _))
      rwa [Real.dist_eq] at this
  have hgη : ∀ z ∈ cube G, ∀ w ∈ cube G, dist z w ≤ η → |AF z - AF w| ≤ ε :=
    fun z hz w hw hzw => by
      have := hg2 z hz w hw (hzw.trans (min_le_right _ _))
      rwa [Real.dist_eq] at this
  obtain ⟨B, hB⟩ := exists_bound_vecTest hF hAF s t r h
  filter_upwards [hτ.eventually_ge_atTop 1, hτ.eventually_ge_atTop (2 * Bg / ε), hgen ε hε,
    hstep, hδ.eventually (ge_mem_nhds hη)] with n h1 h2 h3 h4 h5 x
  have hτ0 : 0 < τ n := by linarith
  have hBgτ : 2 * Bg / τ n ≤ ε := by
    rw [div_le_iff₀ hτ0]
    have := (div_le_iff₀ hε).1 h2
    linarith
  set k0 := ⌈τ n * s⌉₊ with hk0
  set mt := ⌈τ n * t⌉₊ with hmt
  have hkm : k0 ≤ mt := Nat.ceil_mono (mul_le_mul_of_nonneg_left (by exact_mod_cast hst) hτ0.le)
  have hu : ∀ j, τ n * (r j : ℝ) ≤ k0 := fun j =>
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hr j) hτ0.le).trans (Nat.le_ceil _)
  set H : (ℕ → Sₙ n) → ℝ := fun ω => h (fun j => vint (fun l => Y n (ω l)) (τ n * r j))
    with hH_def
  have hHv : Measurable[Filtration.piLE (X := fun _ : ℕ => Sₙ n) k0]
      fun ω : ℕ → Sₙ n => fun j => vint (fun l => Y n (ω l)) (τ n * r j) := by
    let _ : MeasurableSpace (ℕ → Sₙ n) := Filtration.piLE (X := fun _ : ℕ => Sₙ n) k0
    exact Measurable.of_eval fun j => Measurable.of_eval fun i =>
      measurable_interpolate_piLE (fun z => Y n z i) (hu j)
  have hHm : StronglyMeasurable[Filtration.piLE (X := fun _ : ℕ => Sₙ n) k0] H :=
    (h.continuous.measurable.comp hHv).stronglyMeasurable
  have hHmeas : Measurable H := hHm.measurable.mono (Filtration.piLE.le _) le_rfl
  have hHB : ∀ ω, |H ω| ≤ ‖h‖ := fun ω => by
    rw [← Real.norm_eq_abs]
    exact h.norm_coe_le_norm _
  have hD0 := (C n).integral_mul_dynkin x (F ∘ Y n) hHm hHB mt hkm
  have hDint := (C n).integrable_mul_dynkin x (F ∘ Y n) k0 hHmeas hHB mt
  have hMint : Integrable (fun ω : ℕ → Sₙ n => vecTest F AF s t r h
      (vecPath (τ n) fun m => Y n (ω m))) ((C n).pathLaw x) :=
    Integrable.of_bound (((continuous_vecTest hF hAF s t r h).measurable.comp
      (measurable_vecPath (Y n) (τ n))).aestronglyMeasurable) B
      (Eventually.of_forall fun ω => hB _)
  set err : Sₙ n → ℝ := fun z => τ n * ((C n).expect (F ∘ Y n) z - F (Y n z)) - AF (Y n z)
    with herr_def
  have hgen' : ∀ z, (C n).expect (F ∘ Y n) z - (F ∘ Y n) z = (AF (Y n z) + err z) / τ n := by
    intro z
    rw [eq_div_iff hτ0.ne']
    simp only [herr_def, Function.comp_apply]
    ring
  have hpt : ∀ᵐ ω ∂(C n).pathLaw x, |vecTest F AF s t r h (vecPath (τ n) fun m => Y n (ω m)) -
      H ω * ((F ∘ Y n) (ω mt) - (F ∘ Y n) (ω k0) -
        ∑ l ∈ Finset.Ico k0 mt, ((C n).expect (F ∘ Y n) (ω l) - (F ∘ Y n) (ω l)))| ≤
      ‖h‖ * ((2 * t + 5) * ε) := by
    filter_upwards [ae_transition_ne_zero (C n) x] with ω hω
    have ha : ∀ l, (fun l => Y n (ω l)) l ∈ cube G := fun l => hY n (ω l)
    rw [vecTest_vecPath F AF s t r h ha (τ n)]
    have hdef := abs_vec_defect_le ha h1 (s := s) (t := t) (NNReal.coe_nonneg s)
      (by exact_mod_cast hst) hη.le hε.le hAF hBg hBgτ hfη hgη
      (fun l _ => (h4 _ _ (hω l)).trans h5) (fun l => err (ω l)) (fun l => h3 (ω l))
    have hs : ∑ l ∈ Finset.Ico k0 mt, ((C n).expect (F ∘ Y n) (ω l) - (F ∘ Y n) (ω l)) =
        ∑ l ∈ Finset.Ico k0 mt, (AF (Y n (ω l)) + err (ω l)) / τ n :=
      Finset.sum_congr rfl fun l _ => hgen' (ω l)
    rw [hs]
    simp only [Function.comp_apply]
    have e : ∀ P Q : ℝ, P * H ω - H ω * Q = H ω * (P - Q) := fun P Q => by ring
    rw [e, abs_mul]
    exact mul_le_mul (hHB ω) hdef (abs_nonneg _) (norm_nonneg _)
  have hdiff : ∫ ω, vecTest F AF s t r h (vecPath (τ n) fun m => Y n (ω m)) ∂(C n).pathLaw x =
      ∫ ω, (vecTest F AF s t r h (vecPath (τ n) fun m => Y n (ω m)) -
        H ω * ((F ∘ Y n) (ω mt) - (F ∘ Y n) (ω k0) -
          ∑ l ∈ Finset.Ico k0 mt, ((C n).expect (F ∘ Y n) (ω l) - (F ∘ Y n) (ω l))))
        ∂(C n).pathLaw x := by
    rw [integral_sub hMint hDint, hD0, sub_zero]
  rw [hdiff]
  calc _ ≤ ∫ ω, |vecTest F AF s t r h (vecPath (τ n) fun m => Y n (ω m)) -
        H ω * ((F ∘ Y n) (ω mt) - (F ∘ Y n) (ω k0) -
          ∑ l ∈ Finset.Ico k0 mt, ((C n).expect (F ∘ Y n) (ω l) - (F ∘ Y n) (ω l)))|
        ∂(C n).pathLaw x := abs_integral_le_integral_abs
    _ ≤ ∫ _ω, ‖h‖ * ((2 * t + 5) * ε) ∂(C n).pathLaw x :=
        integral_mono_ae (hMint.sub hDint).abs (integrable_const _) hpt
    _ = ‖h‖ * ((2 * t + 5) * ε) := by simp

section Laws

variable {S : Type*} [Fintype S] [MeasurableSpace S] [DiscreteMeasurableSpace S]

noncomputable def mixLaw (C : FinChain S) (π : S → ℝ) : Measure (ℕ → S) :=
  ∑ x, ENNReal.ofReal (π x) • C.pathLaw x

omit [Fintype G] in
theorem isProbabilityMeasure_mixLaw (C : FinChain S) {π : S → ℝ} (hπ0 : ∀ x, 0 ≤ π x)
    (hπ1 : ∑ x, π x = 1) : IsProbabilityMeasure (mixLaw C π) := by
  constructor
  simp only [mixLaw, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun x _ => hπ0 x, hπ1, ENNReal.ofReal_one]

omit [Fintype G] in
theorem integral_mixLaw (C : FinChain S) {π : S → ℝ} (hπ0 : ∀ x, 0 ≤ π x)
    {Φ : (ℕ → S) → ℝ} (hΦ : ∀ x, Integrable Φ (C.pathLaw x)) :
    ∫ ω, Φ ω ∂mixLaw C π = ∑ x, π x * ∫ ω, Φ ω ∂C.pathLaw x := by
  rw [mixLaw, integral_finsetSum_measure fun x _ => (hΦ x).smul_measure ENNReal.ofReal_ne_top]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [integral_smul_measure, ENNReal.toReal_ofReal (hπ0 x), smul_eq_mul]

omit [Fintype G] [MeasurableSpace S] [DiscreteMeasurableSpace S] in
theorem exists_stationary_dist (C : FinChain S) [Nonempty S] :
    ∃ π : S → ℝ, (∀ x, 0 ≤ π x) ∧ ∑ x, π x = 1 ∧ ∀ y, ∑ x, π x * C.P x y = π y := by
  classical
  let R : RateChain S :=
    { Q := C.P - 1
      off_diag_nonneg := fun x y hxy => by
        simp [Matrix.sub_apply, Matrix.one_apply_ne hxy, C.nonneg x y]
      row_sum := fun x => by
        simp [Matrix.sub_apply, Finset.sum_sub_distrib, C.row_sum, Matrix.one_apply] }
  obtain ⟨π, hπ⟩ := R.exists_isStationary
  refine ⟨π, hπ.nonneg, hπ.sum_eq_one, fun y => ?_⟩
  have h := congrFun hπ.vecMul_Q y
  simp only [R, Matrix.vecMul_sub, Matrix.vecMul_one, Pi.sub_apply, Pi.zero_apply,
    sub_eq_zero] at h
  rw [← h]
  simp [Matrix.vecMul, dotProduct]

omit [Fintype G] [MeasurableSpace S] [DiscreteMeasurableSpace S] in
theorem sum_mul_expectN [DecidableEq S] (C : FinChain S) {π : S → ℝ}
    (hπ : ∀ y, ∑ x, π x * C.P x y = π y) (F : S → ℝ) (m : ℕ) :
    ∑ x, π x * C.expectN m F x = ∑ x, π x * F x := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← ih, FinChain.expectN_succ]
    simp only [FinChain.expect_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← hπ y, Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => by ring

omit [Fintype G] in
noncomputable def vecLaw [Finite G] (C : FinChain S) (Y : S → G → ℝ) (τ : ℝ) {π : S → ℝ}
    (hπ0 : ∀ x, 0 ≤ π x) (hπ1 : ∑ x, π x = 1) : ProbabilityMeasure C(ℝ≥0, G → ℝ) :=
  ⟨(mixLaw C π).map fun ω => vecPath τ fun m => Y (ω m), by
    have := isProbabilityMeasure_mixLaw C hπ0 hπ1
    exact (Measure.isProbabilityMeasure_map_iff (measurable_vecPath Y τ).aemeasurable).mpr this⟩

omit [Fintype G] in
theorem integral_vecLaw [Finite G] (C : FinChain S) (Y : S → G → ℝ) (τ : ℝ) {π : S → ℝ}
    (hπ0 : ∀ x, 0 ≤ π x) (hπ1 : ∑ x, π x = 1) (Φ : C(ℝ≥0, G → ℝ) →ᵇ ℝ) :
    ∫ w, Φ w ∂(vecLaw C Y τ hπ0 hπ1 : Measure C(ℝ≥0, G → ℝ)) =
      ∑ x, π x * ∫ ω, Φ (vecPath τ fun m => Y (ω m)) ∂C.pathLaw x := by
  change ∫ w, Φ w ∂((mixLaw C π).map fun ω => vecPath τ fun m => Y (ω m)) = _
  rw [integral_map (measurable_vecPath Y τ).aemeasurable Φ.continuous.aestronglyMeasurable]
  exact integral_mixLaw C hπ0 fun x => Integrable.of_bound
    ((Φ.continuous.measurable.comp (measurable_vecPath Y τ)).aestronglyMeasurable) ‖Φ‖
    (Eventually.of_forall fun ω => Φ.norm_coe_le_norm _)

omit [Fintype G] [MeasurableSpace S] [DiscreteMeasurableSpace S] in
theorem expect_pow_le_of_step (C : FinChain S) (g : S → ℝ) (z : S) {d : ℝ}
    (hd : ∀ w, C.P z w ≠ 0 → |g w - g z| ≤ d) (p : ℕ) :
    C.expect (fun w => (g w - g z) ^ p) z ≤ d ^ p := by
  rw [FinChain.expect_apply]
  calc ∑ w, C.P z w * (g w - g z) ^ p ≤ ∑ w, C.P z w * d ^ p := by
        refine Finset.sum_le_sum fun w _ => ?_
        by_cases hw : C.P z w = 0
        · simp [hw]
        · refine mul_le_mul_of_nonneg_left ?_ (C.nonneg z w)
          calc (g w - g z) ^ p ≤ |(g w - g z) ^ p| := le_abs_self _
            _ = |g w - g z| ^ p := abs_pow _ _
            _ ≤ d ^ p := pow_le_pow_left₀ (abs_nonneg _) (hd w hw) p
    _ = d ^ p := by rw [← Finset.sum_mul, C.row_sum, one_mul]

end Laws

omit [Fintype G] in
theorem isTightMeasureSet_vecLaw [Finite G] (C : ∀ n, FinChain (Sₙ n)) (Y : ∀ n, Sₙ n → G → ℝ)
    (τ : ℕ → ℝ) {π : ∀ n, Sₙ n → ℝ} (hπ0 : ∀ n x, 0 ≤ π n x) (hπ1 : ∀ n, ∑ x, π n x = 1)
    (hY : ∀ n z, Y n z ∈ cube G) (hτ : Tendsto τ atTop atTop) (c : ℝ) (e : ℕ → ℝ)
    (hβ : ∀ i, ∀ᶠ n in atTop, ∀ z,
      |(C n).expect (fun w => Y n w i) z - Y n z i| ≤ c / τ n)
    (hv : ∀ i, ∀ᶠ n in atTop, ∀ z,
      (C n).expect (fun w => (Y n w i - Y n z i) ^ 2) z ≤ c / τ n)
    (hq : ∀ i, ∀ᶠ n in atTop, ∀ z,
      (C n).expect (fun w => (Y n w i - Y n z i) ^ 4) z ≤ e n / τ n)
    (he : Tendsto e atTop (𝓝 0)) :
    IsTightMeasureSet {((μ : ProbabilityMeasure C(ℝ≥0, G → ℝ)) : Measure C(ℝ≥0, G → ℝ)) |
      μ ∈ range fun n => vecLaw (C n) (Y n) (τ n) (hπ0 n) (hπ1 n)} := by
  have := Fintype.ofFinite G
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  set η : ℝ≥0∞ := ε / (Fintype.card G + 1) with hη_def
  have hη : η ≠ 0 := ENNReal.div_ne_zero.2 ⟨hε.ne', by simp⟩
  have hcoord := fun i : G => exists_unitModulus_of_drift C (fun n z => Y n z i) τ
    (fun n z => hY n z i (mem_univ i)) hτ c e (hβ i) (hv i) (hq i) he hη
  choose δ hδ hδn using hcoord
  set Φ : (G → C(ℝ≥0, ℝ)) → C(ℝ≥0, G → ℝ) := fun w => ContinuousMap.pi w with hΦ_def
  have hΦ : Continuous Φ := by
    refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
    exact continuous_pi fun i => continuous_eval.comp
      (((continuous_apply i).comp continuous_fst).prodMk continuous_snd)
  set Kc := Φ '' Set.pi univ fun i => unitModulusSet (δ i) with hKc_def
  have hKc : IsCompact Kc :=
    (isCompact_univ_pi fun i => isCompact_unitModulusSet (hδ i)).image hΦ
  refine ⟨Kc, hKc, ?_⟩
  rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
  have hm := hKc.isClosed.measurableSet.compl
  have hsub : (fun ω : ℕ → Sₙ n => vecPath (τ n) fun m => Y n (ω m)) ⁻¹' Kcᶜ ⊆
      ⋃ i, {ω | ¬ UnitModulus (δ i) (rescaledPath (τ n) fun m => Y n (ω m) i)} := by
    intro ω hω
    by_contra hc
    simp only [mem_iUnion, mem_ofPred_eq, not_exists, not_not] at hc
    exact hω ⟨fun i => rescaledPath (τ n) fun m => Y n (ω m) i, fun i _ => hc i, rfl⟩
  have hx : ∀ x, (C n).pathLaw x
      ((fun ω : ℕ → Sₙ n => vecPath (τ n) fun m => Y n (ω m)) ⁻¹' Kcᶜ) ≤
      Fintype.card G * η := by
    intro x
    calc _ ≤ (C n).pathLaw x
          (⋃ i, {ω | ¬ UnitModulus (δ i) (rescaledPath (τ n) fun m => Y n (ω m) i)}) :=
          measure_mono hsub
      _ ≤ ∑ i, (C n).pathLaw x
          {ω | ¬ UnitModulus (δ i) (rescaledPath (τ n) fun m => Y n (ω m) i)} :=
          measure_iUnion_fintype_le _ _
      _ ≤ ∑ _i : G, η := Finset.sum_le_sum fun i _ => hδn i n x
      _ = Fintype.card G * η := by simp
  change ((mixLaw (C n) (π n)).map fun ω => vecPath (τ n) fun m => Y n (ω m)) Kcᶜ ≤ ε
  rw [Measure.map_apply (measurable_vecPath (Y n) (τ n)) hm, mixLaw, Measure.coe_finsetSum,
    Finset.sum_apply]
  calc ∑ x, (ENNReal.ofReal (π n x) • (C n).pathLaw x)
        ((fun ω : ℕ → Sₙ n => vecPath (τ n) fun m => Y n (ω m)) ⁻¹' Kcᶜ)
      ≤ ∑ x, ENNReal.ofReal (π n x) * (Fintype.card G * η) :=
        Finset.sum_le_sum fun x _ => by
          rw [Measure.smul_apply, smul_eq_mul]
          gcongr; exact hx x
    _ = Fintype.card G * η := by
        rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg fun x _ => hπ0 n x, hπ1 n,
          ENNReal.ofReal_one, one_mul]
    _ ≤ (Fintype.card G + 1) * η := by gcongr; exact le_self_add
    _ = ε := ENNReal.mul_div_cancel (by simp) (by simp)

theorem ae_eq_zero_of_mapClusterPt {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] {μ : ℕ → ProbabilityMeasure E} {Q : ProbabilityMeasure E}
    (hQ : MapClusterPt Q atTop μ) (Φ : E →ᵇ ℝ) (hΦ : ∀ w, 0 ≤ Φ w)
    (h : Tendsto (fun n => ∫ w, Φ w ∂(μ n : Measure E)) atTop (𝓝 0)) :
    ∀ᵐ w ∂(Q : Measure E), Φ w = 0 := by
  have h0 := integral_eq_zero_of_mapClusterPt hQ Φ h
  rwa [integral_eq_zero_iff_of_nonneg hΦ (Φ.integrable _)] at h0

/-- Source: ethier_kurtz1986, ch. 4, sec. 9. -/
theorem exists_stationary_martingale_limit (C : ∀ n, FinChain (Sₙ n))
    [∀ n, Nonempty (Sₙ n)] (Y : ∀ n, Sₙ n → G → ℝ) (τ : ℕ → ℝ) {K : Set (G → ℝ)}
    (hKc : IsClosed K) (hKv : Convex ℝ K) (hKcube : K ⊆ cube G) (hYK : ∀ n z, Y n z ∈ K)
    (hτ : Tendsto τ atTop atTop) (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hstep : ∀ᶠ n in atTop, ∀ z z', (C n).P z z' ≠ 0 → dist (Y n z') (Y n z) ≤ δ n)
    (c : ℝ) (e : ℕ → ℝ)
    (hβ : ∀ i, ∀ᶠ n in atTop, ∀ z,
      |(C n).expect (fun w => Y n w i) z - Y n z i| ≤ c / τ n)
    (hv : ∀ i, ∀ᶠ n in atTop, ∀ z,
      (C n).expect (fun w => (Y n w i - Y n z i) ^ 2) z ≤ c / τ n)
    (hq : ∀ i, ∀ᶠ n in atTop, ∀ z,
      (C n).expect (fun w => (Y n w i - Y n z i) ^ 4) z ≤ e n / τ n)
    (he : Tendsto e atTop (𝓝 0)) {ι : Type*} (F AF : ι → (G → ℝ) → ℝ)
    (hF : ∀ p, Continuous (F p)) (hAF : ∀ p, Continuous (AF p))
    (hgen : ∀ p, ∀ ε > 0, ∀ᶠ n in atTop, ∀ z,
      |τ n * ((C n).expect (F p ∘ Y n) z - F p (Y n z)) - AF p (Y n z)| ≤ ε) :
    ∃ Q : Measure C(ℝ≥0, G → ℝ), IsProbabilityMeasure Q ∧ (∀ᵐ w ∂Q, ∀ t, w t ∈ K) ∧
      (∀ p, ∀ s t : ℝ≥0, s ≤ t → ∀ (k : ℕ) (r : Fin k → ℝ≥0), (∀ j, r j ≤ s) →
        ∀ h : (Fin k → G → ℝ) →ᵇ ℝ,
          ∫ w, (F p (w t) - F p (w s) - ∫ u in (s : ℝ)..t, AF p (w u.toNNReal)) *
            h (fun j => w (r j)) ∂Q = 0) ∧
      ∀ t : ℝ≥0, Q.map (fun w => w t) = Q.map (fun w => w 0) := by
  classical
  have hY : ∀ n z, Y n z ∈ cube G := fun n z => hKcube (hYK n z)
  have hKne : K.Nonempty := ⟨Y 0 (Classical.arbitrary _), hYK 0 _⟩
  choose π hπ0 hπ1 hπs using fun n => exists_stationary_dist (C n)
  set μ := fun n => vecLaw (C n) (Y n) (τ n) (hπ0 n) (hπ1 n) with hμ_def
  have hcomp := isCompact_closure_of_isTightMeasureSet (E := C(ℝ≥0, G → ℝ)) (S := range μ)
    (isTightMeasureSet_vecLaw C Y τ hπ0 hπ1 hY hτ c e hβ hv hq he)
  obtain ⟨Q, -, hQ⟩ := hcomp.exists_mapClusterPt (f := atTop) (u := μ)
    (tendsto_principal.2 (Eventually.of_forall fun n => subset_closure ⟨n, rfl⟩))
  have hmean : ∀ n (Φ : C(ℝ≥0, G → ℝ) →ᵇ ℝ), ∫ w, Φ w ∂(μ n : Measure C(ℝ≥0, G → ℝ)) =
      ∑ x, π n x * ∫ ω, Φ (vecPath (τ n) fun m => Y n (ω m)) ∂(C n).pathLaw x :=
    fun n Φ => integral_vecLaw (C n) (Y n) (τ n) (hπ0 n) (hπ1 n) Φ
  have hmem_t : ∀ t : ℝ≥0, ∀ᵐ w ∂(Q : Measure C(ℝ≥0, G → ℝ)), w t ∈ K := by
    intro t
    have hcont : Continuous fun w : C(ℝ≥0, G → ℝ) => min 1 (Metric.infDist (w t) K) :=
      continuous_const.min ((Metric.continuous_infDist_pt K).comp (continuous_eval_const t))
    have hnn : ∀ w : C(ℝ≥0, G → ℝ), 0 ≤ min 1 (Metric.infDist (w t) K) :=
      fun w => le_min zero_le_one Metric.infDist_nonneg
    obtain ⟨Φ, hΦ⟩ : ∃ Φ : C(ℝ≥0, G → ℝ) →ᵇ ℝ, ∀ w, Φ w = min 1 (Metric.infDist (w t) K) :=
      ⟨BoundedContinuousFunction.ofNormedAddCommGroup _ hcont 1
        fun w => by rw [Real.norm_eq_abs, abs_of_nonneg (hnn w)]; exact min_le_left _ _,
        fun w => rfl⟩
    have hlim : Tendsto (fun n => ∫ w, Φ w ∂(μ n : Measure C(ℝ≥0, G → ℝ))) atTop (𝓝 0) := by
      refine tendsto_const_nhds.congr fun n => ?_
      rw [hmean]
      symm
      refine Finset.sum_eq_zero fun x _ => ?_
      rw [integral_eq_zero_of_ae (Eventually.of_forall fun ω => ?_), mul_zero]
      change Φ (vecPath (τ n) fun m => Y n (ω m)) = 0
      rw [hΦ, vecPath_apply, (Metric.infDist_zero_of_mem (vint_mem hKv (fun m => hYK n (ω m)) _)),
        min_eq_right zero_le_one]
    filter_upwards [ae_eq_zero_of_mapClusterPt hQ Φ (fun w => by rw [hΦ]; exact hnn w) hlim]
      with w hw
    rw [hΦ] at hw
    have hd : Metric.infDist (w t) K = 0 := by
      rcases le_total 1 (Metric.infDist (w t) K) with h1 | h1
      · rw [min_eq_left h1] at hw
        exact absurd hw one_ne_zero
      · rwa [min_eq_right h1] at hw
    exact (hKc.mem_iff_infDist_zero hKne).2 hd
  have hmem : ∀ᵐ w ∂(Q : Measure C(ℝ≥0, G → ℝ)), ∀ t, w t ∈ K := by
    obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq ℝ≥0
    filter_upwards [ae_all_iff.2 fun i => hmem_t (u i)] with w hw t
    have hcl : IsClosed {v : ℝ≥0 | w v ∈ K} := hKc.preimage w.continuous
    have hsub : closure (range u) ⊆ {v : ℝ≥0 | w v ∈ K} :=
      closure_minimal (range_subset_iff.2 hw) hcl
    exact hsub (by rw [hu.closure_range]; exact mem_univ t)
  refine ⟨(Q : Measure C(ℝ≥0, G → ℝ)), inferInstance, hmem, ?_, ?_⟩
  · intro p s t hst k r hr h
    have hlim : Tendsto (fun n => ∫ w, vecTestBCF (hF p) (hAF p) s t r h w
        ∂(μ n : Measure C(ℝ≥0, G → ℝ))) atTop (𝓝 0) := by
      refine tendsto_zero_of_forall_eventually_abs_le (‖h‖ * (2 * t + 5)) fun ε hε => ?_
      filter_upwards [eventually_abs_integral_vecTest_le C Y τ hY hτ δ hδ hstep (hF p)
        (hAF p) (hgen p) hst r hr h hε] with n hn
      rw [hmean]
      calc |∑ x, π n x * ∫ ω, vecTestBCF (hF p) (hAF p) s t r h
            (vecPath (τ n) fun m => Y n (ω m)) ∂(C n).pathLaw x|
          ≤ ∑ x, |π n x * ∫ ω, vecTestBCF (hF p) (hAF p) s t r h
            (vecPath (τ n) fun m => Y n (ω m)) ∂(C n).pathLaw x| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ x, π n x * (‖h‖ * ((2 * t + 5) * ε)) := Finset.sum_le_sum fun x _ => by
            rw [abs_mul, abs_of_nonneg (hπ0 n x)]
            exact mul_le_mul_of_nonneg_left (hn x) (hπ0 n x)
        _ = ‖h‖ * (2 * t + 5) * ε := by rw [← Finset.sum_mul, hπ1 n]; ring
    have h0 := integral_eq_zero_of_mapClusterPt hQ _ hlim
    rw [← h0]
    refine integral_congr_ae ?_
    filter_upwards [hmem] with w hw
    have hc : ∀ v, clampVec (w v) = w v := fun v => clampVec_of_mem (hKcube (hw v))
    rw [vecTestBCF_apply]
    unfold vecTest
    simp only [hc]
  · intro t
    refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun Fb => ?_
    rw [integral_map (continuous_eval_const t).measurable.aemeasurable
        Fb.continuous.aestronglyMeasurable,
      integral_map (continuous_eval_const 0).measurable.aemeasurable
        Fb.continuous.aestronglyMeasurable]
    have hcont : Continuous fun w : C(ℝ≥0, G → ℝ) => Fb (w t) - Fb (w 0) :=
      (Fb.continuous.comp (continuous_eval_const t)).sub
        (Fb.continuous.comp (continuous_eval_const 0))
    have hbd : ∀ w : C(ℝ≥0, G → ℝ), ‖Fb (w t) - Fb (w 0)‖ ≤ 2 * ‖Fb‖ := fun w =>
      (norm_sub_le _ _).trans (by linarith [Fb.norm_coe_le_norm (w t), Fb.norm_coe_le_norm (w 0)])
    obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : C(ℝ≥0, G → ℝ) →ᵇ ℝ, ∀ w, Ψ w = Fb (w t) - Fb (w 0) :=
      ⟨BoundedContinuousFunction.ofNormedAddCommGroup _ hcont (2 * ‖Fb‖) hbd, fun w => rfl⟩
    have hFu := isCompact_cube.uniformContinuousOn_of_continuous
      (Fb.continuous.continuousOn (s := cube G))
    rw [Metric.uniformContinuousOn_iff_le] at hFu
    have hlim : Tendsto (fun n => ∫ w, Ψ w ∂(μ n : Measure C(ℝ≥0, G → ℝ))) atTop (𝓝 0) := by
      refine tendsto_zero_of_forall_eventually_abs_le 1 fun ε hε => ?_
      obtain ⟨η, hη, hFη⟩ := hFu ε hε
      filter_upwards [hstep, hδ.eventually (ge_mem_nhds hη)] with n h4 h5
      rw [hmean]
      set mt := ⌈τ n * t⌉₊ with hmt
      have hone : ∀ x, |∫ ω, Ψ (vecPath (τ n) fun m => Y n (ω m)) ∂(C n).pathLaw x -
          ((C n).expectN mt (fun z => Fb (Y n z)) x - Fb (Y n x))| ≤ ε := by
        intro x
        have hi1 : Integrable (fun ω : ℕ → Sₙ n => Ψ (vecPath (τ n) fun m => Y n (ω m)))
            ((C n).pathLaw x) := Integrable.of_bound
          ((Ψ.continuous.measurable.comp (measurable_vecPath (Y n) (τ n))).aestronglyMeasurable)
          ‖Ψ‖ (Eventually.of_forall fun ω => Ψ.norm_coe_le_norm _)
        have hi2 := (C n).integrable_eval (fun z => Fb (Y n z)) mt x
        have hi3 := (C n).integrable_eval (fun z => Fb (Y n z)) 0 x
        have e1 := (C n).integral_eval mt (fun z => Fb (Y n z)) x
        have e2 := (C n).integral_eval 0 (fun z => Fb (Y n z)) x
        rw [FinChain.expectN_zero] at e2
        have hi23 : Integrable (fun ω : ℕ → Sₙ n => Fb (Y n (ω mt)) - Fb (Y n (ω 0)))
            ((C n).pathLaw x) := hi2.sub hi3
        rw [← e1, ← e2, ← integral_sub hi2 hi3, ← integral_sub hi1 hi23]
        refine (abs_integral_le_integral_abs).trans ?_
        calc ∫ ω, |Ψ (vecPath (τ n) fun m => Y n (ω m)) -
              (Fb (Y n (ω mt)) - Fb (Y n (ω 0)))| ∂(C n).pathLaw x
            ≤ ∫ _ω, ε ∂(C n).pathLaw x := by
              refine integral_mono_ae (hi1.sub (hi2.sub hi3)).abs (integrable_const _) ?_
              filter_upwards [ae_transition_ne_zero (C n) x] with ω hω
              rw [hΨ]
              have h0 : (vecPath (τ n) fun m => Y n (ω m)) 0 = Y n (ω 0) := by
                rw [vecPath_apply, NNReal.coe_zero, mul_zero]
                exact funext fun i => interpolate_of_nonpos _ le_rfl
              rw [h0]
              have hd := dist_vint_ceil_le (a := fun m => Y n (ω m)) hη.le
                (u := τ n * t) fun l _ => (h4 _ _ (hω l)).trans h5
              have := hFη _ (vint_mem_cube (fun m => hY n (ω m)) _) _ (hY n (ω mt)) hd
              rw [Real.dist_eq] at this
              rw [vecPath_apply]
              calc |Fb (vint (fun m => Y n (ω m)) (τ n * t)) - Fb (Y n (ω 0)) -
                    (Fb (Y n (ω mt)) - Fb (Y n (ω 0)))|
                  = |Fb (vint (fun m => Y n (ω m)) (τ n * t)) - Fb (Y n (ω mt))| := by
                    ring_nf
                _ ≤ ε := this
          _ = ε := by simp
      have hzero : ∑ x, π n x * ((C n).expectN mt (fun z => Fb (Y n z)) x - Fb (Y n x)) = 0 := by
        simp only [mul_sub, Finset.sum_sub_distrib]
        rw [sum_mul_expectN (C n) (hπs n), sub_self]
      calc |∑ x, π n x * ∫ ω, Ψ (vecPath (τ n) fun m => Y n (ω m)) ∂(C n).pathLaw x|
          = |∑ x, π n x * (∫ ω, Ψ (vecPath (τ n) fun m => Y n (ω m)) ∂(C n).pathLaw x -
              ((C n).expectN mt (fun z => Fb (Y n z)) x - Fb (Y n x)))| := by
            rw [← sub_zero (∑ x, π n x * ∫ ω, Ψ (vecPath (τ n) fun m => Y n (ω m))
              ∂(C n).pathLaw x), ← hzero, ← Finset.sum_sub_distrib]
            simp only [mul_sub]
        _ ≤ ∑ x, |π n x * (∫ ω, Ψ (vecPath (τ n) fun m => Y n (ω m)) ∂(C n).pathLaw x -
              ((C n).expectN mt (fun z => Fb (Y n z)) x - Fb (Y n x)))| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ x, π n x * ε := Finset.sum_le_sum fun x _ => by
            rw [abs_mul, abs_of_nonneg (hπ0 n x)]
            exact mul_le_mul_of_nonneg_left (hone x) (hπ0 n x)
        _ = 1 * ε := by rw [← Finset.sum_mul, hπ1 n]
    have h0 := integral_eq_zero_of_mapClusterPt hQ Ψ hlim
    simp only [hΨ] at h0
    have hit : Integrable (fun w : C(ℝ≥0, G → ℝ) => Fb (w t)) (Q : Measure C(ℝ≥0, G → ℝ)) :=
      (Fb.compContinuous ⟨fun w : C(ℝ≥0, G → ℝ) => w t, continuous_eval_const t⟩).integrable _
    have hi0 : Integrable (fun w : C(ℝ≥0, G → ℝ) => Fb (w 0)) (Q : Measure C(ℝ≥0, G → ℝ)) :=
      (Fb.compContinuous ⟨fun w : C(ℝ≥0, G → ℝ) => w 0, continuous_eval_const 0⟩).integrable _
    rw [integral_sub hit hi0] at h0
    linarith

end Rhone.Diffusion
