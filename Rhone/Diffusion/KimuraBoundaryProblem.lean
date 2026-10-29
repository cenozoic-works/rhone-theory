/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Diffusion.GeneratorC2
public import Rhone.MarkovChain.MoranFixationLimit
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Kimura's fixation function as the solution of a boundary value problem

Source: kimura1962, p. 714, eq. (3)–(4). -/

@[expose] public section

namespace Rhone.Diffusion

open MarkovChain Set Filter Topology

noncomputable def kimuraFixation (σ x : ℝ) : ℝ :=
  (1 - Real.exp (-(2 * σ * x))) / (1 - Real.exp (-(2 * σ)))

private theorem hasDerivAt_neg_lin (c x : ℝ) : HasDerivAt (fun y : ℝ => -(c * y)) (-c) x := by
  have h := ((hasDerivAt_id x).const_mul c).fun_neg
  simpa using h

private theorem denom_ne_zero {σ : ℝ} (hσ : σ ≠ 0) : 1 - Real.exp (-(2 * σ)) ≠ 0 := by
  intro h
  have h1 : Real.exp (-(2 * σ)) = 1 := by linarith
  have := Real.exp_eq_one_iff _ |>.mp h1
  exact hσ (by linarith)

private theorem hasDerivAt_kimuraFixation {σ : ℝ} (x : ℝ) :
    HasDerivAt (kimuraFixation σ)
      (2 * σ * Real.exp (-(2 * σ * x)) / (1 - Real.exp (-(2 * σ)))) x := by
  have h1 := hasDerivAt_neg_lin (2 * σ) x
  have h2 := (h1.exp).const_sub 1
  have h3 := h2.div_const (1 - Real.exp (-(2 * σ)))
  have e : (-(Real.exp (-(2 * σ * x)) * -(2 * σ))) / (1 - Real.exp (-(2 * σ)))
      = 2 * σ * Real.exp (-(2 * σ * x)) / (1 - Real.exp (-(2 * σ))) := by ring
  rw [e] at h3
  exact h3

private theorem deriv_kimuraFixation {σ : ℝ} :
    deriv (kimuraFixation σ) =
      fun y => 2 * σ * Real.exp (-(2 * σ * y)) / (1 - Real.exp (-(2 * σ))) :=
  funext fun y => (hasDerivAt_kimuraFixation y).deriv

private theorem deriv_deriv_kimuraFixation {σ : ℝ} (x : ℝ) :
    deriv (deriv (kimuraFixation σ)) x =
      -(2 * σ) * (2 * σ * Real.exp (-(2 * σ * x)) / (1 - Real.exp (-(2 * σ)))) := by
  rw [deriv_kimuraFixation]
  have h1 := hasDerivAt_neg_lin (2 * σ) x
  have h2 := ((h1.exp).const_mul (2 * σ)).div_const (1 - Real.exp (-(2 * σ)))
  rw [h2.deriv]
  ring

/-- Source: kimura1962, p. 714, eq. (3)–(4). -/
theorem wfGeneratorSel_kimuraFixation {σ : ℝ} (_hσ : σ ≠ 0) (x : ℝ) :
    wfGeneratorSel σ (kimuraFixation σ) x = 0 := by
  unfold wfGeneratorSel wfGenerator
  rw [deriv_deriv_kimuraFixation x, deriv_kimuraFixation]
  ring

theorem kimuraFixation_zero (σ : ℝ) : kimuraFixation σ 0 = 0 := by
  simp [kimuraFixation]

theorem kimuraFixation_one {σ : ℝ} (hσ : σ ≠ 0) : kimuraFixation σ 1 = 1 := by
  simp only [kimuraFixation, mul_one]
  exact div_self (denom_ne_zero hσ)

private theorem eq_of_hasDerivAt_zero {F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn F (Icc a b)) (hd : ∀ y ∈ Ioo a b, HasDerivAt F 0 y) : F a = F b := by
  rcases hab.eq_or_lt with h | h
  · rw [h]
  · obtain ⟨c, hc', hcd⟩ := exists_deriv_eq_slope F h hc
      (fun y hy => (hd y hy).differentiableAt.differentiableWithinAt)
    rw [(hd c hc').deriv] at hcd
    have := hcd.symm
    rw [div_eq_zero_iff] at this
    rcases this with h0 | h0
    · linarith
    · exact absurd h0 (sub_ne_zero.mpr h.ne')

/-- Source: kimura1962, p. 714, eq. (3)–(4). -/
theorem kimuraFixation_unique {σ : ℝ} (hσ : σ ≠ 0) {f : ℝ → ℝ}
    (hc : ContinuousOn f (Icc 0 1)) (hd : ContDiffOn ℝ 2 f (Ioo 0 1))
    (hL : ∀ x ∈ Ioo (0 : ℝ) 1, wfGeneratorSel σ f x = 0) (h0 : f 0 = 0) (h1 : f 1 = 1) :
    ∀ x ∈ Icc (0 : ℝ) 1, f x = kimuraFixation σ x := by
  have hd' := (contDiffOn_succ_iff_deriv_of_isOpen (n := 1) isOpen_Ioo).1
    (show ContDiffOn ℝ (1 + 1) f (Ioo 0 1) from hd)
  have hf : ∀ y ∈ Ioo (0 : ℝ) 1, HasDerivAt f (deriv f y) y := fun y hy =>
    ((hd'.1.differentiableAt (isOpen_Ioo.mem_nhds hy))).hasDerivAt
  have hf' : ∀ y ∈ Ioo (0 : ℝ) 1, HasDerivAt (deriv f) (deriv (deriv f) y) y := fun y hy =>
    ((hd'.2.2.differentiableOn one_ne_zero).differentiableAt (isOpen_Ioo.mem_nhds hy)).hasDerivAt
  have hg : ∀ y ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun t => deriv f t * Real.exp (2 * σ * t)) 0 y := by
    intro y hy
    have h2 : HasDerivAt (fun t : ℝ => Real.exp (2 * σ * t))
        (Real.exp (2 * σ * y) * (2 * σ)) y := by
      simpa using (((hasDerivAt_id y).const_mul (2 * σ)).exp)
    have h3 := (hf' y hy).mul h2
    have hy0 : y * (1 - y) ≠ 0 := (mul_pos hy.1 (by linarith [hy.2])).ne'
    have hLy := hL y hy
    unfold wfGeneratorSel wfGenerator at hLy
    have hz : deriv (deriv f) y + 2 * σ * deriv f y = 0 := by
      have : y * (1 - y) * (deriv (deriv f) y + 2 * σ * deriv f y) = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left hy0
    convert h3 using 1
    have : deriv (deriv f) y * Real.exp (2 * σ * y) + deriv f y * (Real.exp (2 * σ * y) * (2 * σ))
        = Real.exp (2 * σ * y) * (deriv (deriv f) y + 2 * σ * deriv f y) := by ring
    rw [this, hz, mul_zero]
  set K : ℝ := deriv f (1 / 2) * Real.exp (2 * σ * (1 / 2)) with hK
  have hKc : ∀ y ∈ Ioo (0 : ℝ) 1, deriv f y * Real.exp (2 * σ * y) = K := by
    intro y hy
    have hmem : ∀ a b : ℝ, a ∈ Ioo (0 : ℝ) 1 → b ∈ Ioo (0 : ℝ) 1 → a ≤ b →
        deriv f a * Real.exp (2 * σ * a) = deriv f b * Real.exp (2 * σ * b) := by
      intro a b ha hb hab
      refine eq_of_hasDerivAt_zero (F := fun t => deriv f t * Real.exp (2 * σ * t)) hab ?_
        (fun t ht => hg t ⟨ht.1.trans_le' ha.1.le, ht.2.trans_le hb.2.le⟩)
      intro t ht
      exact (hg t ⟨lt_of_lt_of_le ha.1 ht.1, lt_of_le_of_lt ht.2 hb.2⟩).continuousAt
        |>.continuousWithinAt
    have hhalf : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
    rcases le_total y (1 / 2) with hle | hle
    · exact hmem _ _ hy hhalf hle
    · exact (hmem _ _ hhalf hy hle).symm
  have hder : ∀ y ∈ Ioo (0 : ℝ) 1, deriv f y = K * Real.exp (-(2 * σ * y)) := by
    intro y hy
    rw [← hKc y hy, mul_assoc, ← Real.exp_add]
    simp
  set a : ℝ := K / (2 * σ) with ha
  have hF : ∀ y ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun t => f t + a * Real.exp (-(2 * σ * t))) 0 y := by
    intro y hy
    have h2 : HasDerivAt (fun t : ℝ => Real.exp (-(2 * σ * t)))
        (Real.exp (-(2 * σ * y)) * (-(2 * σ))) y := by
      simpa using (hasDerivAt_neg_lin (2 * σ) y).exp
    have h3 := (hf y hy).add (h2.const_mul a)
    convert h3 using 1
    rw [hder y hy, ha]
    field_simp
    ring
  have hFc : ContinuousOn (fun t => f t + a * Real.exp (-(2 * σ * t))) (Icc 0 1) :=
    hc.add (by fun_prop)
  have hFx : ∀ x ∈ Icc (0 : ℝ) 1,
      f 0 + a * Real.exp (-(2 * σ * 0)) = f x + a * Real.exp (-(2 * σ * x)) := by
    intro x hx
    refine eq_of_hasDerivAt_zero (F := fun t => f t + a * Real.exp (-(2 * σ * t))) hx.1
      (hFc.mono (Icc_subset_Icc le_rfl hx.2))
      (fun t ht => hF t ⟨ht.1, ht.2.trans_le hx.2⟩)
  have hsum1 := hFx 1 ⟨zero_le_one, le_rfl⟩
  intro x hx
  have hsum := hFx x hx
  have hden := denom_ne_zero hσ
  simp only [mul_zero, neg_zero, Real.exp_zero, mul_one] at hsum1 hsum
  rw [h0, h1] at hsum1
  rw [h0] at hsum
  have hak : a * (1 - Real.exp (-(2 * σ))) = 1 := by linear_combination hsum1
  have ha' : a = 1 / (1 - Real.exp (-(2 * σ))) := (eq_div_iff hden).2 hak
  have hfx : f x = a * (1 - Real.exp (-(2 * σ * x))) := by linarith
  rw [hfx, ha', kimuraFixation]
  field_simp

theorem eq_affine_of_hasDerivAt_zero {w w' : ℝ → ℝ} (hc : ContinuousOn w (Icc 0 1))
    (h1 : ∀ y ∈ Ioo (0 : ℝ) 1, HasDerivAt w (w' y) y)
    (h2 : ∀ y ∈ Ioo (0 : ℝ) 1, HasDerivAt w' 0 y) :
    ∀ x ∈ Icc (0 : ℝ) 1, w x = w 0 + (w 1 - w 0) * x := by
  set K : ℝ := w' (1 / 2) with hK
  have hhalf : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hmem : ∀ a b : ℝ, a ∈ Ioo (0 : ℝ) 1 → b ∈ Ioo (0 : ℝ) 1 → a ≤ b → w' a = w' b := by
    intro a b ha hb hab
    refine eq_of_hasDerivAt_zero (F := w') hab ?_
      (fun t ht => h2 t ⟨ha.1.trans ht.1, ht.2.trans hb.2⟩)
    intro t ht
    exact (h2 t ⟨lt_of_lt_of_le ha.1 ht.1, lt_of_le_of_lt ht.2 hb.2⟩).continuousAt
      |>.continuousWithinAt
  have hKc : ∀ y ∈ Ioo (0 : ℝ) 1, w' y = K := by
    intro y hy
    rcases le_total y (1 / 2) with hle | hle
    · exact hmem _ _ hy hhalf hle
    · exact (hmem _ _ hhalf hy hle).symm
  have hF : ∀ y ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun t => w t - K * t) 0 y := by
    intro y hy
    have h3 : HasDerivAt (fun t => w t - K * t) (w' y - K) y :=
      (h1 y hy).sub (by simpa using (hasDerivAt_id y).const_mul K)
    rw [hKc y hy, sub_self] at h3
    exact h3
  have hFc : ContinuousOn (fun t => w t - K * t) (Icc 0 1) := hc.sub (by fun_prop)
  have hFx : ∀ x ∈ Icc (0 : ℝ) 1, w 0 - K * 0 = w x - K * x := by
    intro x hx
    exact eq_of_hasDerivAt_zero (F := fun t => w t - K * t) hx.1
      (hFc.mono (Icc_subset_Icc le_rfl hx.2)) (fun t ht => hF t ⟨ht.1, ht.2.trans_le hx.2⟩)
  intro x hx
  have e1 := hFx 1 ⟨zero_le_one, le_rfl⟩
  have e := hFx x hx
  have hK1 : K = w 1 - w 0 := by linarith
  rw [← hK1]
  linarith

noncomputable def kimuraFixationFn (σ x : ℝ) : ℝ := if σ = 0 then x else kimuraFixation σ x

theorem kimuraFixationFn_of_ne {σ : ℝ} (hσ : σ ≠ 0) : kimuraFixationFn σ = kimuraFixation σ :=
  funext fun y => by simp [kimuraFixationFn, hσ]

theorem kimuraFixationFn_zero_left : kimuraFixationFn 0 = fun y => y :=
  funext fun y => by simp [kimuraFixationFn]

/-- Source: kimura1962, p. 714, eq. (3)–(4). -/
theorem wfGeneratorSel_kimuraFixationFn (σ x : ℝ) :
    wfGeneratorSel σ (kimuraFixationFn σ) x = 0 := by
  by_cases hσ : σ = 0
  · subst hσ
    rw [kimuraFixationFn_zero_left, wfGeneratorSel, wfGenerator_id]
    simp
  · rw [kimuraFixationFn_of_ne hσ]
    exact wfGeneratorSel_kimuraFixation hσ x

theorem kimuraFixationFn_zero (σ : ℝ) : kimuraFixationFn σ 0 = 0 := by
  by_cases hσ : σ = 0
  · simp [kimuraFixationFn, hσ]
  · rw [kimuraFixationFn_of_ne hσ, kimuraFixation_zero]

theorem kimuraFixationFn_one (σ : ℝ) : kimuraFixationFn σ 1 = 1 := by
  by_cases hσ : σ = 0
  · simp [kimuraFixationFn, hσ]
  · rw [kimuraFixationFn_of_ne hσ, kimuraFixation_one hσ]

/-- Source: kimura1962, p. 714, eq. (3)–(4). -/
theorem kimuraFixationFn_unique (σ : ℝ) {f : ℝ → ℝ}
    (hc : ContinuousOn f (Icc 0 1)) (hd : ContDiffOn ℝ 2 f (Ioo 0 1))
    (hL : ∀ x ∈ Ioo (0 : ℝ) 1, wfGeneratorSel σ f x = 0) (h0 : f 0 = 0) (h1 : f 1 = 1) :
    ∀ x ∈ Icc (0 : ℝ) 1, f x = kimuraFixationFn σ x := by
  by_cases hσ : σ = 0
  · subst hσ
    have hd' := (contDiffOn_succ_iff_deriv_of_isOpen (n := 1) isOpen_Ioo).1
      (show ContDiffOn ℝ (1 + 1) f (Ioo 0 1) from hd)
    have hf : ∀ y ∈ Ioo (0 : ℝ) 1, HasDerivAt f (deriv f y) y := fun y hy =>
      ((hd'.1.differentiableAt (isOpen_Ioo.mem_nhds hy))).hasDerivAt
    have hf' : ∀ y ∈ Ioo (0 : ℝ) 1, HasDerivAt (deriv f) 0 y := by
      intro y hy
      have h := ((hd'.2.2.differentiableOn one_ne_zero).differentiableAt
        (isOpen_Ioo.mem_nhds hy)).hasDerivAt
      have hy0 : y * (1 - y) ≠ 0 := (mul_pos hy.1 (by linarith [hy.2])).ne'
      have hLy := hL y hy
      unfold wfGeneratorSel wfGenerator at hLy
      have hz : deriv (deriv f) y = 0 := by
        have : y * (1 - y) * deriv (deriv f) y = 0 := by linarith
        exact (mul_eq_zero.mp this).resolve_left hy0
      rwa [hz] at h
    intro x hx
    have h := eq_affine_of_hasDerivAt_zero hc hf hf' x hx
    rw [h, h0, h1, kimuraFixationFn_zero_left]
    ring
  · rw [kimuraFixationFn_of_ne hσ]
    exact kimuraFixation_unique hσ hc hd hL h0 h1

theorem tendsto_kimuraFixation_nhdsNE_zero (x : ℝ) :
    Tendsto (fun σ => kimuraFixation σ x) (𝓝[≠] 0) (𝓝 x) := by
  have hn : HasDerivAt (fun s : ℝ => 1 - Real.exp (-(2 * x * s))) (2 * x) 0 := by
    have h := ((hasDerivAt_neg_lin (2 * x) 0).exp).const_sub 1
    simpa using h
  have hd : HasDerivAt (fun s : ℝ => 1 - Real.exp (-(2 * s))) 2 0 := by
    have h := ((hasDerivAt_neg_lin 2 0).exp).const_sub 1
    simpa using h
  have h := (hasDerivAt_iff_tendsto_slope.1 hn).div (hasDerivAt_iff_tendsto_slope.1 hd)
    two_ne_zero
  rw [mul_div_cancel_left₀ x two_ne_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : s ≠ 0 := hs
  simp only [Pi.div_apply, slope, vsub_eq_sub, sub_zero, smul_eq_mul, mul_zero, neg_zero,
    Real.exp_zero, sub_self]
  rw [mul_div_mul_left _ _ (inv_ne_zero hs0), kimuraFixation]
  ring_nf

theorem moran_limit_eq_kimuraFixation (σ x : ℝ) :
    (1 - Real.exp (-(σ * x))) / (1 - Real.exp (-σ)) = kimuraFixation (σ / 2) x := by
  unfold kimuraFixation
  rw [show 2 * (σ / 2) * x = σ * x by ring, show 2 * (σ / 2) = σ by ring]

/-- Source: moran1958; kimura1962, p. 715, eq. (8). -/
theorem tendsto_moranFixProb_kimuraFixation {σ x : ℝ} (hσ : σ ≠ 0) (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1) :
    Tendsto (fun N : ℕ => moranFixProb N (1 + σ / N) ⌊x * N⌋₊) atTop
      (𝓝 (kimuraFixation (σ / 2) x)) := by
  rw [← moran_limit_eq_kimuraFixation]
  exact tendsto_moranFixProb_kimura hσ hx0 hx1

end Rhone.Diffusion
