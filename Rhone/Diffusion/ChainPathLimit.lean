/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Diffusion.ChainPathMeasurable
public import Rhone.Diffusion.InterpolatedRiemann
public import Rhone.Diffusion.PathTightness
public import Rhone.MarkovChain.ChainDynkin
public import Rhone.Diffusion.GeneratorLimit
public import Rhone.Diffusion.MartingaleProblem
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Limits of rescaled chain paths solve the martingale problem

Source: ethier_kurtz1986, ch. 4, sec. 8, ch. 3, sec. 7, sec. 10. -/

@[expose] public section

namespace Rhone.Diffusion

open MeasureTheory Filter Topology Set MarkovChain Analysis Probability
open scoped NNReal BoundedContinuousFunction

noncomputable def martingaleTest (f g : ℝ → ℝ) (s t : ℝ≥0) {k : ℕ} (r : Fin k → ℝ≥0)
    (h : (Fin k → ℝ) →ᵇ ℝ) (w : C(ℝ≥0, ℝ)) : ℝ :=
  (f (clampUnit (w t)) - f (clampUnit (w s)) -
    ∫ u in (s : ℝ)..t, g (clampUnit (w u.toNNReal))) * h (fun j => w (r j))

theorem continuous_martingaleTest {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (s t : ℝ≥0) {k : ℕ} (r : Fin k → ℝ≥0) (h : (Fin k → ℝ) →ᵇ ℝ) :
    Continuous (martingaleTest f g s t r h) := by
  unfold martingaleTest
  have hev : ∀ v : ℝ≥0, Continuous fun w : C(ℝ≥0, ℝ) => w v := fun v => continuous_eval_const v
  have hjoint : Continuous fun p : C(ℝ≥0, ℝ) × ℝ => g (clampUnit (p.1 p.2.toNNReal)) :=
    hg.comp (continuous_clampUnit.comp (continuous_eval.comp
      (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))))
  have hint : Continuous fun w : C(ℝ≥0, ℝ) =>
      ∫ u in (s : ℝ)..t, g (clampUnit (w u.toNNReal)) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (w : C(ℝ≥0, ℝ)) (u : ℝ) => g (clampUnit (w u.toNNReal))) hjoint _ _
  refine (((hf.comp (continuous_clampUnit.comp (hev t))).sub
    (hf.comp (continuous_clampUnit.comp (hev s)))).sub hint).mul ?_
  exact h.continuous.comp (continuous_pi fun j => hev (r j))

theorem exists_bound_martingaleTest {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (s t : ℝ≥0) {k : ℕ} (r : Fin k → ℝ≥0) (h : (Fin k → ℝ) →ᵇ ℝ) :
    ∃ B, ∀ w, ‖martingaleTest f g s t r h w‖ ≤ B := by
  obtain ⟨Bf, hBf⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hf.continuousOn (s := Icc (0 : ℝ) 1))
  obtain ⟨Bg, hBg⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hg.continuousOn (s := Icc (0 : ℝ) 1))
  refine ⟨(2 * Bf + Bg * |(t : ℝ) - s|) * ‖h‖, fun w => ?_⟩
  unfold martingaleTest
  rw [norm_mul]
  refine mul_le_mul ?_ (h.norm_coe_le_norm _) (norm_nonneg _) ?_
  · have hi := intervalIntegral.norm_integral_le_of_norm_le_const (a := (s : ℝ)) (b := t)
      (C := Bg) (f := fun u => g (clampUnit (w u.toNNReal))) (fun u _ => hBg _ (clampUnit_mem _))
    have h1 := hBf _ (clampUnit_mem (w t))
    have h2 := hBf _ (clampUnit_mem (w s))
    calc _ ≤ ‖f (clampUnit (w t))‖ + ‖f (clampUnit (w s))‖ +
          ‖∫ u in (s : ℝ)..t, g (clampUnit (w u.toNNReal))‖ :=
        (norm_sub_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
      _ ≤ 2 * Bf + Bg * |(t : ℝ) - s| := by linarith
  · have h0 := (norm_nonneg _).trans (hBf 0 ⟨le_rfl, zero_le_one⟩)
    have h1 := (norm_nonneg _).trans (hBg 0 ⟨le_rfl, zero_le_one⟩)
    positivity

noncomputable def martingaleTestBCF {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (s t : ℝ≥0) {k : ℕ} (r : Fin k → ℝ≥0) (h : (Fin k → ℝ) →ᵇ ℝ) : C(ℝ≥0, ℝ) →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (martingaleTest f g s t r h)
    (continuous_martingaleTest hf hg s t r h) _
    (exists_bound_martingaleTest hf hg s t r h).choose_spec

theorem martingaleTestBCF_apply {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (s t : ℝ≥0) {k : ℕ} (r : Fin k → ℝ≥0) (h : (Fin k → ℝ) →ᵇ ℝ) (w : C(ℝ≥0, ℝ)) :
    martingaleTestBCF hf hg s t r h w = martingaleTest f g s t r h w := rfl

theorem martingaleTest_rescaledPath (f g : ℝ → ℝ) (s t : ℝ≥0) {k : ℕ} (r : Fin k → ℝ≥0)
    (h : (Fin k → ℝ) →ᵇ ℝ) {a : ℕ → ℝ} (ha : ∀ m, a m ∈ Icc (0 : ℝ) 1) (τ : ℝ) :
    martingaleTest f g s t r h (rescaledPath τ a) =
      (f (interpolate a (τ * t)) - f (interpolate a (τ * s)) -
        ∫ u in (s : ℝ)..t, g (interpolate a (τ * u))) *
        h (fun j => interpolate a (τ * r j)) := by
  have hc : ∀ u, clampUnit (interpolate a u) = interpolate a u :=
    fun u => clampUnit_of_mem (interpolate_mem_Icc ha u)
  unfold martingaleTest
  simp only [rescaledPath_apply, hc]
  congr 2
  refine intervalIntegral.integral_congr fun u hu => ?_
  have hu0 : 0 ≤ u := (le_min s.2 t.2).trans hu.1
  simp only [Real.coe_toNNReal u hu0]

theorem tendsto_zero_of_forall_eventually_abs_le {u : ℕ → ℝ} (c : ℝ)
    (h : ∀ ε > 0, ∀ᶠ n in atTop, |u n| ≤ c * ε) : Tendsto u atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  have hc : 0 < |c| + 1 := by positivity
  filter_upwards [h (δ / (2 * (|c| + 1))) (by positivity)] with n hn
  rw [Real.dist_eq, sub_zero]
  have h1 : c * (δ / (2 * (|c| + 1))) ≤ (|c| + 1) * (δ / (2 * (|c| + 1))) :=
    mul_le_mul_of_nonneg_right (by linarith [le_abs_self c]) (by positivity)
  have h2 : (|c| + 1) * (δ / (2 * (|c| + 1))) = δ / 2 := by
    field_simp
  linarith

theorem defect_tail_le {K1 T τ η ε E S M : ℝ} (hK1 : 0 ≤ K1) (hT : 0 ≤ T) (hτ : 0 < τ)
    (hη : 0 < η) (hε : 0 < ε) (hM0 : 0 ≤ M) (hM : M ≤ τ * (T + 1)) (hS : S ≤ M * (E / τ))
    (hE : |E| ≤ ε * η ^ 4 / (K1 * (T + 1) + 1)) : K1 * (S / η ^ 4) ≤ ε := by
  have hη4 : 0 < η ^ 4 := pow_pos hη 4
  have hden : 0 < K1 * (T + 1) + 1 := by positivity
  have h1 : M * (E / τ) ≤ (T + 1) * |E| := by
    have hMt : M / τ ≤ T + 1 := by rw [div_le_iff₀ hτ]; linarith
    calc M * (E / τ) = M / τ * E := by ring
      _ ≤ M / τ * |E| := mul_le_mul_of_nonneg_left (le_abs_self E) (by positivity)
      _ ≤ (T + 1) * |E| := mul_le_mul_of_nonneg_right hMt (abs_nonneg E)
  have h2 : K1 * S ≤ K1 * ((T + 1) * |E|) := mul_le_mul_of_nonneg_left (hS.trans h1) hK1
  have h3 : K1 * ((T + 1) * |E|) ≤ K1 * (T + 1) * (ε * η ^ 4 / (K1 * (T + 1) + 1)) := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_left hE (by positivity)
  have h4 : K1 * (T + 1) * (ε * η ^ 4 / (K1 * (T + 1) + 1)) ≤ ε * η ^ 4 := by
    rw [mul_div_assoc', div_le_iff₀ hden]
    have : 0 ≤ ε * η ^ 4 := by positivity
    nlinarith
  rw [mul_div_assoc', div_le_iff₀ hη4]
  linarith

variable {Sₙ : ℕ → Type*} [∀ n, Fintype (Sₙ n)] [∀ n, MeasurableSpace (Sₙ n)]
  [∀ n, DiscreteMeasurableSpace (Sₙ n)]

theorem tendsto_integral_martingaleTest (C : ∀ n, FinChain (Sₙ n)) (y : ∀ n, Sₙ n → ℝ)
    (τ : ℕ → ℝ) (x : ∀ n, Sₙ n) (hy01 : ∀ n z, y n z ∈ Icc (0 : ℝ) 1)
    (hτ : Tendsto τ atTop atTop) (e : ℕ → ℝ)
    (hq : ∀ᶠ n in atTop, ∀ z, (C n).expect (fun w => (y n w - y n z) ^ 4) z ≤ e n / τ n)
    (he : Tendsto e atTop (𝓝 0)) {A : (ℝ → ℝ) → ℝ → ℝ} {D : Set (ℝ → ℝ)}
    (hA : GeneratorLimit C τ y A D) {f : ℝ → ℝ} (hfD : f ∈ D) (hf : Continuous f)
    (hg : Continuous (A f)) {s t : ℝ≥0} (hst : s ≤ t) {k : ℕ} (r : Fin k → ℝ≥0)
    (hr : ∀ j, r j ≤ s) (h : (Fin k → ℝ) →ᵇ ℝ) :
    Tendsto (fun n => ∫ ω, martingaleTest f (A f) s t r h
      (rescaledPath (τ n) fun m => y n (ω m)) ∂(C n).pathLaw (x n)) atTop (𝓝 0) := by
  obtain ⟨Bf, hBf'⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hf.continuousOn (s := Icc (0 : ℝ) 1))
  obtain ⟨Bg, hBg'⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hg.continuousOn (s := Icc (0 : ℝ) 1))
  have hBf : ∀ z ∈ Icc (0 : ℝ) 1, |f z| ≤ Bf := fun z hz => by
    rw [← Real.norm_eq_abs]; exact hBf' z hz
  have hBg : ∀ z ∈ Icc (0 : ℝ) 1, |A f z| ≤ Bg := fun z hz => by
    rw [← Real.norm_eq_abs]; exact hBg' z hz
  have hBf0 : 0 ≤ Bf := (abs_nonneg _).trans (hBf 0 ⟨le_rfl, zero_le_one⟩)
  have hBg0 : 0 ≤ Bg := (abs_nonneg _).trans (hBg 0 ⟨le_rfl, zero_le_one⟩)
  have hfu := isCompact_Icc.uniformContinuousOn_of_continuous (hf.continuousOn
    (s := Icc (0 : ℝ) 1))
  have hgu := isCompact_Icc.uniformContinuousOn_of_continuous (hg.continuousOn
    (s := Icc (0 : ℝ) 1))
  rw [Metric.uniformContinuousOn_iff_le] at hfu hgu
  have hT : (0 : ℝ) ≤ t := t.2
  refine tendsto_zero_of_forall_eventually_abs_le (‖h‖ * (2 * (t : ℝ) + 6)) fun ε hε => ?_
  obtain ⟨η1, hη1, hf1⟩ := hfu ε hε
  obtain ⟨η2, hη2, hg2⟩ := hgu ε hε
  set η := min η1 η2 with hη_def
  have hη : 0 < η := lt_min hη1 hη2
  have hfη : ∀ z ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (0 : ℝ) 1, |z - w| ≤ η → |f z - f w| ≤ ε :=
    fun z hz w hw hzw => by
      have := hf1 z hz w hw (by rw [Real.dist_eq]; exact hzw.trans (min_le_left _ _))
      rwa [Real.dist_eq] at this
  have hgη : ∀ z ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (0 : ℝ) 1, |z - w| ≤ η →
      |A f z - A f w| ≤ ε := fun z hz w hw hzw => by
    have := hg2 z hz w hw (by rw [Real.dist_eq]; exact hzw.trans (min_le_right _ _))
    rwa [Real.dist_eq] at this
  set K1 : ℝ := 4 * Bf + (2 * (t : ℝ) + 1) * Bg + ((t : ℝ) + 1) * ε with hK1_def
  have hK1 : 0 ≤ K1 := by positivity
  have hev4 : ∀ᶠ n in atTop, |e n| ≤ ε * η ^ 4 / (K1 * ((t : ℝ) + 1) + 1) := by
    have he' : Tendsto (fun n => |e n|) atTop (𝓝 0) := by simpa using he.abs
    exact (he'.eventually (ge_mem_nhds (by positivity)))
  obtain ⟨B, hB⟩ := exists_bound_martingaleTest hf hg s t r h
  filter_upwards [hτ.eventually_ge_atTop 1, hτ.eventually_ge_atTop (2 * Bg / ε),
    hA.eventually_le hfD hε, hev4, hq] with n h1 h2 h3 h4 h5
  have hτ0 : 0 < τ n := by linarith
  have hBgτ : 2 * Bg / τ n ≤ ε := by
    rw [div_le_iff₀ hτ0]
    have := (div_le_iff₀ hε).1 h2
    linarith
  set k0 := ⌈τ n * s⌉₊ with hk0
  set mt := ⌈τ n * t⌉₊ with hmt
  have hkm : k0 ≤ mt := Nat.ceil_mono (mul_le_mul_of_nonneg_left (by exact_mod_cast hst) hτ0.le)
  have hm2 : (mt : ℝ) < τ n * t + 1 := Nat.ceil_lt_add_one (by positivity)
  have hu : ∀ j, τ n * (r j : ℝ) ≤ k0 := fun j =>
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hr j) hτ0.le).trans (Nat.le_ceil _)
  set H : (ℕ → Sₙ n) → ℝ := fun ω => h (fun j => interpolate (fun l => y n (ω l)) (τ n * r j))
    with hH_def
  have hHv : Measurable[Filtration.piLE (X := fun _ : ℕ => Sₙ n) k0]
      fun ω : ℕ → Sₙ n => fun j => interpolate (fun l => y n (ω l)) (τ n * r j) :=
    by
      let _ : MeasurableSpace (ℕ → Sₙ n) := Filtration.piLE (X := fun _ : ℕ => Sₙ n) k0
      exact Measurable.of_eval fun j => measurable_interpolate_piLE (y n) (hu j)
  have hHm : StronglyMeasurable[Filtration.piLE (X := fun _ : ℕ => Sₙ n) k0] H :=
    (h.continuous.measurable.comp hHv).stronglyMeasurable
  have hHmeas : Measurable H := hHm.measurable.mono (Filtration.piLE.le _) le_rfl
  have hHB : ∀ ω, |H ω| ≤ ‖h‖ := fun ω => by
    rw [← Real.norm_eq_abs]
    exact h.norm_coe_le_norm _
  have hD0 := (C n).integral_mul_dynkin (x n) (f ∘ y n) hHm hHB mt hkm
  have hDint := (C n).integrable_mul_dynkin (x n) (f ∘ y n) k0 hHmeas hHB mt
  have hMint : Integrable (fun ω : ℕ → Sₙ n => martingaleTest f (A f) s t r h
      (rescaledPath (τ n) fun m => y n (ω m))) ((C n).pathLaw (x n)) :=
    Integrable.of_bound (((continuous_martingaleTest hf hg s t r h).measurable.comp
      (measurable_rescaledPath (y n) (τ n))).aestronglyMeasurable) B
      (Eventually.of_forall fun ω => hB _)
  have hgen : ∀ z, (C n).expect (f ∘ y n) z - (f ∘ y n) z =
      (A f (y n z) + generatorError C τ y A f n z) / τ n := by
    intro z
    rw [eq_div_iff hτ0.ne']
    unfold generatorError
    simp only [Function.comp_apply]
    ring
  have hpt : ∀ ω : ℕ → Sₙ n, |martingaleTest f (A f) s t r h
      (rescaledPath (τ n) fun m => y n (ω m)) -
      H ω * ((f ∘ y n) (ω mt) - (f ∘ y n) (ω k0) -
        ∑ l ∈ Finset.Ico k0 mt, ((C n).expect (f ∘ y n) (ω l) - (f ∘ y n) (ω l)))| ≤
      ‖h‖ * ((2 * (t : ℝ) + 5) * ε + K1 *
        ∑ l ∈ Finset.range mt, (y n (ω (l + 1)) - y n (ω l)) ^ 4 / η ^ 4) := by
    intro ω
    have ha : ∀ l, (fun l => y n (ω l)) l ∈ Icc (0 : ℝ) 1 := fun l => hy01 n (ω l)
    have hrepr : martingaleTest f (A f) s t r h (rescaledPath (τ n) fun m => y n (ω m)) =
        _ * H ω := martingaleTest_rescaledPath f (A f) s t r h ha (τ n)
    rw [hrepr]
    have hdef := abs_martingale_defect_le ha h1 (s := s) (t := t) (NNReal.coe_nonneg s)
      (by exact_mod_cast hst) hη hε.le hg hBf hBg hBgτ hfη hgη
      (fun l => generatorError C τ y A f n (ω l)) (fun l => h3 (ω l))
    have hs : ∑ l ∈ Finset.Ico k0 mt, ((C n).expect (f ∘ y n) (ω l) - (f ∘ y n) (ω l)) =
        ∑ l ∈ Finset.Ico k0 mt, (A f (y n (ω l)) + generatorError C τ y A f n (ω l)) / τ n :=
      Finset.sum_congr rfl fun l _ => hgen (ω l)
    rw [hs]
    simp only [Function.comp_apply]
    have e : ∀ P Q : ℝ, P * H ω - H ω * Q = H ω * (P - Q) := fun P Q => by ring
    rw [e, abs_mul]
    exact mul_le_mul (hHB ω) hdef (abs_nonneg _) (norm_nonneg _)
  have hstep : ∀ l, ∫ ω, (y n (ω (l + 1)) - y n (ω l)) ^ 4 ∂(C n).pathLaw (x n) ≤ e n / τ n :=
    fun l => (C n).integral_step_pow_four_le (y n) h5 (x n) l
  have hIs : ∀ l, Integrable (fun ω : ℕ → Sₙ n => (y n (ω (l + 1)) - y n (ω l)) ^ 4 / η ^ 4)
      ((C n).pathLaw (x n)) := fun l => ((C n).integrable_step_pow_four (y n) (x n) l).div_const _
  have hIsum : Integrable (fun ω : ℕ → Sₙ n =>
      ∑ l ∈ Finset.range mt, (y n (ω (l + 1)) - y n (ω l)) ^ 4 / η ^ 4) ((C n).pathLaw (x n)) :=
    integrable_finsetSum _ fun l _ => hIs l
  set Ssum : ℝ := ∑ l ∈ Finset.range mt, ∫ ω, (y n (ω (l + 1)) - y n (ω l)) ^ 4
    ∂(C n).pathLaw (x n) with hSsum
  have hSle : Ssum ≤ mt * (e n / τ n) := by
    calc Ssum ≤ ∑ _l ∈ Finset.range mt, e n / τ n := Finset.sum_le_sum fun l _ => hstep l
      _ = mt * (e n / τ n) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hboundint : ∫ ω, ‖h‖ * ((2 * (t : ℝ) + 5) * ε + K1 *
      ∑ l ∈ Finset.range mt, (y n (ω (l + 1)) - y n (ω l)) ^ 4 / η ^ 4) ∂(C n).pathLaw (x n) =
      ‖h‖ * ((2 * (t : ℝ) + 5) * ε + K1 * (Ssum / η ^ 4)) := by
    rw [integral_const_mul, integral_add (integrable_const _) (hIsum.const_mul K1),
      integral_const, integral_const_mul K1, integral_finsetSum _ fun l _ => hIs l, hSsum,
      Finset.sum_div]
    simp only [integral_div, probReal_univ, one_smul]
  have htail : K1 * (Ssum / η ^ 4) ≤ ε :=
    defect_tail_le hK1 hT hτ0 hη hε (Nat.cast_nonneg mt)
      (by
        have e2 : τ n * ((t : ℝ) + 1) = τ n * t + τ n := by ring
        linarith) hSle h4
  have hdiff : ∫ ω, martingaleTest f (A f) s t r h (rescaledPath (τ n) fun m => y n (ω m))
      ∂(C n).pathLaw (x n) = ∫ ω, (martingaleTest f (A f) s t r h
        (rescaledPath (τ n) fun m => y n (ω m)) -
      H ω * ((f ∘ y n) (ω mt) - (f ∘ y n) (ω k0) -
        ∑ l ∈ Finset.Ico k0 mt, ((C n).expect (f ∘ y n) (ω l) - (f ∘ y n) (ω l))))
      ∂(C n).pathLaw (x n) := by
    rw [integral_sub hMint hDint, hD0, sub_zero]
  rw [hdiff]
  calc _ ≤ ∫ ω, |martingaleTest f (A f) s t r h (rescaledPath (τ n) fun m => y n (ω m)) -
        H ω * ((f ∘ y n) (ω mt) - (f ∘ y n) (ω k0) -
          ∑ l ∈ Finset.Ico k0 mt, ((C n).expect (f ∘ y n) (ω l) - (f ∘ y n) (ω l)))|
        ∂(C n).pathLaw (x n) := abs_integral_le_integral_abs
    _ ≤ ∫ ω, ‖h‖ * ((2 * (t : ℝ) + 5) * ε + K1 *
        ∑ l ∈ Finset.range mt, (y n (ω (l + 1)) - y n (ω l)) ^ 4 / η ^ 4)
        ∂(C n).pathLaw (x n) :=
        integral_mono (hMint.sub hDint).abs
          (((integrable_const _).add (hIsum.const_mul K1)).const_mul _) hpt
    _ = ‖h‖ * ((2 * (t : ℝ) + 5) * ε + K1 * (Ssum / η ^ 4)) := hboundint
    _ ≤ ‖h‖ * ((2 * (t : ℝ) + 5) * ε + ε) :=
        mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
    _ = ‖h‖ * (2 * (t : ℝ) + 6) * ε := by ring

noncomputable def chainPathLaw {S : Type*} [Fintype S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] (C : FinChain S) (g : S → ℝ) (τ : ℝ) (x : S) :
    ProbabilityMeasure C(ℝ≥0, ℝ) :=
  ⟨(C.pathLaw x).map fun ω => rescaledPath τ fun m => g (ω m),
    by infer_instance⟩

theorem integral_chainPathLaw {S : Type*} [Fintype S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] (C : FinChain S) (g : S → ℝ) (τ : ℝ) (x : S)
    {F : C(ℝ≥0, ℝ) → ℝ} (hF : Continuous F) :
    ∫ w, F w ∂(chainPathLaw C g τ x : Measure C(ℝ≥0, ℝ)) =
      ∫ ω, F (rescaledPath τ fun m => g (ω m)) ∂C.pathLaw x :=
  integral_map (measurable_rescaledPath g τ).aemeasurable hF.aestronglyMeasurable

theorem integral_eq_zero_of_mapClusterPt {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] {μ : ℕ → ProbabilityMeasure E} {Q : ProbabilityMeasure E}
    (hQ : MapClusterPt Q atTop μ) (Φ : E →ᵇ ℝ)
    (h : Tendsto (fun n => ∫ w, Φ w ∂(μ n : Measure E)) atTop (𝓝 0)) :
    ∫ w, Φ w ∂(Q : Measure E) = 0 := by
  have hc := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction Φ).continuousAt
    (x := Q)
  have h2 : ClusterPt (∫ w, Φ w ∂(Q : Measure E))
      (map (fun n => ∫ w, Φ w ∂(μ n : Measure E)) atTop) := hQ.continuousAt_comp hc
  exact eq_of_nhds_neBot (h2.mono h).neBot

theorem isMartingaleSolution_of_mapClusterPt (C : ∀ n, FinChain (Sₙ n)) (y : ∀ n, Sₙ n → ℝ)
    (τ : ℕ → ℝ) (x : ∀ n, Sₙ n) (hy01 : ∀ n z, y n z ∈ Icc (0 : ℝ) 1)
    (hτ : Tendsto τ atTop atTop) (e : ℕ → ℝ)
    (hq : ∀ᶠ n in atTop, ∀ z, (C n).expect (fun w => (y n w - y n z) ^ 4) z ≤ e n / τ n)
    (he : Tendsto e atTop (𝓝 0)) {A : (ℝ → ℝ) → ℝ → ℝ} {D : Set (ℝ → ℝ)}
    (hA : GeneratorLimit C τ y A D) (hD : ∀ f ∈ D, Continuous f ∧ Continuous (A f)) {x₀ : ℝ}
    (hx : Tendsto (fun n => y n (x n)) atTop (𝓝 x₀)) {Q : ProbabilityMeasure C(ℝ≥0, ℝ)}
    (hQ : MapClusterPt Q atTop fun n => chainPathLaw (C n) (y n) (τ n) (x n)) :
    IsMartingaleSolution A D (Icc 0 1) x₀ (Q : Measure C(ℝ≥0, ℝ)) := by
  have hmem_t : ∀ t : ℝ≥0, ∀ᵐ w ∂(Q : Measure C(ℝ≥0, ℝ)), w t ∈ Icc (0 : ℝ) 1 := by
    intro t
    have hcont : Continuous fun w : C(ℝ≥0, ℝ) => min 1 |w t - clampUnit (w t)| :=
      continuous_const.min (((continuous_eval_const t).sub
        (continuous_clampUnit.comp (continuous_eval_const t))).abs)
    have hnn : ∀ w : C(ℝ≥0, ℝ), 0 ≤ min 1 |w t - clampUnit (w t)| :=
      fun w => le_min zero_le_one (abs_nonneg _)
    obtain ⟨Φ, hΦ⟩ : ∃ Φ : C(ℝ≥0, ℝ) →ᵇ ℝ, ∀ w, Φ w = min 1 |w t - clampUnit (w t)| :=
      ⟨BoundedContinuousFunction.ofNormedAddCommGroup _ hcont 1
        fun w => by rw [Real.norm_eq_abs, abs_of_nonneg (hnn w)]; exact min_le_left _ _,
        fun w => rfl⟩
    have hlim : Tendsto (fun n => ∫ w, Φ w
        ∂(chainPathLaw (C n) (y n) (τ n) (x n) : Measure C(ℝ≥0, ℝ))) atTop (𝓝 0) := by
      refine tendsto_const_nhds.congr fun n => ?_
      rw [integral_chainPathLaw _ _ _ _ Φ.continuous]
      symm
      refine integral_eq_zero_of_ae (Eventually.of_forall fun ω => ?_)
      change Φ (rescaledPath (τ n) fun m => y n (ω m)) = 0
      rw [hΦ, clampUnit_of_mem (rescaledPath_mem_Icc (fun m => hy01 n (ω m)) _ t), sub_self,
        abs_zero, min_eq_right zero_le_one]
    have h0 := integral_eq_zero_of_mapClusterPt hQ Φ hlim
    have hint : Integrable (fun w : C(ℝ≥0, ℝ) => Φ w) (Q : Measure C(ℝ≥0, ℝ)) := Φ.integrable _
    rw [integral_eq_zero_iff_of_nonneg (fun w => by rw [hΦ]; exact hnn w) hint] at h0
    filter_upwards [h0] with w hw
    change Φ w = 0 at hw
    rw [hΦ] at hw
    have habs : |w t - clampUnit (w t)| = 0 := by
      rcases le_total 1 |w t - clampUnit (w t)| with h1 | h1
      · rw [min_eq_left h1] at hw
        exact absurd hw one_ne_zero
      · rwa [min_eq_right h1] at hw
    rw [abs_eq_zero, sub_eq_zero] at habs
    rw [habs]
    exact clampUnit_mem _
  have hmem : ∀ᵐ w ∂(Q : Measure C(ℝ≥0, ℝ)), ∀ t, w t ∈ Icc (0 : ℝ) 1 := by
    obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq ℝ≥0
    filter_upwards [ae_all_iff.2 fun i => hmem_t (u i)] with w hw t
    have hcl : IsClosed {v : ℝ≥0 | w v ∈ Icc (0 : ℝ) 1} := isClosed_Icc.preimage w.continuous
    have hsub : closure (range u) ⊆ {v : ℝ≥0 | w v ∈ Icc (0 : ℝ) 1} :=
      closure_minimal (range_subset_iff.2 hw) hcl
    exact hsub (by rw [hu.closure_range]; exact mem_univ t)
  refine ⟨inferInstance, ?_, hmem, ?_⟩
  · have hcont : Continuous fun w : C(ℝ≥0, ℝ) => min 1 |w 0 - x₀| :=
      continuous_const.min (((continuous_eval_const 0).sub continuous_const).abs)
    have hnn : ∀ w : C(ℝ≥0, ℝ), 0 ≤ min 1 |w 0 - x₀| :=
      fun w => le_min zero_le_one (abs_nonneg _)
    obtain ⟨Φ, hΦ⟩ : ∃ Φ : C(ℝ≥0, ℝ) →ᵇ ℝ, ∀ w, Φ w = min 1 |w 0 - x₀| :=
      ⟨BoundedContinuousFunction.ofNormedAddCommGroup _ hcont 1
        fun w => by rw [Real.norm_eq_abs, abs_of_nonneg (hnn w)]; exact min_le_left _ _,
        fun w => rfl⟩
    have hval : ∀ n, ∫ w, Φ w ∂(chainPathLaw (C n) (y n) (τ n) (x n) : Measure C(ℝ≥0, ℝ)) =
        min 1 |y n (x n) - x₀| := by
      intro n
      classical
      rw [integral_chainPathLaw _ _ _ _ Φ.continuous]
      have e : ∀ ω : ℕ → Sₙ n, Φ (rescaledPath (τ n) fun m => y n (ω m)) =
          (fun z => min 1 |y n z - x₀|) (ω 0) := by
        intro ω
        rw [hΦ, rescaledPath_apply, NNReal.coe_zero, mul_zero, interpolate_of_nonpos _ le_rfl]
      calc ∫ ω, Φ (rescaledPath (τ n) fun m => y n (ω m)) ∂(C n).pathLaw (x n)
          = ∫ ω, (fun z => min 1 |y n z - x₀|) (ω 0) ∂(C n).pathLaw (x n) :=
            integral_congr_ae (Eventually.of_forall e)
        _ = min 1 |y n (x n) - x₀| := by
            exact ((C n).integral_eval 0 (fun z => min 1 |y n z - x₀|) (x n)).trans
              (by rw [FinChain.expectN_zero])
    have hlim : Tendsto (fun n => ∫ w, Φ w
        ∂(chainPathLaw (C n) (y n) (τ n) (x n) : Measure C(ℝ≥0, ℝ))) atTop (𝓝 0) := by
      simp_rw [hval]
      have hc : Continuous fun z : ℝ => min 1 |z - x₀| :=
        continuous_const.min ((continuous_id.sub continuous_const).abs)
      have := (hc.tendsto x₀).comp hx
      rw [sub_self, abs_zero, min_eq_right zero_le_one] at this
      exact this
    have h0 := integral_eq_zero_of_mapClusterPt hQ Φ hlim
    have hint : Integrable (fun w : C(ℝ≥0, ℝ) => Φ w) (Q : Measure C(ℝ≥0, ℝ)) := Φ.integrable _
    rw [integral_eq_zero_iff_of_nonneg (fun w => by rw [hΦ]; exact hnn w) hint] at h0
    filter_upwards [h0] with w hw
    change Φ w = 0 at hw
    rw [hΦ] at hw
    have habs : |w 0 - x₀| = 0 := by
      rcases le_total 1 |w 0 - x₀| with h1 | h1
      · rw [min_eq_left h1] at hw
        exact absurd hw one_ne_zero
      · rwa [min_eq_right h1] at hw
    rwa [abs_eq_zero, sub_eq_zero] at habs
  · intro f hfD s t hst k r hr h
    obtain ⟨hf, hg⟩ := hD f hfD
    have hlim : Tendsto (fun n => ∫ w, martingaleTestBCF hf hg s t r h w
        ∂(chainPathLaw (C n) (y n) (τ n) (x n) : Measure C(ℝ≥0, ℝ))) atTop (𝓝 0) := by
      have := tendsto_integral_martingaleTest C y τ x hy01 hτ e hq he hA hfD hf hg hst r hr h
      refine this.congr fun n => ?_
      rw [integral_chainPathLaw _ _ _ _ (martingaleTestBCF hf hg s t r h).continuous]
      rfl
    have h0 := integral_eq_zero_of_mapClusterPt hQ _ hlim
    rw [← h0]
    refine integral_congr_ae ?_
    filter_upwards [hmem] with w hw
    have hc : ∀ v, clampUnit (w v) = w v := fun v => clampUnit_of_mem (hw v)
    rw [martingaleTestBCF_apply]
    unfold martingaleTest
    simp only [hc]

theorem isTightMeasureSet_chainPathLaw (C : ∀ n, FinChain (Sₙ n)) (y : ∀ n, Sₙ n → ℝ)
    (τ : ℕ → ℝ) (x : ∀ n, Sₙ n) (hy : ∀ n, (C n).IsHarmonic (y n))
    (hy01 : ∀ n z, y n z ∈ Icc (0 : ℝ) 1) (hτ : Tendsto τ atTop atTop) (c : ℝ) (e : ℕ → ℝ)
    (hv : ∀ᶠ n in atTop, ∀ z, (C n).expect (fun w => (y n w - y n z) ^ 2) z ≤ c / τ n)
    (hq : ∀ᶠ n in atTop, ∀ z, (C n).expect (fun w => (y n w - y n z) ^ 4) z ≤ e n / τ n)
    (he : Tendsto e atTop (𝓝 0)) :
    IsTightMeasureSet {((μ : ProbabilityMeasure C(ℝ≥0, ℝ)) : Measure C(ℝ≥0, ℝ)) |
      μ ∈ range fun n => chainPathLaw (C n) (y n) (τ n) (x n)} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨δ, hδ, hδn⟩ := exists_unitModulus_of_moments C y τ x hy hy01 hτ c e hv hq he hε.ne'
  refine ⟨unitModulusSet δ, isCompact_unitModulusSet hδ, ?_⟩
  rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
  have hK := (isCompact_unitModulusSet hδ).isClosed.measurableSet.compl
  calc ((chainPathLaw (C n) (y n) (τ n) (x n) : ProbabilityMeasure C(ℝ≥0, ℝ)) :
        Measure C(ℝ≥0, ℝ)) (unitModulusSet δ)ᶜ
      = (C n).pathLaw (x n)
          {ω | ¬ UnitModulus δ (rescaledPath (τ n) fun m => y n (ω m))} := by
        change ((C n).pathLaw (x n)).map _ _ = _
        rw [Measure.map_apply (measurable_rescaledPath (y n) (τ n)) hK]
        rfl
    _ ≤ ε := hδn n

theorem exists_isMartingaleSolution_of_chains (C : ∀ n, FinChain (Sₙ n)) (y : ∀ n, Sₙ n → ℝ)
    (τ : ℕ → ℝ) (x : ∀ n, Sₙ n) (hy : ∀ n, (C n).IsHarmonic (y n))
    (hy01 : ∀ n z, y n z ∈ Icc (0 : ℝ) 1) (hτ : Tendsto τ atTop atTop) (c : ℝ) (e : ℕ → ℝ)
    (hv : ∀ᶠ n in atTop, ∀ z, (C n).expect (fun w => (y n w - y n z) ^ 2) z ≤ c / τ n)
    (hq : ∀ᶠ n in atTop, ∀ z, (C n).expect (fun w => (y n w - y n z) ^ 4) z ≤ e n / τ n)
    (he : Tendsto e atTop (𝓝 0)) {A : (ℝ → ℝ) → ℝ → ℝ} {D : Set (ℝ → ℝ)}
    (hA : GeneratorLimit C τ y A D) (hD : ∀ f ∈ D, Continuous f ∧ Continuous (A f)) {x₀ : ℝ}
    (hx : Tendsto (fun n => y n (x n)) atTop (𝓝 x₀)) :
    ∃ P : Measure C(ℝ≥0, ℝ), IsMartingaleSolution A D (Icc 0 1) x₀ P := by
  have hcomp := isCompact_closure_of_isTightMeasureSet
    (isTightMeasureSet_chainPathLaw C y τ x hy hy01 hτ c e hv hq he)
  obtain ⟨Q, -, hQ⟩ := hcomp.exists_mapClusterPt (f := atTop)
    (u := fun n => chainPathLaw (C n) (y n) (τ n) (x n))
    (tendsto_principal.2 (Eventually.of_forall fun n => subset_closure ⟨n, rfl⟩))
  exact ⟨Q, isMartingaleSolution_of_mapClusterPt C y τ x hy01 hτ e hq he hA hD hx hQ⟩

theorem tendsto_integral_of_chains (C : ∀ n, FinChain (Sₙ n)) (y : ∀ n, Sₙ n → ℝ)
    (τ : ℕ → ℝ) (x : ∀ n, Sₙ n) (hy : ∀ n, (C n).IsHarmonic (y n))
    (hy01 : ∀ n z, y n z ∈ Icc (0 : ℝ) 1) (hτ : Tendsto τ atTop atTop) (c : ℝ) (e : ℕ → ℝ)
    (hv : ∀ᶠ n in atTop, ∀ z, (C n).expect (fun w => (y n w - y n z) ^ 2) z ≤ c / τ n)
    (hq : ∀ᶠ n in atTop, ∀ z, (C n).expect (fun w => (y n w - y n z) ^ 4) z ≤ e n / τ n)
    (he : Tendsto e atTop (𝓝 0)) {A : (ℝ → ℝ) → ℝ → ℝ} {D : Set (ℝ → ℝ)}
    (hA : GeneratorLimit C τ y A D) (hD : ∀ f ∈ D, Continuous f ∧ Continuous (A f)) {x₀ : ℝ}
    (hx : Tendsto (fun n => y n (x n)) atTop (𝓝 x₀)) {P : Measure C(ℝ≥0, ℝ)}
    (hP : IsMartingaleSolution A D (Icc 0 1) x₀ P)
    (huniq : ∀ Q, IsMartingaleSolution A D (Icc 0 1) x₀ Q → Q = P) (F : C(ℝ≥0, ℝ) →ᵇ ℝ) :
    Tendsto (fun n => ∫ ω, F (rescaledPath (τ n) fun m => y n (ω m)) ∂(C n).pathLaw (x n))
      atTop (𝓝 (∫ w, F w ∂P)) := by
  have := hP.isProbabilityMeasure
  let P' : ProbabilityMeasure C(ℝ≥0, ℝ) := ⟨P, inferInstance⟩
  have hcomp := isCompact_closure_of_isTightMeasureSet
    (isTightMeasureSet_chainPathLaw C y τ x hy hy01 hτ c e hv hq he)
  have hconv : Tendsto (fun n => chainPathLaw (C n) (y n) (τ n) (x n)) atTop (𝓝 P') :=
    hcomp.tendsto_nhds_of_unique_mapClusterPt
      (Eventually.of_forall fun n => subset_closure ⟨n, rfl⟩)
      fun Q _ hQ => Subtype.ext (huniq _
        (isMartingaleSolution_of_mapClusterPt C y τ x hy01 hτ e hq he hA hD hx hQ))
  have h := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hconv F
  refine h.congr fun n => ?_
  exact integral_chainPathLaw _ _ _ _ F.continuous

end Rhone.Diffusion
