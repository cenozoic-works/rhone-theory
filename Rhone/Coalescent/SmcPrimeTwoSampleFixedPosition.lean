/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeTwoSampleRenewal
public import Rhone.Coalescent.SmcPrimeTwoSampleNoChange
public import Rhone.Coalescent.SmcPrimeTwoSampleInitialHeight
public import Rhone.Coalescent.SmcPrimeSpatialNonexplosion

/-!
# Two samples: the root height at a fixed position of the SMC′ chain

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/

@[expose] public section

namespace Rhone.Coalescent.SmcPrime
open MeasureTheory ProbabilityTheory Set IntervalProcess
open scoped ENNReal

theorem spatialProcess_law_map_eval_zero (N : ℕ) (R : ℝ) (μ₀ : Measure (SpatialState N)) :
    ((spatialProcess N R).law μ₀).map (fun ω => ω 0) = μ₀ := by
  ext s hs
  have h : ∀ z : SpatialState N,
      (spatialProcess N R).traj z ((fun ω : ℕ → SpatialState N => ω 0) ⁻¹' s) =
        s.indicator 1 z := by
    intro z
    rw [← Measure.map_apply (measurable_pi_apply 0) hs]
    change ((spatialProcess N R).pathLaw z).map (fun ω => ω 0) s = _
    rw [Rhone.MarkovChain.DiscreteProcess.map_eval_zero, Measure.dirac_apply' _ hs]
  rw [Measure.map_apply (measurable_pi_apply 0) hs, Rhone.MarkovChain.DiscreteProcess.law,
    Measure.bind_apply (hs.preimage (measurable_pi_apply 0))
      (Kernel.measurable _).aemeasurable, lintegral_congr h, lintegral_indicator_one hs]

theorem spatialProcess_law_lintegral_eval_zero (N : ℕ) (R : ℝ)
    (μ₀ : Measure (SpatialState N)) (F : SpatialState N → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ ω, F (ω 0) ∂(spatialProcess N R).law μ₀ = ∫⁻ z, F z ∂μ₀ := by
  rw [← lintegral_map hF (measurable_pi_apply 0), spatialProcess_law_map_eval_zero]

theorem spatialProcess_law_lintegral_shift (N : ℕ) (R : ℝ) (μ₀ : Measure (SpatialState N))
    (k : ℕ) (F : (ℕ → SpatialState N) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ ω, F (fun j => ω (k + j)) ∂(spatialProcess N R).law μ₀ =
      ∫⁻ ω, ∫⁻ ω', F ω' ∂(spatialProcess N R).pathLaw (ω k)
        ∂(spatialProcess N R).law μ₀ := by
  have hsh := Rhone.MarkovChain.DiscreteProcess.measurable_shift (S := SpatialState N) k
  have hin : Measurable fun w : SpatialState N =>
      ∫⁻ ω', F ω' ∂(spatialProcess N R).traj w := hF.lintegral_kernel
  have hpath : ∀ z : SpatialState N,
      ∫⁻ ω, F (fun j => ω (k + j)) ∂(spatialProcess N R).traj z =
        ∫⁻ ω, ∫⁻ ω', F ω' ∂(spatialProcess N R).traj (ω k)
          ∂(spatialProcess N R).traj z := by
    intro z
    have hshift := spatialProcess_map_shift N R z k
    calc ∫⁻ ω, F (fun j => ω (k + j)) ∂(spatialProcess N R).traj z
        = ∫⁻ ω, F ω ∂((spatialProcess N R).pathLaw z).map (fun ω j => ω (k + j)) :=
          (lintegral_map hF hsh).symm
      _ = ∫⁻ ω, F ω ∂(((spatialProcess N R).pathLaw z).map (fun ω => ω k)).bind
            (spatialProcess N R).traj := by rw [hshift]
      _ = ∫⁻ w, ∫⁻ ω', F ω' ∂(spatialProcess N R).traj w
            ∂((spatialProcess N R).pathLaw z).map (fun ω => ω k) :=
          Measure.lintegral_bind (Kernel.measurable _).aemeasurable hF.aemeasurable
      _ = ∫⁻ ω, ∫⁻ ω', F ω' ∂(spatialProcess N R).traj (ω k)
            ∂(spatialProcess N R).traj z := lintegral_map hin (measurable_pi_apply k)
  have e1 : ∫⁻ ω, F (fun j => ω (k + j)) ∂μ₀.bind (spatialProcess N R).traj =
      ∫⁻ z, ∫⁻ ω, F (fun j => ω (k + j)) ∂(spatialProcess N R).traj z ∂μ₀ :=
    Measure.lintegral_bind (Kernel.measurable _).aemeasurable
      (show Measurable (fun ω : ℕ → SpatialState N => F fun j => ω (k + j)) from
        hF.comp hsh).aemeasurable
  have e2 : ∫⁻ ω, ∫⁻ ω', F ω' ∂(spatialProcess N R).traj (ω k)
        ∂μ₀.bind (spatialProcess N R).traj =
      ∫⁻ z, ∫⁻ ω, ∫⁻ ω', F ω' ∂(spatialProcess N R).traj (ω k)
        ∂(spatialProcess N R).traj z ∂μ₀ :=
    Measure.lintegral_bind (Kernel.measurable _).aemeasurable
      (show Measurable (fun ω : ℕ → SpatialState N =>
        ∫⁻ ω', F ω' ∂(spatialProcess N R).traj (ω k)) from
        hin.comp (measurable_pi_apply k)).aemeasurable
  exact e1.trans ((lintegral_congr hpath).trans e2.symm)

theorem spatialProcess_law_lintegral_step (N : ℕ) (R : ℝ) (μ₀ : Measure (SpatialState N))
    (k : ℕ) (Φ : SpatialState N × SpatialState N → ℝ≥0∞) (hΦ : Measurable Φ) :
    ∫⁻ ω, Φ (ω k, ω (k + 1)) ∂(spatialProcess N R).law μ₀ =
      ∫⁻ ω, ∫⁻ a, Φ (ω k, spatialStep N R (ω k) a) ∂proposalNoiseLaw
        ∂(spatialProcess N R).law μ₀ := by
  have hF : Measurable fun ω : ℕ → SpatialState N => Φ (ω 0, ω 1) :=
    hΦ.comp ((measurable_pi_apply 0).prodMk (measurable_pi_apply 1))
  refine (spatialProcess_law_lintegral_shift N R μ₀ k _ hF).trans
    (lintegral_congr fun ω => ?_)
  rw [spatialProcess_pathLaw_lintegral_first_step N R (ω k) _ hF]
  refine lintegral_congr fun a => ?_
  have hw : Measurable fun w : SpatialState N => Φ (ω k, w) :=
    hΦ.comp (measurable_const.prodMk measurable_id)
  exact spatialProcess_pathLaw_lintegral_eval_zero N R _ _ hw

theorem TwoSampleArray.spatialStep_lintegral_stepOp {T : Tree 2} (hT : TwoSampleArray T)
    {R : ℝ} (hR : 0 < R) (hh : 0 < rootHeight T) (p : ℝ) (φ : ℝ × ℝ → ℝ≥0∞)
    (hφ : Measurable φ) (hφ0 : ∀ q a : ℝ, 1 ≤ q → φ (q, a) = 0) :
    ∫⁻ u, φ ((SmcPrime.spatialStep 2 R (p, T) u).1,
        rootHeight (SmcPrime.spatialStep 2 R (p, T) u).2) ∂proposalNoiseLaw =
      twoSampleStepOp R φ (p, rootHeight T) := by
  by_cases hp : 1 ≤ p
  · have hstep : ∀ a, SmcPrime.spatialStep 2 R (p, T) a = (1, T) := by
      intro a
      simp only [SmcPrime.spatialStep, hp, true_or, ↓reduceIte]
    simp only [hstep, hφ0 1 _ le_rfl, lintegral_zero]
    exact (twoSampleStepOp_eq_zero R φ hφ0 hp _).symm
  · have hp1 : p < 1 := not_le.mp hp
    have hRh : 0 < R * rootHeight T := mul_pos hR hh
    let G : ℝ → ℝ≥0∞ := fun t => twoSampleHeightOp (fun a => φ (p + t, a)) (rootHeight T)
    have hG : Measurable G := by
      have h0 := (measurable_twoSampleHeightOp φ hφ).comp
        (show Measurable fun t : ℝ => (p + t, rootHeight T) from
          (measurable_const.add measurable_id).prodMk measurable_const)
      exact h0
    have hpt : ∀ e ∈ Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-e)) *
        (if p + e / (R * rootHeight T) < 1 then
          ENNReal.ofReal (twoSampleSelfMass (rootHeight T)) *
              φ (p + e / (R * rootHeight T), rootHeight T) +
            ∫⁻ a in Ioi 0, ENNReal.ofReal (twoSampleJumpDensity (rootHeight T) a) *
              φ (p + e / (R * rootHeight T), a)
        else φ (1, rootHeight T)) =
        ENNReal.ofReal (Real.exp (-e)) * G (e / (R * rootHeight T)) := by
      intro e he
      congr 1
      by_cases h1 : p + e / (R * rootHeight T) < 1
      · simp only [h1, ↓reduceIte, G, twoSampleHeightOp]
      · have hz : (fun a => φ (p + e / (R * rootHeight T), a)) = fun _ => 0 :=
          funext fun a => hφ0 _ a (not_lt.mp h1)
        simp only [h1, ↓reduceIte, G, hz, twoSampleHeightOp_zero, hφ0 1 _ le_rfl]
    rw [hT.spatialStep_lintegral hR hh hp1 φ hφ,
      setLIntegral_congr_fun measurableSet_Ioi hpt,
      lintegral_Ioi_exp_neg_comp_div hRh G hG]
    rfl

noncomputable def stateMean (R : ℝ) (k : ℕ) (φ : ℝ × ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ ω, φ ((ω k).1, rootHeight (ω k).2) ∂(spatialProcess 2 R).law (spatialInitialLaw 2)

theorem stateMean_zero (R : ℝ) (φ : ℝ × ℝ → ℝ≥0∞) (hφ : Measurable φ) :
    stateMean R 0 φ = ∫⁻ h in Ioi 0, ENNReal.ofReal (Real.exp (-h)) * φ (0, h) := by
  have hF : Measurable fun z : SpatialState 2 => φ (z.1, rootHeight z.2) :=
    hφ.comp (measurable_fst.prodMk ((rootHeight_measurable 2).comp measurable_snd))
  unfold stateMean
  rw [spatialProcess_law_lintegral_eval_zero 2 R _ _ hF]
  exact spatialInitialLaw_two_lintegral φ hφ

theorem stateMean_succ {R : ℝ} (hR : 0 < R) (k : ℕ) (φ : ℝ × ℝ → ℝ≥0∞)
    (hφ : Measurable φ) (hφ0 : ∀ q a : ℝ, 1 ≤ q → φ (q, a) = 0) :
    stateMean R (k + 1) φ = stateMean R k (twoSampleStepOp R φ) := by
  have hΦ : Measurable fun w : SpatialState 2 × SpatialState 2 =>
      φ (w.2.1, rootHeight w.2.2) :=
    hφ.comp ((measurable_fst.comp measurable_snd).prodMk
      ((rootHeight_measurable 2).comp (measurable_snd.comp measurable_snd)))
  unfold stateMean
  rw [spatialProcess_law_lintegral_step 2 R _ k _ hΦ]
  refine lintegral_congr_ae ?_
  filter_upwards [spatialProcess_two_law_twoSampleArray_ae R] with ω hω
  exact (hω k).1.spatialStep_lintegral_stepOp hR (hω k).2 (ω k).1 φ hφ hφ0

theorem sum_stateMean_le {R : ℝ} (hR : 0 < R) (n : ℕ) :
    ∀ φ : ℝ × ℝ → ℝ≥0∞, Measurable φ → (∀ q a : ℝ, 1 ≤ q → φ (q, a) = 0) →
      ∑ k ∈ Finset.range (n + 1), stateMean R k φ ≤
        (∫⁻ h in Ioi 0, ENNReal.ofReal (Real.exp (-h)) * φ (0, h)) +
          ∫⁻ q in Ioi 0, ∫⁻ h in Ioi 0,
            ENNReal.ofReal (R * (h * Real.exp (-h))) * φ (q, h) := by
  induction n with
  | zero =>
    intro φ hφ _
    rw [Finset.range_one, Finset.sum_singleton, stateMean_zero R φ hφ]
    exact le_self_add
  | succ n ih =>
    intro φ hφ hφ0
    have hS := measurable_twoSampleStepOp R φ hφ
    have hS0 : ∀ q a : ℝ, 1 ≤ q → twoSampleStepOp R φ (q, a) = 0 := fun q a hq =>
      twoSampleStepOp_eq_zero R φ hφ0 hq a
    rw [Finset.sum_range_succ' _ (n + 1)]
    simp only [stateMean_succ hR _ φ hφ hφ0]
    rw [stateMean_zero R φ hφ, add_comm]
    exact add_le_add le_rfl
      ((ih _ hS hS0).trans (twoSampleOccupation_step hR φ hφ).le)

noncomputable def probeWeight (R x : ℝ) (g : ℝ → ℝ≥0∞) (z : ℝ × ℝ) : ℝ≥0∞ :=
  if z.1 ≤ x then ENNReal.ofReal (Real.exp (-(R * z.2 * (x - z.1)))) * g z.2 else 0

theorem measurable_probeWeight (R x : ℝ) (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    Measurable (probeWeight R x g) := by
  unfold probeWeight
  refine Measurable.ite (measurableSet_le measurable_fst measurable_const) ?_
    measurable_const
  exact Measurable.mul (by fun_prop) (hg.comp measurable_snd)

noncomputable def probeTerm (x : ℝ) (g : ℝ → ℝ≥0∞) (k : ℕ) (ω : ℕ → SpatialState 2) :
    ℝ≥0∞ :=
  if (ω k).1 ≤ x ∧ x < (ω (k + 1)).1 then g (rootHeight (ω k).2) else 0

theorem measurable_probeTerm (x : ℝ) (g : ℝ → ℝ≥0∞) (hg : Measurable g) (k : ℕ) :
    Measurable (probeTerm x g k) := by
  unfold probeTerm
  have h1 : Measurable fun ω : ℕ → SpatialState 2 => (ω k).1 :=
    measurable_fst.comp (measurable_pi_apply k)
  have h2 : Measurable fun ω : ℕ → SpatialState 2 => (ω (k + 1)).1 :=
    measurable_fst.comp (measurable_pi_apply (k + 1))
  refine Measurable.ite ?_ ?_ measurable_const
  · exact (measurableSet_le h1 measurable_const).inter
      (measurableSet_lt measurable_const h2)
  · exact hg.comp ((rootHeight_measurable 2).comp
      (measurable_snd.comp (measurable_pi_apply k)))

theorem lintegral_probeTerm {R : ℝ} (hR : 0 < R) {x : ℝ} (hx1 : x < 1) (g : ℝ → ℝ≥0∞)
    (hg : Measurable g) (k : ℕ) :
    ∫⁻ ω, probeTerm x g k ω ∂(spatialProcess 2 R).law (spatialInitialLaw 2) =
      stateMean R k (probeWeight R x g) := by
  let Φ : SpatialState 2 × SpatialState 2 → ℝ≥0∞ := fun w =>
    if w.1.1 ≤ x ∧ x < w.2.1 then g (rootHeight w.1.2) else 0
  have hΦ : Measurable Φ := by
    refine Measurable.ite ?_ ?_ measurable_const
    · exact (measurableSet_le (measurable_fst.comp measurable_fst) measurable_const).inter
        (measurableSet_lt measurable_const (measurable_fst.comp measurable_snd))
    · exact hg.comp ((rootHeight_measurable 2).comp (measurable_snd.comp measurable_fst))
  have h1 := spatialProcess_law_lintegral_step 2 R (spatialInitialLaw 2) k Φ hΦ
  unfold stateMean
  refine h1.trans (lintegral_congr_ae ?_)
  filter_upwards [spatialProcess_two_law_twoSampleArray_ae R] with ω hω
  obtain ⟨hT, hh⟩ := hω k
  generalize ω k = z at hT hh
  obtain ⟨p, T⟩ := z
  dsimp only at hT hh ⊢
  have hstepm : Measurable fun a : ProposalNoise =>
      SmcPrime.spatialStep 2 R (p, T) a :=
    (spatialStep_measurable 2 R).comp (measurable_const.prodMk measurable_id)
  have hind : Measurable fun a : ProposalNoise =>
      if x < (SmcPrime.spatialStep 2 R (p, T) a).1 then (1 : ℝ≥0∞) else 0 :=
    Measurable.ite (measurableSet_lt measurable_const (measurable_fst.comp hstepm))
      measurable_const measurable_const
  by_cases hpx : p ≤ x
  · have hpt : ∀ a : ProposalNoise,
        Φ ((p, T), SmcPrime.spatialStep 2 R (p, T) a) =
          (if x < (SmcPrime.spatialStep 2 R (p, T) a).1 then (1 : ℝ≥0∞) else 0) *
            g (rootHeight T) := by
      intro a
      by_cases hxa : x < (SmcPrime.spatialStep 2 R (p, T) a).1
      · simp only [Φ, hpx, hxa, and_self, ↓reduceIte, one_mul]
      · simp only [Φ, hpx, hxa, and_false, ↓reduceIte, zero_mul]
    rw [lintegral_congr hpt, lintegral_mul_const _ hind,
      hT.spatialStep_position_gt_lintegral hR hh hpx hx1]
    simp only [probeWeight, hpx, ↓reduceIte]
  · have hpt : ∀ a : ProposalNoise,
        Φ ((p, T), SmcPrime.spatialStep 2 R (p, T) a) = 0 := by
      intro a
      simp only [Φ, hpx, false_and, ↓reduceIte]
    rw [lintegral_congr hpt, lintegral_zero]
    simp only [probeWeight, hpx, ↓reduceIte]

theorem occupation_probeWeight {R : ℝ} (hR : 0 < R) {x : ℝ} (hx0 : 0 ≤ x) (g : ℝ → ℝ≥0∞)
    (hg : Measurable g) :
    (∫⁻ h in Ioi 0, ENNReal.ofReal (Real.exp (-h)) * probeWeight R x g (0, h)) +
        ∫⁻ q in Ioi 0, ∫⁻ h in Ioi 0,
          ENNReal.ofReal (R * (h * Real.exp (-h))) * probeWeight R x g (q, h) =
      ∫⁻ h in Ioi 0, ENNReal.ofReal (Real.exp (-h)) * g h := by
  have hpw := measurable_probeWeight R x g hg
  have hw : Measurable fun h : ℝ => ENNReal.ofReal (R * (h * Real.exp (-h))) := by fun_prop
  have hwe : Measurable fun h : ℝ => ENNReal.ofReal (Real.exp (-h)) := by fun_prop
  have hswap : ∫⁻ q in Ioi 0, ∫⁻ h in Ioi 0,
        ENNReal.ofReal (R * (h * Real.exp (-h))) * probeWeight R x g (q, h) =
      ∫⁻ h in Ioi 0, ∫⁻ q in Ioi 0,
        ENNReal.ofReal (R * (h * Real.exp (-h))) * probeWeight R x g (q, h) := by
    refine lintegral_lintegral_swap (Measurable.aemeasurable ?_)
    exact (hw.comp measurable_snd).mul hpw
  have hinner : ∀ h ∈ Ioi (0 : ℝ), ∫⁻ q in Ioi 0,
        ENNReal.ofReal (R * (h * Real.exp (-h))) * probeWeight R x g (q, h) =
      ENNReal.ofReal (1 - Real.exp (-(R * h * x))) *
        (ENNReal.ofReal (Real.exp (-h)) * g h) := by
    intro h hh
    have hRh : 0 ≤ R * h := mul_nonneg hR.le (mem_Ioi.mp hh).le
    have hpt : ∀ q : ℝ,
        ENNReal.ofReal (R * (h * Real.exp (-h))) * probeWeight R x g (q, h) =
          (Iic x).indicator (fun q => ENNReal.ofReal (R * h * Real.exp (-(R * h * (x - q)))) *
            (ENNReal.ofReal (Real.exp (-h)) * g h)) q := by
      intro q
      by_cases hq : q ≤ x
      · rw [indicator_of_mem (show q ∈ Iic x from hq)]
        simp only [probeWeight, hq, ↓reduceIte]
        rw [show R * (h * Real.exp (-h)) = R * h * Real.exp (-h) by ring,
          ENNReal.ofReal_mul hRh, ENNReal.ofReal_mul hRh]
        ring
      · rw [indicator_of_notMem (show q ∉ Iic x from hq)]
        simp only [probeWeight, hq, ↓reduceIte, mul_zero]
    rw [lintegral_congr hpt, lintegral_indicator measurableSet_Iic,
      Measure.restrict_restrict measurableSet_Iic, inter_comm, Ioi_inter_Iic,
      lintegral_mul_const _ (by fun_prop), ← setLIntegral_congr Ioo_ae_eq_Ioc,
      lintegral_Ioo_rate_exp hRh hx0]
  have hfirst : Measurable fun h : ℝ =>
      ENNReal.ofReal (Real.exp (-h)) * probeWeight R x g (0, h) := by
    have h0 := hpw.comp (show Measurable fun h : ℝ => ((0 : ℝ), h) from
      measurable_const.prodMk measurable_id)
    exact hwe.mul h0
  rw [hswap, setLIntegral_congr_fun measurableSet_Ioi hinner]
  refine (lintegral_add_left hfirst _).symm.trans ?_
  refine setLIntegral_congr_fun measurableSet_Ioi fun h hh => ?_
  have he1 : Real.exp (-(R * h * x)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg
      (mul_nonneg hR.le (mem_Ioi.mp hh).le) hx0))
  have hsum : ENNReal.ofReal (Real.exp (-(R * h * x))) +
      ENNReal.ofReal (1 - Real.exp (-(R * h * x))) = 1 := by
    rw [← ENNReal.ofReal_add (Real.exp_nonneg _) (sub_nonneg.mpr he1), add_sub_cancel,
      ENNReal.ofReal_one]
  simp only [probeWeight, hx0, ↓reduceIte, sub_zero]
  calc ENNReal.ofReal (Real.exp (-h)) * (ENNReal.ofReal (Real.exp (-(R * h * x))) * g h) +
        ENNReal.ofReal (1 - Real.exp (-(R * h * x))) *
          (ENNReal.ofReal (Real.exp (-h)) * g h)
      = (ENNReal.ofReal (Real.exp (-(R * h * x))) +
          ENNReal.ofReal (1 - Real.exp (-(R * h * x)))) *
            (ENNReal.ofReal (Real.exp (-h)) * g h) := by ring
    _ = ENNReal.ofReal (Real.exp (-h)) * g h := by rw [hsum, one_mul]

theorem tsum_lintegral_probeTerm_le {R : ℝ} (hR : 0 < R) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∑' k, ∫⁻ ω, probeTerm x g k ω ∂(spatialProcess 2 R).law (spatialInitialLaw 2) ≤
      ∫⁻ h in Ioi 0, ENNReal.ofReal (Real.exp (-h)) * g h := by
  simp only [lintegral_probeTerm hR hx1 g hg]
  have hpw := measurable_probeWeight R x g hg
  have hpw0 : ∀ q a : ℝ, 1 ≤ q → probeWeight R x g (q, a) = 0 := by
    intro q a hq
    have hqx : ¬ q ≤ x := fun h => absurd (hq.trans h) (not_le.mpr hx1)
    simp only [probeWeight, hqx, ↓reduceIte]
  refine ENNReal.tsum_le_of_sum_range_le fun n => ?_
  rw [← occupation_probeWeight hR hx0 g hg]
  cases n with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, zero_le]
  | succ m => exact sum_stateMean_le hR m _ hpw hpw0

theorem spatialProcess_two_probe_segment_ae (R : ℝ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    ∀ᵐ ω ∂(spatialProcess 2 R).law (spatialInitialLaw 2),
      ∃ k, (ω k).1 ≤ x ∧ x < (ω (k + 1)).1 := by
  have hset : MeasurableSet {z : SpatialState 2 | z.1 = 0} :=
    measurableSet_eq_fun measurable_fst measurable_const
  have hinit : ∀ᵐ z ∂spatialInitialLaw 2, z.1 = 0 := by
    unfold spatialInitialLaw
    rw [ae_map_iff (show Measurable (fun T : Tree 2 => ((0 : ℝ), T)) from
      measurable_const.prodMk measurable_id).aemeasurable hset]
    exact Filter.Eventually.of_forall fun T => rfl
  have h0 : ∀ᵐ ω ∂(spatialProcess 2 R).law (spatialInitialLaw 2), (ω 0).1 = 0 := by
    have h1 : ∀ᵐ z ∂((spatialProcess 2 R).law (spatialInitialLaw 2)).map (fun ω => ω 0),
        z.1 = 0 := by
      rw [spatialProcess_law_map_eval_zero]
      exact hinit
    exact (ae_map_iff (measurable_pi_apply 0).aemeasurable hset).mp h1
  filter_upwards [h0, spatialProcess_nonexplosive 2 R] with ω hω0 hend
  obtain ⟨k, hk⟩ := hend
  classical
  have hex : ∃ m, x < (ω m).1 := ⟨k, by rw [hk]; exact hx1⟩
  have hm := Nat.find_spec hex
  cases hmz : Nat.find hex with
  | zero =>
    rw [hmz, hω0] at hm
    exact absurd hm (not_lt.mpr hx0)
  | succ j =>
    have hj : ¬ x < (ω j).1 := Nat.find_min hex (by omega)
    rw [hmz] at hm
    exact ⟨j, not_lt.mp hj, hm⟩

theorem spatialProcess_two_fixed_position_lintegral {R : ℝ} (hR : 0 < R) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x < 1) (g : ℝ → ℝ≥0∞) (hg : Measurable g) (hg1 : ∀ h, g h ≤ 1) :
    ∑' k, ∫⁻ ω, probeTerm x g k ω ∂(spatialProcess 2 R).law (spatialInitialLaw 2) =
      ∫⁻ h in Ioi 0, ENNReal.ofReal (Real.exp (-h)) * g h := by
  have hgc : Measurable fun h : ℝ => 1 - g h := measurable_const.sub hg
  have hle := tsum_lintegral_probeTerm_le hR hx0 hx1 g hg
  have hlec := tsum_lintegral_probeTerm_le hR hx0 hx1 (fun h => 1 - g h) hgc
  refine le_antisymm hle ?_
  have hone : (1 : ℝ≥0∞) ≤ ∑' k, ∫⁻ ω, probeTerm x (fun _ => 1) k ω
      ∂(spatialProcess 2 R).law (spatialInitialLaw 2) := by
    rw [← lintegral_tsum fun k => (measurable_probeTerm x _ measurable_const k).aemeasurable]
    calc (1 : ℝ≥0∞) = ∫⁻ _ω, 1 ∂(spatialProcess 2 R).law (spatialInitialLaw 2) := by
          rw [lintegral_one, measure_univ]
      _ ≤ ∫⁻ ω, ∑' k, probeTerm x (fun _ => 1) k ω
            ∂(spatialProcess 2 R).law (spatialInitialLaw 2) := by
          refine lintegral_mono_ae ?_
          filter_upwards [spatialProcess_two_probe_segment_ae R hx0 hx1] with ω hω
          obtain ⟨k, hk⟩ := hω
          have h1 : probeTerm x (fun _ => 1) k ω = 1 := by
            simp only [probeTerm, hk, and_self, ↓reduceIte]
          calc (1 : ℝ≥0∞) = probeTerm x (fun _ => 1) k ω := h1.symm
            _ ≤ ∑' k, probeTerm x (fun _ => 1) k ω :=
              ENNReal.le_tsum (f := fun k => probeTerm x (fun _ => 1) k ω) k
  have hsplit : ∑' k, ∫⁻ ω, probeTerm x (fun _ => 1) k ω
        ∂(spatialProcess 2 R).law (spatialInitialLaw 2) =
      (∑' k, ∫⁻ ω, probeTerm x g k ω ∂(spatialProcess 2 R).law (spatialInitialLaw 2)) +
        ∑' k, ∫⁻ ω, probeTerm x (fun h => 1 - g h) k ω
          ∂(spatialProcess 2 R).law (spatialInitialLaw 2) := by
    rw [← ENNReal.tsum_add]
    refine tsum_congr fun k => ?_
    rw [← lintegral_add_left (measurable_probeTerm x g hg k)]
    refine lintegral_congr fun ω => ?_
    by_cases hc : (ω k).1 ≤ x ∧ x < (ω (k + 1)).1
    · simp only [probeTerm, hc, and_self, ↓reduceIte]
      exact (add_tsub_cancel_of_le (hg1 _)).symm
    · simp only [probeTerm, hc, ↓reduceIte, add_zero]
  have hAB : (∫⁻ h in Ioi 0, ENNReal.ofReal (Real.exp (-h)) * g h) +
      ∫⁻ h in Ioi 0, ENNReal.ofReal (Real.exp (-h)) * (1 - g h) = 1 := by
    have hm : Measurable fun h : ℝ => ENNReal.ofReal (Real.exp (-h)) * g h :=
      Measurable.mul (by fun_prop) hg
    rw [← lintegral_add_left hm]
    have hpt : ∀ h : ℝ, ENNReal.ofReal (Real.exp (-h)) * g h +
        ENNReal.ofReal (Real.exp (-h)) * (1 - g h) = ENNReal.ofReal (Real.exp (-h)) := by
      intro h
      rw [← mul_add, add_tsub_cancel_of_le (hg1 h), mul_one]
    rw [lintegral_congr hpt, lintegral_Ioi_exp_neg 0, neg_zero, Real.exp_zero,
      ENNReal.ofReal_one]
  have hB : ∫⁻ h in Ioi 0, ENNReal.ofReal (Real.exp (-h)) * (1 - g h) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (le_add_self.trans_eq hAB)
  refine ENNReal.le_of_add_le_add_right hB ?_
  calc (∫⁻ h in Ioi 0, ENNReal.ofReal (Real.exp (-h)) * g h) +
        ∫⁻ h in Ioi 0, ENNReal.ofReal (Real.exp (-h)) * (1 - g h) = 1 := hAB
    _ ≤ _ := hone
    _ = _ := hsplit
    _ ≤ _ := add_le_add le_rfl hlec

theorem tsum_stateMean_probeWeight {R : ℝ} (hR : 0 < R) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1)
    (g : ℝ → ℝ≥0∞) (hg : Measurable g) (hg1 : ∀ h, g h ≤ 1) :
    ∑' k, stateMean R k (probeWeight R x g) =
      ∫⁻ h in Ioi 0, ENNReal.ofReal (Real.exp (-h)) * g h := by
  rw [← spatialProcess_two_fixed_position_lintegral hR hx0 hx1 g hg hg1]
  exact tsum_congr fun k => (lintegral_probeTerm hR hx1 g hg k).symm

end Rhone.Coalescent.SmcPrime
