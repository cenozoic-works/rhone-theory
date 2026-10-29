/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.FullARGWeightedExit
public import Rhone.Coalescent.FullARGPairTimeKernel
public import Rhone.Coalescent.FullARGTwoSamplePath

/-!
# First and second moments of the two-sample pair coalescence time under the full ARG

Source: hudson1983, p. 188, eq. (10), p. 189; mcvean2002, eq. (9)–(12), pp. 988–989. -/
@[expose] public section

namespace Rhone.Coalescent.IntervalProcess
open SmcSupport MeasureTheory ProbabilityTheory MarkovChain
open scoped ENNReal

section Generic

variable {S : Type*}

open scoped Classical in
theorem exitValue_eq_of_exit {A : Set S} {g : S → ℝ≥0∞} {m K : ℕ} {ω : ℕ → S}
    (hK : ∀ k, k < K ↔ ω k ∈ A) :
    IntervalProcess.exitValue A g m ω = if ω m ∈ A then g (ω K) else 0 := by
  unfold IntervalProcess.exitValue
  by_cases hm : ω m ∈ A
  · have hmK : m < K := (hK m).mpr hm
    have hK1 : K - 1 + 1 = K := by omega
    rw [ite_eq_left hm, tsum_eq_single (K - 1)]
    · rw [ite_eq_left, hK1]
      refine ⟨by omega, (hK _).mp (by omega), ?_⟩
      rw [hK1]
      exact fun h => lt_irrefl K ((hK K).mpr h)
    · intro k hk
      rw [ite_eq_right]
      rintro ⟨h1, h2, h3⟩
      have h4 := (hK k).mpr h2
      have h5 : ¬k + 1 < K := fun h => h3 ((hK _).mp h)
      omega
  · have hKm : K ≤ m := not_lt.mp fun h => hm ((hK m).mp h)
    rw [ite_eq_right hm]
    refine ENNReal.tsum_eq_zero.mpr fun k => ?_
    rw [ite_eq_right]
    rintro ⟨h1, h2, -⟩
    have h4 := (hK k).mpr h2
    omega

end Generic

theorem ENNReal_two_mul_le_sq_add_one (b : ℝ≥0∞) : 2 * b ≤ b ^ 2 + 1 := by
  induction b using ENNReal.recTopCoe with
  | top => simp
  | coe r =>
    have h : 2 * r ≤ r ^ 2 + 1 := by
      apply NNReal.coe_le_coe.mp
      push_cast
      nlinarith [sq_nonneg ((r : ℝ) - 1)]
    exact_mod_cast h

def PairTimePath (ω : EventPath) : Prop :=
  ChronologicalAncestryPath 2 ω ∧
    (∀ (q : GenomicProbe) (k : ℕ), twoSampleTransition q (ω k, ω (k + 1))) ∧
    ∃ K, ∀ k, K ≤ k → (ω k).1.2.2.1 ≤ 1

theorem eventProcess_pairTimePath (R : ℝ) (hR : 0 ≤ R) :
    ∀ᵐ ω ∂(eventProcess false R).pathLaw (initialState 2, (0, .inl ())),
      PairTimePath ω := by
  have h2 : ∀ᵐ ω ∂(eventProcess false R).pathLaw (initialState 2, (0, .inl ())),
      ∀ (q : GenomicProbe) (k : ℕ), twoSampleTransition q (ω k, ω (k + 1)) :=
    ae_all_iff.mpr fun q => eventProcess_twoSampleTransition R _ q
  filter_upwards [eventProcess_chronologicalAncestryPath 2 false R, h2,
    eventProcess_liveCount_reaches_one 2 R hR] with ω a b c
  exact ⟨a, b, c⟩

theorem initial_mem_pairActive (q : GenomicProbe) :
    ((initialState 2, (0, .inl ())) : AugmentedState) ∈ pairActive (q.val : ℝ) :=
  ⟨carrierCount_initialState 2 _ (by exact_mod_cast q.property.1)
    (by exact_mod_cast q.property.2), le_refl (0 : ℝ)⟩

theorem PairTimePath.exists_exit {ω : EventPath} (h : PairTimePath ω) (q : GenomicProbe) :
    ∃ K, (∀ k, k < K ↔ ω k ∈ pairActive (q.val : ℝ)) ∧
      genealogyObservation 2 ω q 0 1 = ENNReal.ofReal (ω K).1.1 := by
  obtain ⟨K, hlt, hK, hobs⟩ :=
    genealogyObservation_eq_time_of_carrierCount h.1 q (h.2.1 q) h.2.2
  refine ⟨K, fun k => ⟨fun hk => ⟨hlt k hk, (h.1.valid k).1⟩, fun hk => ?_⟩, hobs⟩
  by_contra hkK
  have hanti : Antitone fun k => carrierCount (q.val : ℝ) (ω k).1 :=
    antitone_nat_of_succ_le fun k => (h.2.1 q k).2.1
  have h1 : carrierCount (q.val : ℝ) (ω k).1 ≤ carrierCount (q.val : ℝ) (ω K).1 :=
    hanti (not_lt.mp hkK)
  have h2 : carrierCount (q.val : ℝ) (ω k).1 = 2 := hk.1
  omega

theorem PairTimePath.time_lt_succ {ω : EventPath} (h : PairTimePath ω) (q : GenomicProbe)
    {k : ℕ} (hk : ω k ∈ pairActive (q.val : ℝ)) : (ω k).1.1 < (ω (k + 1)).1.1 := by
  refine (h.2.1 q k).1 ?_
  change 2 ≤ (ω k).1.2.2.1
  have h1 := materialCount_le (fun a => materialContains a (q.val : ℝ)) (ω k).1
  have h2 : carrierCount (q.val : ℝ) (ω k).1 = 2 := hk.1
  unfold carrierCount at h2
  omega

theorem measurable_pairTime (x : GenomicProbe) :
    Measurable fun G : Genealogy 2 => G x 0 1 :=
  (measurable_pi_apply (1 : Fin 2)).comp
    ((measurable_pi_apply (0 : Fin 2)).comp (measurable_pi_apply x))

theorem pathLaw_lintegral_mul_pairTime_of_step (R : ℝ) (hR : 0 ≤ R) (q : GenomicProbe)
    {g : AugmentedState → ℝ≥0∞} (hg : Measurable g)
    (hstep : ∀ z ∈ pairActive (q.val : ℝ), ∫⁻ w, g w ∂eventKernel false R z = g z)
    {φ : ℝ≥0∞ → ℝ≥0∞}
    (hout : ∀ z, z ∉ pairActive (q.val : ℝ) → g z = φ (ENNReal.ofReal z.1.1))
    {c : ℝ≥0∞} (hc : c ≠ ∞)
    (hdom : ∀ z ∈ pairActive (q.val : ℝ), ∀ z' ∈ pairActive (q.val : ℝ), ∀ s : ℝ,
      z.1.1 ≤ s → g z ≤ c * (φ (ENNReal.ofReal s) + g z'))
    (m : ℕ) {W : EventPath → ℝ≥0∞}
    (hW : Measurable[Filtration.piLE (X := fun _ : ℕ => AugmentedState) m] W)
    (hfin : ∫⁻ ω, W ω * (pairActive (q.val : ℝ)).indicator g (ω m)
      ∂(eventProcess false R).pathLaw (initialState 2, (0, .inl ())) ≠ ∞) :
    ∫⁻ ω, W ω * (pairActive (q.val : ℝ)).indicator
        (fun _ => φ (genealogyObservation 2 ω q 0 1)) (ω m)
        ∂(eventProcess false R).pathLaw (initialState 2, (0, .inl ())) =
      ∫⁻ ω, W ω * (pairActive (q.val : ℝ)).indicator g (ω m)
        ∂(eventProcess false R).pathLaw (initialState 2, (0, .inl ())) := by
  classical
  have hgood := eventProcess_pairTimePath R hR
  have hWa : Measurable W :=
    hW.mono ((Filtration.piLE (X := fun _ : ℕ => AugmentedState)).le m) le_rfl
  have hstep' : ∀ z ∈ pairActive (q.val : ℝ),
      ∫⁻ w, g w ∂(eventProcess false R).step z = g z := hstep
  have hpt : ∀ᵐ ω ∂(eventProcess false R).pathLaw (initialState 2, (0, .inl ())),
      W ω * (pairActive (q.val : ℝ)).indicator
          (fun _ => φ (genealogyObservation 2 ω q 0 1)) (ω m) =
        W ω * IntervalProcess.exitValue (pairActive (q.val : ℝ)) g m ω := by
    filter_upwards [hgood] with ω hω
    obtain ⟨K, hK, hT⟩ := hω.exists_exit q
    rw [exitValue_eq_of_exit hK, hout _ (fun h => lt_irrefl K ((hK K).mpr h)), ← hT]
    by_cases h : ω m ∈ pairActive (q.val : ℝ) <;> simp [h]
  have hmono : ∀ᵐ ω ∂(eventProcess false R).pathLaw (initialState 2, (0, .inl ())),
      ∀ k, ω (k + 1) ∈ pairActive (q.val : ℝ) → ω k ∈ pairActive (q.val : ℝ) := by
    filter_upwards [hgood] with ω hω k hk
    obtain ⟨K, hK, -⟩ := hω.exists_exit q
    have := (hK (k + 1)).mpr hk
    exact (hK k).mp (by omega)
  have hexit : ∀ᵐ ω ∂(eventProcess false R).pathLaw (initialState 2, (0, .inl ())),
      ∃ n, ω n ∉ pairActive (q.val : ℝ) := by
    filter_upwards [hgood] with ω hω
    obtain ⟨K, hK, -⟩ := hω.exists_exit q
    exact ⟨K, fun h => lt_irrefl K ((hK K).mpr h)⟩
  have hle := IntervalProcess.pathLaw_lintegral_mul_exitValue_le (eventProcess false R)
    (pairActive_measurable (q.val : ℝ)) hg hstep' (initialState 2, (0, .inl ())) m hW hmono
  have hI := lintegral_congr_ae hpt
  have hmeasR : Measurable fun ω : EventPath =>
      W ω * (pairActive (q.val : ℝ)).indicator g (ω m) :=
    hWa.mul ((hg.indicator (pairActive_measurable _)).comp (measurable_pi_apply m))
  rw [hI]
  symm
  refine IntervalProcess.pathLaw_lintegral_mul_exitValue (eventProcess false R)
    (pairActive_measurable (q.val : ℝ)) hg hstep' (initialState 2, (0, .inl ())) m hW hmono
    hexit (D := fun ω => c * (W ω * (pairActive (q.val : ℝ)).indicator
        (fun _ => φ (genealogyObservation 2 ω q 0 1)) (ω m) +
      W ω * (pairActive (q.val : ℝ)).indicator g (ω m))) ?_ ?_
  · rw [lintegral_const_mul' _ _ hc, lintegral_add_right _ hmeasR, hI]
    exact ENNReal.mul_ne_top hc
      (ENNReal.add_ne_top.mpr ⟨ne_top_of_le_ne_top hfin hle, hfin⟩)
  · filter_upwards [hgood] with ω hω n hmn hn
    obtain ⟨K, hK, hT⟩ := hω.exists_exit q
    have hnK : n < K := (hK n).mpr hn
    have hmA : ω m ∈ pairActive (q.val : ℝ) := (hK m).mp (by omega)
    have hd := hdom _ hn _ hmA _ (hω.1.time_monotone hnK.le)
    rw [Set.indicator_of_mem hmA, Set.indicator_of_mem hmA, ← mul_add, hT]
    calc W ω * g (ω n)
        ≤ W ω * (c * (φ (ENNReal.ofReal (ω K).1.1) + g (ω m))) := by gcongr
      _ = c * (W ω * (φ (ENNReal.ofReal (ω K).1.1) + g (ω m))) := by ring

theorem pathLaw_lintegral_mul_pairTime (R : ℝ) (hR : 0 ≤ R) (q : GenomicProbe)
    (m : ℕ) {W : EventPath → ℝ≥0∞}
    (hW : Measurable[Filtration.piLE (X := fun _ : ℕ => AugmentedState) m] W)
    (hfin : ∫⁻ ω, W ω * (pairActive (q.val : ℝ)).indicator (pairTimeFirst (q.val : ℝ)) (ω m)
      ∂(eventProcess false R).pathLaw (initialState 2, (0, .inl ())) ≠ ∞) :
    ∫⁻ ω, W ω * (pairActive (q.val : ℝ)).indicator
        (fun _ => genealogyObservation 2 ω q 0 1) (ω m)
        ∂(eventProcess false R).pathLaw (initialState 2, (0, .inl ())) =
      ∫⁻ ω, W ω * (pairActive (q.val : ℝ)).indicator (pairTimeFirst (q.val : ℝ)) (ω m)
        ∂(eventProcess false R).pathLaw (initialState 2, (0, .inl ())) := by
  refine pathLaw_lintegral_mul_pairTime_of_step R hR q (pairTimeFirst_measurable _)
    (eventKernel_pairTimeFirst R _) (φ := fun t => t)
    (fun z hz => pairTimeFirst_of_notMem hz) (c := 1) ENNReal.one_ne_top ?_ m hW hfin
  intro z hz z' hz' s hs
  rw [pairTimeFirst_of_mem hz, pairTimeFirst_of_mem hz', one_mul]
  exact add_le_add (ENNReal.ofReal_le_ofReal hs) le_add_self

theorem pathLaw_lintegral_mul_pairTime_sq (R : ℝ) (hR : 0 ≤ R) (q : GenomicProbe)
    (m : ℕ) {W : EventPath → ℝ≥0∞}
    (hW : Measurable[Filtration.piLE (X := fun _ : ℕ => AugmentedState) m] W)
    (hfin : ∫⁻ ω, W ω * (pairActive (q.val : ℝ)).indicator (pairTimeSecond (q.val : ℝ)) (ω m)
      ∂(eventProcess false R).pathLaw (initialState 2, (0, .inl ())) ≠ ∞) :
    ∫⁻ ω, W ω * (pairActive (q.val : ℝ)).indicator
        (fun _ => genealogyObservation 2 ω q 0 1 ^ 2) (ω m)
        ∂(eventProcess false R).pathLaw (initialState 2, (0, .inl ())) =
      ∫⁻ ω, W ω * (pairActive (q.val : ℝ)).indicator (pairTimeSecond (q.val : ℝ)) (ω m)
        ∂(eventProcess false R).pathLaw (initialState 2, (0, .inl ())) := by
  refine pathLaw_lintegral_mul_pairTime_of_step R hR q (pairTimeSecond_measurable _)
    (eventKernel_pairTimeSecond R _) (φ := fun t => t ^ 2)
    (fun z hz => pairTimeSecond_of_notMem hz) (c := 2) (by simp) ?_ m hW hfin
  intro z hz z' hz' s hs
  rw [pairTimeSecond_of_mem hz, pairTimeSecond_of_mem hz']
  have hab : ENNReal.ofReal z.1.1 ≤ ENNReal.ofReal s := ENNReal.ofReal_le_ofReal hs
  have h2 : (2 : ℝ≥0∞) ≤ ENNReal.ofReal z'.1.1 ^ 2 + (2 * ENNReal.ofReal z'.1.1 + 2) :=
    le_add_self.trans le_add_self
  have h3 : (3 : ℝ≥0∞) ≤ 2 * 2 := by norm_num
  calc ENNReal.ofReal z.1.1 ^ 2 + (2 * ENNReal.ofReal z.1.1 + 2)
      ≤ ENNReal.ofReal s ^ 2 + (2 * ENNReal.ofReal s + 2) := by gcongr
    _ ≤ ENNReal.ofReal s ^ 2 + (ENNReal.ofReal s ^ 2 + 1 + 2) := by
        gcongr
        exact ENNReal_two_mul_le_sq_add_one _
    _ = 2 * ENNReal.ofReal s ^ 2 + 3 := by ring
    _ ≤ 2 * ENNReal.ofReal s ^ 2 + 2 * 2 := by gcongr
    _ = 2 * (ENNReal.ofReal s ^ 2 + 2) := by ring
    _ ≤ 2 * (ENNReal.ofReal s ^ 2 +
          (ENNReal.ofReal z'.1.1 ^ 2 + (2 * ENNReal.ofReal z'.1.1 + 2))) := by gcongr

theorem pathLaw_lintegral_indicator_initial (R : ℝ) (q : GenomicProbe)
    (f : AugmentedState → ℝ≥0∞) :
    ∫⁻ ω, (fun _ : EventPath => (1 : ℝ≥0∞)) ω *
        (pairActive (q.val : ℝ)).indicator f (ω 0)
        ∂(eventProcess false R).pathLaw (initialState 2, (0, .inl ())) =
      f (initialState 2, (0, .inl ())) := by
  have h0 : ∀ᵐ ω ∂(eventProcess false R).pathLaw (initialState 2, (0, .inl ())),
      (fun _ : EventPath => (1 : ℝ≥0∞)) ω * (pairActive (q.val : ℝ)).indicator f (ω 0) =
        f (initialState 2, (0, .inl ())) := by
    filter_upwards [eventProcess_chronologicalAncestryPath 2 false R] with ω h
    rw [h.1, Set.indicator_of_mem (initial_mem_pairActive q), one_mul]
  rw [lintegral_congr_ae h0, lintegral_const, measure_univ, mul_one]

theorem pathLaw_lintegral_pairTime (R : ℝ) (hR : 0 ≤ R) (q : GenomicProbe) :
    ∫⁻ ω, genealogyObservation 2 ω q 0 1
        ∂(eventProcess false R).pathLaw (initialState 2, (0, .inl ())) = 1 := by
  have hval : pairTimeFirst (q.val : ℝ) (initialState 2, (0, .inl ())) = 1 := by
    rw [pairTimeFirst_of_mem (initial_mem_pairActive q)]
    simp [initialState]
  have hmain := pathLaw_lintegral_mul_pairTime R hR q 0
    (W := fun _ => 1) measurable_const
    (by rw [pathLaw_lintegral_indicator_initial, hval]; exact ENNReal.one_ne_top)
  rw [pathLaw_lintegral_indicator_initial, hval] at hmain
  rw [← hmain]
  refine lintegral_congr_ae ?_
  filter_upwards [eventProcess_chronologicalAncestryPath 2 false R] with ω h
  rw [h.1, Set.indicator_of_mem (initial_mem_pairActive q), one_mul]

theorem pathLaw_lintegral_pairTime_sq (R : ℝ) (hR : 0 ≤ R) (q : GenomicProbe) :
    ∫⁻ ω, genealogyObservation 2 ω q 0 1 ^ 2
        ∂(eventProcess false R).pathLaw (initialState 2, (0, .inl ())) = 2 := by
  have hval : pairTimeSecond (q.val : ℝ) (initialState 2, (0, .inl ())) = 2 := by
    rw [pairTimeSecond_of_mem (initial_mem_pairActive q)]
    simp [initialState]
  have hmain := pathLaw_lintegral_mul_pairTime_sq R hR q 0
    (W := fun _ => 1) measurable_const
    (by rw [pathLaw_lintegral_indicator_initial, hval]; simp)
  rw [pathLaw_lintegral_indicator_initial, hval] at hmain
  rw [← hmain]
  refine lintegral_congr_ae ?_
  filter_upwards [eventProcess_chronologicalAncestryPath 2 false R] with ω h
  rw [h.1, Set.indicator_of_mem (initial_mem_pairActive q), one_mul]

/-- Source: hudson1983, p. 188, eq. (10), p. 189; mcvean2002, eq. (9)–(12), pp. 988–989. -/
theorem fullARG_two_sample_pairTime_lintegral (R : ℝ) (hR : 0 ≤ R) (x : GenomicProbe) :
    ∫⁻ G, G x 0 1 ∂fullARGGenealogyLaw 2 R = 1 := by
  unfold fullARGGenealogyLaw
  rw [lintegral_map (measurable_pairTime x) (genealogyObservation_measurable 2)]
  exact pathLaw_lintegral_pairTime R hR x

/-- Source: hudson1983, p. 188, eq. (10), p. 189; mcvean2002, eq. (9)–(12), pp. 988–989. -/
theorem fullARG_two_sample_pairTime_sq_lintegral (R : ℝ) (hR : 0 ≤ R) (x : GenomicProbe) :
    ∫⁻ G, G x 0 1 ^ 2 ∂fullARGGenealogyLaw 2 R = 2 := by
  unfold fullARGGenealogyLaw
  rw [lintegral_map ((measurable_pairTime x).pow_const 2) (genealogyObservation_measurable 2)]
  exact pathLaw_lintegral_pairTime_sq R hR x

end Rhone.Coalescent.IntervalProcess
