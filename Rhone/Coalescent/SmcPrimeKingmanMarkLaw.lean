/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeKingmanOneStepMarkLaw
public import Rhone.Coalescent.SmcPrimeKingmanFiniteSupport

/-!
# Kingman merger marks and waiting times: uniform pair and exponential clock laws

Source: kingman1982, Thm 1, eq. (1.7), (2.2). -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open MeasureTheory ProbabilityTheory IntervalProcess SmcSupport
open scoped ENNReal

def kingmanMarks (N : ℕ) (h : KingmanHistory N) : Fin (N - 1) → (ℕ × ℕ) × ℝ :=
  fun j => kingmanMark (h ⟨j.val, by omega⟩) (h ⟨j.val + 1, by omega⟩)

def kingmanWaitingTimes (N : ℕ) (h : KingmanHistory N) : Fin (N - 1) → ℝ :=
  fun j => (kingmanMarks N h j).2

noncomputable def kingmanMarkLaw (N : ℕ) : Measure (Fin (N - 1) → (ℕ × ℕ) × ℝ) :=
  Measure.pi fun j : Fin (N - 1) => (uniformOn (kingmanPairSet (N - j.val))).prod
    (expMeasure (Rhone.Coalescent.coalRate (N - j.val) : ℝ))

theorem kingmanMark_comp_measurable {α : Type*} [MeasurableSpace α] {f g : α → AugmentedState}
    (hf : Measurable f) (hg : Measurable g) : Measurable fun x => kingmanMark (f x) (g x) :=
  kingmanMark_measurable.comp (hf.prodMk hg)

theorem kingmanMarks_measurable (N : ℕ) : Measurable (kingmanMarks N) :=
  measurable_pi_iff.mpr fun _ =>
    kingmanMark_comp_measurable (measurable_pi_apply _) (measurable_pi_apply _)

theorem uniformOn_kingmanPairSet_probability {m : ℕ} (hm : 2 ≤ m) :
    IsProbabilityMeasure (uniformOn (kingmanPairSet m)) :=
  isProbabilityMeasure_uniformOn
    (((Set.finite_Iio m).prod (Set.finite_Iio m)).subset
      fun _ hq => ⟨lt_trans hq.1 hq.2, hq.2⟩)
    ⟨(0, 1), Nat.zero_lt_one, hm⟩

theorem expMeasure_coalRate_probability {m : ℕ} (hm : 2 ≤ m) :
    IsProbabilityMeasure (expMeasure (Rhone.Coalescent.coalRate m : ℝ)) :=
  isProbabilityMeasure_expMeasure (by exact_mod_cast Rhone.Coalescent.coalRate_pos hm)

theorem eventProcess_kingmanMark_rectangles (N n : ℕ) (hn : n ≤ N - 1)
    (s : ℕ → Set ((ℕ × ℕ) × ℝ)) (hs : ∀ j, MeasurableSet (s j)) :
    ((eventProcess false 0).pathLaw (initialState N, (0, .inl ())))
      {ω | ∀ j < n, kingmanMark (ω j) (ω (j + 1)) ∈ s j} =
    ∏ j ∈ Finset.range n, ((uniformOn (kingmanPairSet (N - j))).prod
      (expMeasure (Rhone.Coalescent.coalRate (N - j) : ℝ))) (s j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    set μ := (eventProcess false 0).pathLaw (initialState N, (0, .inl ())) with hμ
    let A : Set EventPath := {ω | ∀ j < n, kingmanMark (ω j) (ω (j + 1)) ∈ s j}
    have hA : MeasurableSet A := by
      have : A = ⋂ j, ⋂ (_ : j < n), {ω : EventPath | kingmanMark (ω j) (ω (j + 1)) ∈ s j} := by
        ext ω
        simp [A]
      rw [this]
      exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
        kingmanMark_comp_measurable (measurable_pi_apply j) (measurable_pi_apply (j + 1)) (hs j)
    let F : EventPath → ARGPrefix n × AugmentedState :=
      fun ω => ((fun k : Finset.Iic n => ω k.val), ω (n + 1))
    have hF : Measurable F :=
      (measurable_pi_iff.mpr fun k => measurable_pi_apply k.val).prodMk (measurable_pi_apply _)
    let top : Finset.Iic n := ⟨n, Finset.mem_Iic.mpr le_rfl⟩
    let B : Set (ARGPrefix n × AugmentedState) := {p |
      (∀ j, ∀ hj : j < n, kingmanMark (p.1 ⟨j, Finset.mem_Iic.mpr (by omega)⟩)
        (p.1 ⟨j + 1, Finset.mem_Iic.mpr (by omega)⟩) ∈ s j) ∧
      kingmanMark (p.1 top) p.2 ∈ s n}
    have hB : MeasurableSet B := by
      have : B = (⋂ j, ⋂ (hj : j < n), {p : ARGPrefix n × AugmentedState |
          kingmanMark (p.1 ⟨j, Finset.mem_Iic.mpr (by omega)⟩)
            (p.1 ⟨j + 1, Finset.mem_Iic.mpr (by omega)⟩) ∈ s j}) ∩
          {p | kingmanMark (p.1 top) p.2 ∈ s n} := by
        ext p
        simp [B]
      rw [this]
      refine (MeasurableSet.iInter fun j => MeasurableSet.iInter fun hj => ?_).inter ?_
      · exact kingmanMark_comp_measurable ((measurable_pi_apply _).comp measurable_fst)
          ((measurable_pi_apply _).comp measurable_fst) (hs j)
      · exact kingmanMark_comp_measurable ((measurable_pi_apply _).comp measurable_fst)
          measurable_snd (hs n)
    have hset : {ω : EventPath | ∀ j < n + 1, kingmanMark (ω j) (ω (j + 1)) ∈ s j} = F ⁻¹' B := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, B, F, top]
      constructor
      · intro h
        exact ⟨fun j hj => h j (by omega), h n (by omega)⟩
      · rintro ⟨h1, h2⟩ j hj
        by_cases hjn : j < n
        · exact h1 j hjn
        · have : j = n := by omega
          subst this
          exact h2
    have hval : ∀ᵐ ω ∂μ, (eventProcess false 0).stepSeq n (F ω).1 (Prod.mk (F ω).1 ⁻¹' B) =
        A.indicator (fun _ => ((uniformOn (kingmanPairSet (N - n))).prod
          (expMeasure (Rhone.Coalescent.coalRate (N - n) : ℝ))) (s n)) ω := by
      filter_upwards [eventProcess_chronologicalAncestryPath N false 0,
        eventProcess_kingmanTransition (initialState N, (0, .inl ()))] with ω hc hk
      have hcount := kingman_path_count N ω (congrArg Prod.fst hc.1) hk n (by omega)
      have hker : (eventProcess false 0).stepSeq n (F ω).1 = eventKernel false 0 (ω n) := by
        rw [Rhone.MarkovChain.DiscreteProcess.stepSeq, Kernel.comap_apply]
        rfl
      rw [hker]
      by_cases hω : ω ∈ A
      · have hsec : Prod.mk (F ω).1 ⁻¹' B = kingmanMark (ω n) ⁻¹' s n := by
          ext y
          simp only [Set.mem_preimage, B, F, top, Set.mem_ofPred_eq]
          exact ⟨fun h => h.2, fun h => ⟨fun j hj => hω j hj, h⟩⟩
        have hmk : Measurable (kingmanMark (ω n)) :=
          kingmanMark_comp_measurable measurable_const measurable_id
        rw [hsec, Set.indicator_of_mem hω, ← Measure.map_apply hmk (hs n),
          eventKernel_kingmanMark_law (ω n) (by omega), hcount]
      · have hsec : Prod.mk (F ω).1 ⁻¹' B = ∅ := by
          ext y
          simp only [Set.mem_preimage, B, F, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
            iff_false, not_and]
          intro h
          exact absurd (fun j hj => h j hj) hω
        rw [hsec, measure_empty, Set.indicator_of_notMem hω]
    have hmeas : Measurable fun h : ARGPrefix n =>
        (eventProcess false 0).stepSeq n h (Prod.mk h ⁻¹' B) :=
      Kernel.measurable_kernel_prodMk_left hB
    rw [hset, ← Measure.map_apply hF hB]
    change (μ.map F) B = _
    have hnext : μ.map F = (argPrefixLaw 0 (initialState N, (0, .inl ())) n).compProd
        ((eventProcess false 0).stepSeq n) := argPrefixLaw_next 0 _ n
    rw [hnext, Measure.compProd_apply hB, argPrefixLaw,
      lintegral_map hmeas (measurable_pi_iff.mpr fun k => measurable_pi_apply k.val)]
    change ∫⁻ ω, (eventProcess false 0).stepSeq n (F ω).1 (Prod.mk (F ω).1 ⁻¹' B) ∂μ = _
    rw [lintegral_congr_ae hval, lintegral_indicator_const hA, Finset.prod_range_succ, mul_comm]
    congr 1
    exact ih (by omega)

theorem kingmanStepLaw_probability {m : ℕ} (hm : 2 ≤ m) :
    IsProbabilityMeasure ((uniformOn (kingmanPairSet m)).prod
      (expMeasure (Rhone.Coalescent.coalRate m : ℝ))) := by
  have := uniformOn_kingmanPairSet_probability hm
  have := expMeasure_coalRate_probability hm
  infer_instance

/-- Source: kingman1982, Thm 1, eq. (1.7), (2.2). -/
theorem kingmanHistoryLaw_marks (N : ℕ) :
    (kingmanHistoryLaw N).map (kingmanMarks N) = kingmanMarkLaw N := by
  have : ∀ j : Fin (N - 1), IsProbabilityMeasure
      ((uniformOn (kingmanPairSet (N - j.val))).prod
        (expMeasure (Rhone.Coalescent.coalRate (N - j.val) : ℝ))) :=
    fun j => kingmanStepLaw_probability (by omega)
  unfold kingmanMarkLaw
  symm
  apply Measure.pi_eq
  intro s hs
  let s' : ℕ → Set ((ℕ × ℕ) × ℝ) := fun j => if hj : j < N - 1 then s ⟨j, hj⟩ else Set.univ
  have hs' : ∀ j, MeasurableSet (s' j) := by
    intro j
    dsimp only [s']
    split_ifs
    exacts [hs _, MeasurableSet.univ]
  have hpi := MeasurableSet.univ_pi hs
  rw [Measure.map_apply (kingmanMarks_measurable N) hpi, kingmanHistoryLaw,
    Measure.map_apply (kingmanHistoryMap_measurable N) ((kingmanMarks_measurable N) hpi)]
  have hset : (fun ω : EventPath => fun k : Fin N => ω k.val) ⁻¹'
      (kingmanMarks N ⁻¹' Set.pi Set.univ s) =
      {ω | ∀ j < N - 1, kingmanMark (ω j) (ω (j + 1)) ∈ s' j} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_ofPred_eq,
      kingmanMarks]
    constructor
    · intro h j hj
      simpa only [s', dite_eq_left hj] using h ⟨j, hj⟩
    · intro h j
      simpa only [s', dite_eq_left j.isLt] using h j.val j.isLt
  rw [hset, eventProcess_kingmanMark_rectangles N (N - 1) le_rfl s' hs',
    ← Fin.prod_univ_eq_prod_range (fun j => ((uniformOn (kingmanPairSet (N - j))).prod
      (expMeasure (Rhone.Coalescent.coalRate (N - j) : ℝ))) (s' j))]
  apply Finset.prod_congr rfl
  intro j _
  simp only [s', dite_eq_left j.isLt]

/-- Source: kingman1982, eq. (1.7), (1.12)–(1.13). -/
theorem kingmanHistoryLaw_waitingTimes (N : ℕ) :
    (kingmanHistoryLaw N).map (kingmanWaitingTimes N) =
      Measure.pi fun j : Fin (N - 1) =>
        expMeasure (Rhone.Coalescent.coalRate (N - j.val) : ℝ) := by
  have hU : ∀ j : Fin (N - 1), IsProbabilityMeasure (uniformOn (kingmanPairSet (N - j.val))) :=
    fun j => uniformOn_kingmanPairSet_probability (by omega)
  have hE : ∀ j : Fin (N - 1), IsProbabilityMeasure
      (expMeasure (Rhone.Coalescent.coalRate (N - j.val) : ℝ)) :=
    fun j => expMeasure_coalRate_probability (by omega)
  have hsnd : ∀ j : Fin (N - 1), ((uniformOn (kingmanPairSet (N - j.val))).prod
      (expMeasure (Rhone.Coalescent.coalRate (N - j.val) : ℝ))).map Prod.snd =
      expMeasure (Rhone.Coalescent.coalRate (N - j.val) : ℝ) := fun j => by
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  have : ∀ j : Fin (N - 1), SigmaFinite (((uniformOn (kingmanPairSet (N - j.val))).prod
      (expMeasure (Rhone.Coalescent.coalRate (N - j.val) : ℝ))).map Prod.snd) := fun j => by
    rw [hsnd]
    infer_instance
  have h : kingmanWaitingTimes N =
      (fun (f : Fin (N - 1) → (ℕ × ℕ) × ℝ) j => (f j).2) ∘ kingmanMarks N := rfl
  rw [h, ← Measure.map_map (by fun_prop) (kingmanMarks_measurable N), kingmanHistoryLaw_marks,
    kingmanMarkLaw, Measure.pi_map_pi (fun _ => measurable_snd.aemeasurable)]
  simp only [hsnd]

/-- Source: kingman1982, Thm 1, eq. (2.2). -/
theorem kingmanHistoryLaw_pair_uniform (N : ℕ) (j : Fin (N - 1)) :
    (kingmanHistoryLaw N).map (fun h => (kingmanMarks N h j).1) =
      uniformOn (kingmanPairSet (N - j.val)) := by
  have hU : ∀ j : Fin (N - 1), IsProbabilityMeasure (uniformOn (kingmanPairSet (N - j.val))) :=
    fun j => uniformOn_kingmanPairSet_probability (by omega)
  have hE : ∀ j : Fin (N - 1), IsProbabilityMeasure
      (expMeasure (Rhone.Coalescent.coalRate (N - j.val) : ℝ)) :=
    fun j => expMeasure_coalRate_probability (by omega)
  have h : (fun h => (kingmanMarks N h j).1) =
      (Prod.fst ∘ fun f : Fin (N - 1) → (ℕ × ℕ) × ℝ => f j) ∘ kingmanMarks N := rfl
  rw [h, ← Measure.map_map (by fun_prop) (kingmanMarks_measurable N), kingmanHistoryLaw_marks,
    kingmanMarkLaw, ← Measure.map_map measurable_fst (measurable_pi_apply j),
    (measurePreserving_eval _ j).map_eq, Measure.map_fst_prod, measure_univ, one_smul]

end Rhone.Coalescent.SmcPrime
