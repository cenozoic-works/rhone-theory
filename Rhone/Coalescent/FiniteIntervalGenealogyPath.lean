/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.FiniteIntervalGenealogyAncestry
public import Rhone.Coalescent.FiniteIntervalGenealogyCoverage
public import Rhone.Coalescent.SmcSupport.SamplerValidity
public import Rhone.Coalescent.SmcSupport.Selector

/-! # Sampler ancestry and chronological event times -/
@[expose] public section
namespace Rhone.Coalescent.IntervalProcess
open SmcSupport

theorem sampleStep_ancestorCarried (mode : Mode) (R : ℝ) (s : State)
    (hs : Valid s) (q : GenomicProbe) (a : ℕ)
    (ha : ancestorCarried s (q.val : ℝ) a) (u : Noise)
    (hu0 : 0 ≤ u 0) (hu1 : u 0 < 1) :
    ancestorCarried (sampleStep mode R s u).1 (q.val : ℝ)
      (ancestorStep s (sampleStep mode R s u).2.2 q a) := by
  classical
  unfold sampleStep
  split_ifs with hstop
  · simpa [ancestorStep] using ha
  · have ht : 0 < totalRate mode R s :=
      lt_of_le_of_ne (by positivity) (Ne.symm (fun h => hstop (Or.inr h)))
    obtain ⟨b, hb, hp⟩ := selectedAction_exists_positive mode R s u hu0 hu1 ht
    rw [hb]
    cases b with
    | inl ij =>
      exact coalSuccessor_ancestorCarried s hs q a ha ij.1 ij.2
        (positive_pair_order mode R s ij hp)
    | inr i => exact splitSuccessor_ancestorCarried s hs q a ha i _

theorem sampleStep_time_le (mode : Mode) (R : ℝ) (s : State) (u : Noise)
    (hu0 : 0 ≤ u 1) (hu1 : u 1 ≤ 1) :
    s.1 ≤ (sampleStep mode R s u).1.1 := by
  have hd : Real.log (u 1) / (totalRate mode R s : ℝ) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (Real.log_nonpos hu0 hu1)
      (totalRate mode R s).property
  have ht : s.1 ≤ s.1 - Real.log (u 1) / (totalRate mode R s : ℝ) := by linarith
  classical
  unfold sampleStep
  split_ifs
  · exact le_rfl
  · cases selectedAction mode R s u with
    | none => exact le_rfl
    | some a => cases a <;> exact ht

theorem sampleStep_record_time (mode : Mode) (R : ℝ) (s : State) (u : Noise) :
    (sampleStep mode R s u).2.1 = (sampleStep mode R s u).1.1 := by
  classical
  unfold sampleStep
  split_ifs
  · rfl
  · cases selectedAction mode R s u with
    | none => rfl
    | some a => cases a <;> rfl

def SamplerPath (N : ℕ) (mode : Mode) (R : ℝ) (ω : EventPath) : Prop :=
  ω 0 = (initialState N, (0, .inl ())) ∧
    ∀ k, ∃ u : Noise, 0 ≤ u 0 ∧ u 0 < 1 ∧ 0 ≤ u 1 ∧ u 1 ≤ 1 ∧
      0 < u 2 ∧ u 2 < 1 ∧ ω (k + 1) = sampleStep mode R (ω k).1 u

theorem SamplerPath.valid {N : ℕ} {mode : Mode} {R : ℝ} {ω : EventPath}
    (h : SamplerPath N mode R ω) (k : ℕ) : Valid (ω k).1 := by
  induction k with
  | zero => rw [h.1]; exact initialState_valid N
  | succ k ih =>
    obtain ⟨u, _, _, ht0, ht1, hc0, hc1, hu⟩ := h.2 k
    rw [hu]
    exact sampleStep_valid mode R _ ih u ht0 ht1 hc0 hc1

theorem SamplerPath.ancestorCarried {N : ℕ} {mode : Mode} {R : ℝ} {ω : EventPath}
    (h : SamplerPath N mode R ω) (q : GenomicProbe) (i : Fin N) (k : ℕ) :
    ancestorCarried (ω k).1 (q.val : ℝ) (ancestorLabel N ω q i k) := by
  induction k with
  | zero => simp only [ancestorLabel, h.1]; exact initial_ancestorCarried N q i
  | succ k ih =>
    obtain ⟨u, hs0, hs1, _, _, _, _, hu⟩ := h.2 k
    simp only [ancestorLabel, hu]
    exact sampleStep_ancestorCarried mode R _ (h.valid k) q _ ih u hs0 hs1

theorem SamplerPath.time_monotone {N : ℕ} {mode : Mode} {R : ℝ} {ω : EventPath}
    (h : SamplerPath N mode R ω) : Monotone (fun k => (ω k).1.1) := by
  apply monotone_nat_of_le_succ
  intro k
  obtain ⟨u, _, _, ht0, ht1, _, _, hu⟩ := h.2 k
  rw [hu]
  exact sampleStep_time_le mode R _ u ht0 ht1

theorem SamplerPath.completed_of_one {N : ℕ} {mode : Mode} {R : ℝ} {ω : EventPath}
    (h : SamplerPath N mode R ω) (K : ℕ) (hk : (ω K).1.2.2.1 ≤ 1) :
    ∀ q i j, ancestorLabel N ω q i K = ancestorLabel N ω q j K := by
  intro q i j
  obtain ⟨a, ha, _⟩ := h.ancestorCarried q i K
  obtain ⟨b, hb, _⟩ := h.ancestorCarried q j K
  have hab : a = b := Fin.ext (by omega)
  exact ha.symm.trans (hab ▸ hb)

theorem SamplerPath.observation_eq_prefix {N : ℕ} {mode : Mode} {R : ℝ} {ω : EventPath}
    (h : SamplerPath N mode R ω) (K : ℕ) (hk : (ω K).1.2.2.1 ≤ 1) :
    genealogyObservation N ω = prefixGenealogyObservation N K ω :=
  genealogyObservation_eq_prefix N K ω h.time_monotone (h.completed_of_one K hk)

def CompletedCoverage (s : State) : Prop :=
  ∀ (q : GenomicProbe) (i j : Fin s.2.2.1),
    materialContains (s.2.2.2 i).2 (q.val : ℝ) →
    materialContains (s.2.2.2 j).2 (q.val : ℝ) → i = j

theorem SamplerPath.completed_of_coverage {N : ℕ} {mode : Mode} {R : ℝ}
    {ω : EventPath} (h : SamplerPath N mode R ω) (K : ℕ)
    (hk : CompletedCoverage (ω K).1) :
    ∀ q i j, ancestorLabel N ω q i K = ancestorLabel N ω q j K := by
  intro q i j
  obtain ⟨a, ha, haq⟩ := h.ancestorCarried q i K
  obtain ⟨b, hb, hbq⟩ := h.ancestorCarried q j K
  exact ha.symm.trans (hk q a b haq hbq ▸ hb)

theorem SamplerPath.observation_eq_prefix_of_coverage {N : ℕ} {mode : Mode} {R : ℝ}
    {ω : EventPath} (h : SamplerPath N mode R ω) (K : ℕ)
    (hk : CompletedCoverage (ω K).1) :
    genealogyObservation N ω = prefixGenealogyObservation N K ω :=
  genealogyObservation_eq_prefix N K ω h.time_monotone (h.completed_of_coverage K hk)

theorem SamplerPath.genealogy_eq_first_agreement {N : ℕ} {mode : Mode} {R : ℝ}
    {ω : EventPath} (h : SamplerPath N mode R ω) (q : GenomicProbe)
    (i j : Fin N) (K : ℕ)
    (he : ancestorLabel N ω q i K = ancestorLabel N ω q j K)
    (hb : ∀ k < K, ancestorLabel N ω q i k ≠ ancestorLabel N ω q j k) :
    genealogyObservation N ω q i j = ENNReal.ofReal (ω K).1.1 := by
  apply le_antisymm
  · exact iInf_le_of_le K (by simp [he])
  · apply le_iInf
    intro k
    by_cases hk : k < K
    · simp [hb k hk]
    · have hkl : K ≤ k := Nat.le_of_not_gt hk
      have hek := ancestorLabel_equal_later N ω q i j K k hkl he
      simp only [hek, ite_eq_left]
      exact ENNReal.ofReal_le_ofReal (h.time_monotone hkl)

theorem SamplerPath.record_time {N : ℕ} {mode : Mode} {R : ℝ} {ω : EventPath}
    (h : SamplerPath N mode R ω) (k : ℕ) : (ω k).2.1 = (ω k).1.1 := by
  cases k with
  | zero => rw [h.1]; rfl
  | succ k =>
    obtain ⟨u, _, _, _, _, _, _, hu⟩ := h.2 k
    rw [hu]
    exact sampleStep_record_time mode R _ u

theorem SamplerPath.genealogy_diagonal {N : ℕ} {mode : Mode} {R : ℝ}
    {ω : EventPath} (h : SamplerPath N mode R ω) (q : GenomicProbe) (i : Fin N) :
    genealogyObservation N ω q i i = 0 := by
  apply le_antisymm
  · exact iInf_le_of_le 0 (by simp [h.1, initialState])
  · exact bot_le

end Rhone.Coalescent.IntervalProcess
