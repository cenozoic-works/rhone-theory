/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.TypedAncestralChain.Event

/-! # The sampling probability is the measure of a path event -/

@[expose] public section

namespace Rhone.Coalescent.TypedAncestralChain

open Finset TwoLocusGenealogy LinearAlgebra.Recursion MeasureTheory ProbabilityTheory
open Preorder

variable {n KA KB : ℕ} {θA θB ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}
variable {σA : Fin n → Fin KA} {σB : Fin n → Fin KB}

theorem hitN_mono (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (hπA : ∀ i, 0 ≤ πA i)
    (hπB : ∀ j, 0 ≤ πB j) (N : ℕ) {L : Finset (Lin n)} (hw : WF L) :
    hitN σA σB θA θB ρ πA πB N L ≤ hitN σA σB θA θB ρ πA πB (N + 1) L := by
  by_cases hcl : Clean σA σB L
  · rw [hitN_eq_fitN N hw hcl, hitN_eq_fitN (N + 1) hw hcl]
    exact fitN_mono hθA hθB hρ hπA hπB N _
  · rw [hitN_eq_zero N hcl, hitN_eq_zero (N + 1) hcl]

theorem hitN_le_one (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (hπA : ∀ i, 0 ≤ πA i)
    (hsA : ∑ i, πA i = 1) (hπB : ∀ j, 0 ≤ πB j) (hsB : ∑ j, πB j = 1) (N : ℕ)
    {L : Finset (Lin n)} (hw : WF L) : hitN σA σB θA θB ρ πA πB N L ≤ 1 := by
  by_cases hcl : Clean σA σB L
  · rw [hitN_eq_fitN N hw hcl]
    exact fitN_le_one hθA hθB hρ hπA hsA hπB hsB N _
  · rw [hitN_eq_zero N hcl]
    norm_num

theorem hitS_mono (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (hπA : ∀ i, 0 ≤ πA i)
    (hπB : ∀ j, 0 ≤ πB j) (N : ℕ) {s : TS n KA KB} (hs : WFT s.st) :
    hitS σA σB θA θB ρ πA πB N s ≤ hitS σA σB θA θB ρ πA πB (N + 1) s := by
  rw [hitS, hitS, hitNT_eq hθA hθB hρ N hs, hitNT_eq hθA hθB hρ (N + 1) hs]
  split_ifs with hf
  · exact hitN_mono hθA hθB hρ hπA hπB N hs.wf
  · exact le_refl 0

theorem hitS_le_one (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (hπA : ∀ i, 0 ≤ πA i)
    (hsA : ∑ i, πA i = 1) (hπB : ∀ j, 0 ≤ πB j) (hsB : ∑ j, πB j = 1) (N : ℕ)
    {s : TS n KA KB} (hs : WFT s.st) : hitS σA σB θA θB ρ πA πB N s ≤ 1 := by
  rw [hitS, hitNT_eq hθA hθB hρ N hs]
  split_ifs with hf
  · exact hitN_le_one hθA hθB hρ hπA hsA hπB hsB N hs.wf
  · norm_num

theorem ofReal_iSup_of_monotone {f : ℕ → ℝ} (hmono : Monotone f) (hbdd : ∀ N, f N ≤ 1) :
    ENNReal.ofReal (⨆ N, f N) = ⨆ N, ENNReal.ofReal (f N) := by
  have hb : BddAbove (Set.range f) := by
    refine ⟨1, ?_⟩
    rintro x ⟨N, rfl⟩
    exact hbdd N
  have h1 : Filter.Tendsto f Filter.atTop (nhds (⨆ N, f N)) := tendsto_atTop_ciSup hmono hb
  have h2 : Filter.Tendsto (fun N => ENNReal.ofReal (f N)) Filter.atTop
      (nhds (ENNReal.ofReal (⨆ N, f N))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp h1
  have h3 : Filter.Tendsto (fun N => ENNReal.ofReal (f N)) Filter.atTop
      (nhds (⨆ N, ENNReal.ofReal (f N))) :=
    tendsto_atTop_iSup (fun a b hab => ENNReal.ofReal_le_ofReal (hmono hab))
  exact tendsto_nhds_unique h2 h3

section Event

variable (h : Adm θA θB ρ πA πB)

theorem ae_stay {E : Set (TS n KA KB)} (hE : Absorbing θA θB ρ E) (s : TS n KA KB) :
    ∀ᵐ ω ∂(argTrajT θA θB ρ πA πB h s), ∀ k, ω k ∈ E → ω (k + 1) ∈ E := by
  rw [MeasureTheory.ae_all_iff]
  intro k
  rw [MeasureTheory.ae_iff]
  have hset : {ω : (_ : ℕ) → TS n KA KB | ¬ (ω k ∈ E → ω (k + 1) ∈ E)}
      = {ω : (_ : ℕ) → TS n KA KB | ω k ∈ E ∧ ω (k + 1) ∉ E} := by
    ext ω
    exact Classical.not_imp
  rw [hset]
  exact measure_escape_zero h hE k s

theorem stay_le {E : Set (TS n KA KB)} {ω : (_ : ℕ) → TS n KA KB}
    (hω : ∀ k, ω k ∈ E → ω (k + 1) ∈ E) {k N : ℕ} (hkN : k ≤ N)
    (hk : ω k ∈ E) : ω N ∈ E := by
  induction N, hkN using Nat.le_induction with
  | base => exact hk
  | succ M _ ih => exact hω M ih

theorem measure_ever_eq_iSup {E : Set (TS n KA KB)} (hE : Absorbing θA θB ρ E)
    (s : TS n KA KB) :
    argTrajT θA θB ρ πA πB h s {ω | ∃ k, ω k ∈ E}
      = ⨆ N, argTrajT θA θB ρ πA πB h s {ω | ω N ∈ E} := by
  set μ := argTrajT θA θB ρ πA πB h s with hμ
  set A : ℕ → Set ((_ : ℕ) → TS n KA KB) := fun N => {ω | ω N ∈ E} with hA
  set B : ℕ → Set ((_ : ℕ) → TS n KA KB) := fun N => ⋃ k, ⋃ (_ : k ≤ N), A k with hB
  have hBmono : Monotone B := by
    intro N M hNM
    exact Set.iUnion_mono fun k => Set.iUnion_mono' fun hk => ⟨hk.trans hNM, le_rfl⟩
  have hunion : (⋃ N, B N) = {ω | ∃ k, ω k ∈ E} := by
    ext ω
    constructor
    · rintro hw
      obtain ⟨N, hN⟩ := Set.mem_iUnion.1 hw
      obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hN
      obtain ⟨_, hk2⟩ := Set.mem_iUnion.1 hk
      exact ⟨k, hk2⟩
    · rintro ⟨k, hk⟩
      exact Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨le_rfl, hk⟩⟩⟩
  have hBA : ∀ N, μ (B N) = μ (A N) := by
    intro N
    refine le_antisymm ?_ (measure_mono (fun ω hω => Set.mem_iUnion.2
      ⟨N, Set.mem_iUnion.2 ⟨le_rfl, hω⟩⟩))
    refine measure_mono_ae ?_
    filter_upwards [ae_stay h hE s] with ω hω hωB
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hωB
    obtain ⟨hkN, hk2⟩ := Set.mem_iUnion.1 hk
    exact stay_le hω hkN hk2
  rw [← hunion, hBmono.measure_iUnion]
  exact iSup_congr hBA

theorem measure_hit_ever (hθA : 0 < θA) (hθB : 0 < θB) {s : TS n KA KB} (hs : WFT s.st) :
    argTrajT θA θB ρ πA πB h s {ω | ∃ k, ω k ∈ TFin σA σB}
      = ENNReal.ofReal (⨆ N, hitS σA σB θA θB ρ πA πB N s) := by
  rw [measure_ever_eq_iSup h absorbing_TFin s]
  have hval : ∀ N, argTrajT θA θB ρ πA πB h s {ω | ω N ∈ TFin σA σB}
      = ENNReal.ofReal (hitS σA σB θA θB ρ πA πB N s) := fun N => measure_eval_mem h N s
  simp only [hval]
  exact (ofReal_iSup_of_monotone
    (monotone_nat_of_le_succ fun N => hitS_mono hθA hθB h.rho h.piA h.piB N hs)
    (fun N => hitS_le_one hθA hθB h.rho h.piA h.sumA h.piB h.sumB N hs)).symm

theorem measure_hit_ever_eq_hitProb (hθA : 0 < θA) (hθB : 0 < θB) {s : TS n KA KB}
    (hs : WFT s.st) (hf : Fits σA σB s.st) :
    argTrajT θA θB ρ πA πB h s {ω | ∃ k, ω k ∈ TFin σA σB}
      = ENNReal.ofReal (hitProb σA σB θA θB ρ πA πB s.st.1) := by
  rw [measure_hit_ever h hθA hθB hs, hitProb]
  refine congrArg ENNReal.ofReal (iSup_congr fun N => ?_)
  rw [hitS, hitNT_eq hθA hθB h.rho N hs, ite_eq_left hf]

theorem measure_hit_ever_initT (hθA : 0 < θA) (hθB : 0 < θB) :
    argTrajT θA θB ρ πA πB h ⟨initT n KA KB⟩ {ω | ∃ k, ω k ∈ TFin σA σB}
      = ENNReal.ofReal (LinearAlgebra.Recursion.q (πA := πA) (πB := πB) hθA hθB h.rho
          (cSample σA σB)) := by
  have h1 := measure_hit_ever_eq_hitProb (σA := σA) (σB := σB) h hθA hθB
    (s := (⟨initT n KA KB⟩ : TS n KA KB)) initT_wft initT_fits
  rw [h1]
  exact congrArg ENNReal.ofReal
    (hitProb_fullState hθA hθB h.rho h.piA h.sumA h.piB h.sumB)

theorem mem_TFin_iff {t : TS n KA KB} (ht : WFT t.st) :
    t ∈ TFin σA σB ↔ t.st.1 = ∅ ∧ (∀ k, t.st.2.1 k = some (σA k))
      ∧ (∀ k, t.st.2.2 k = some (σB k)) := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, ((fits_iff_eq ht h1).1 h2).1, ((fits_iff_eq ht h1).1 h2).2⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, (fits_iff_eq ht h1).2 ⟨h2, h3⟩⟩

end Event

theorem fits_one_allele (t : TSt n 1 1) :
    Fits (fun _ => (0 : Fin 1)) (fun _ => (0 : Fin 1)) t :=
  ⟨fun _ i _ => Subsingleton.elim _ i, fun _ j _ => Subsingleton.elim _ j⟩

theorem TFin_one_allele :
    TFin (fun _ => (0 : Fin 1)) (fun _ => (0 : Fin 1))
      = {t : TS n 1 1 | t.st.1 = ∅} := by
  ext t
  exact ⟨fun ht => ht.1, fun ht => ⟨ht, fits_one_allele t.st⟩⟩

theorem adm_one_allele (hθA : 0 ≤ θA) (hθB : 0 ≤ θB) (hρ : 0 ≤ ρ) :
    Adm θA θB ρ (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => (1 : ℝ)) :=
  ⟨hθA, hθB, hρ, fun _ => zero_le_one, fun _ => zero_le_one, by simp, by simp⟩

end Rhone.Coalescent.TypedAncestralChain
