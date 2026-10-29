/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.TwoLocusChain
public import Rhone.Coalescent.WeakSelectionWright
public import Rhone.Coalescent.TypedAncestralChain.Sampling
public import Rhone.MarkovChain.LumpingTrajectory
public import Rhone.MarkovChain.ClosedHitting

/-! # The two-locus sampling probability with mutation and the Core chain definitions -/

@[expose] public section
namespace Rhone.Coalescent
open MeasureTheory ProbabilityTheory Finset Diffusion Rhone.LinearAlgebra MarkovChain
open TwoLocusGenealogy
open TypedAncestralChain Recursion

variable {n KA KB : ℕ} {θA θB ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}
variable {σA : Fin n → Fin KA} {σB : Fin n → Fin KB}

theorem isSolution_iff_eq_qProb (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hπA : ∀ i, 0 ≤ πA i) (hsA : ∑ i, πA i = 1) (hπB : ∀ j, 0 ≤ πB j)
    (hsB : ∑ j, πB j = 1) (q : Config KA KB → ℝ) :
    IsSolution θA θB ρ πA πB q ↔ q = qProb θA θB ρ πA πB := by
  constructor
  · intro hq
    exact IsSolution.unique hθA hθB hρ hq (qProb_isSolution hθA hθB hρ hπA hsA hπB hsB)
  · rintro rfl
    exact qProb_isSolution hθA hθB hρ hπA hsA hπB hsB

theorem existsUnique_isSolution_real (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hπA : ∀ i, 0 ≤ πA i) (hsA : ∑ i, πA i = 1) (hπB : ∀ j, 0 ≤ πB j)
    (hsB : ∑ j, πB j = 1) :
    ∃! q : Config KA KB → ℝ, IsSolution θA θB ρ πA πB q :=
  ⟨qProb θA θB ρ πA πB, qProb_isSolution hθA hθB hρ hπA hsA hπB hsB,
    fun q hq => (isSolution_iff_eq_qProb hθA hθB hρ hπA hsA hπB hsB q).1 hq⟩

noncomputable def argChainT (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ)
    (h : Adm θA θB ρ πA πB) : FinChain (TS n KA KB) where
  P := fun s t => transS θA θB ρ πA πB s t
  nonneg := fun s t => transS_nonneg h.thA h.thB h.rho h.piA h.piB s t
  row_sum := fun s => sum_transS h.sumA h.sumB s

theorem argChainT_P (h : Adm θA θB ρ πA πB) (s t : TS n KA KB) :
    (argChainT θA θB ρ πA πB h).P s t = transS θA θB ρ πA πB s t := rfl

theorem argChainT_pathLaw (h : Adm θA θB ρ πA πB) (s : TS n KA KB) :
    (argChainT θA θB ρ πA πB h).pathLaw s = argTrajT θA θB ρ πA πB h s := rfl

theorem argChainT_pathLaw_real_hit (h : Adm θA θB ρ πA πB) (hθA : 0 < θA) (hθB : 0 < θB)
    {s : TS n KA KB} (hs : WFT s.st) (hf : Fits σA σB s.st) (hcl : Clean σA σB s.st.1) :
    ((argChainT θA θB ρ πA πB h).pathLaw s).real {ω | ∃ k, ω k ∈ TFin σA σB} =
      qProb θA θB ρ πA πB (cfg σA σB s.st.1) := by
  rw [argChainT_pathLaw, measureReal_def, measure_hit_ever_eq_hitProb h hθA hθB hs hf,
    hitProb_eq_qProb hs.wf hcl, ENNReal.toReal_ofReal]
  exact qProb_nonneg hθA hθB h.rho h.piA h.sumA h.piB h.sumB _

theorem argChainT_pathLaw_real_sample (h : Adm θA θB ρ πA πB) (hθA : 0 < θA)
    (hθB : 0 < θB) (σA : Fin n → Fin KA) (σB : Fin n → Fin KB) :
    ((argChainT θA θB ρ πA πB h).pathLaw ⟨initT n KA KB⟩).real
        {ω | ∃ k, ω k ∈ TFin σA σB} =
      qProb θA θB ρ πA πB (cSample σA σB) :=
  (argChainT_pathLaw_real_hit (σA := σA) (σB := σB) (s := ⟨initT n KA KB⟩) h hθA hθB
    initT_wft initT_fits fullState_clean).trans
    (congrArg (qProb θA θB ρ πA πB) cfg_fullState)

theorem isSolution_eq_pathLaw_real_sample (h : Adm θA θB ρ πA πB) (hθA : 0 < θA)
    (hθB : 0 < θB) {q : Config KA KB → ℝ} (hq : IsSolution θA θB ρ πA πB q)
    (σA : Fin n → Fin KA) (σB : Fin n → Fin KB) :
    q (cSample σA σB) =
      ((argChainT θA θB ρ πA πB h).pathLaw ⟨initT n KA KB⟩).real
        {ω | ∃ k, ω k ∈ TFin σA σB} := by
  rw [argChainT_pathLaw_real_sample h hθA hθB σA σB,
    (isSolution_iff_eq_qProb hθA hθB h.rho h.piA h.sumA h.piB h.sumB q).1 hq]

open Classical in
theorem argChainT_isClosedSet_wft (h : Adm θA θB ρ πA πB) :
    (argChainT (n := n) θA θB ρ πA πB h).IsClosedSet
      (Finset.univ.filter fun s : TS n KA KB => WFT s.st) := by
  intro s hs t ht
  have hs' : WFT s.st := (Finset.mem_filter.1 hs).2
  have ht' : ¬ WFT t.st := fun hc => ht (Finset.mem_filter.2 ⟨Finset.mem_univ t, hc⟩)
  change transS θA θB ρ πA πB s t = 0
  by_cases hd : 0 < dtot θA θB ρ s.st.1
  · have hne : ∀ u : TSt n KA KB, WFT u → (if u = t.st then (1 : ℝ) else 0) = 0 :=
      fun u hu => ite_eq_right fun (hc : u = t.st) => ht' (hc ▸ hu)
    have h1 : (∑ p ∈ s.st.1, ∑ q ∈ s.st.1.erase p,
        (if ((coalL s.st.1 p q, s.st.2.1, s.st.2.2) : TSt n KA KB) = t.st then (1 : ℝ)
          else 0)) = 0 :=
      Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun q hq => hne _ (hs'.coal hp hq)
    have h2 : (∑ p ∈ carA s.st.1, ∑ i, πA i *
        (if ((mutAL s.st.1 p, setT s.st.2.1 p.1 i, s.st.2.2) : TSt n KA KB) = t.st
          then (1 : ℝ) else 0)) = 0 :=
      Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun i _ => by
        rw [hne _ (hs'.mutA (mem_carA.1 hp).1 i), mul_zero]
    have h3 : (∑ p ∈ carB s.st.1, ∑ j, πB j *
        (if ((mutBL s.st.1 p, s.st.2.1, setT s.st.2.2 p.2 j) : TSt n KA KB) = t.st
          then (1 : ℝ) else 0)) = 0 :=
      Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun j _ => by
        rw [hne _ (hs'.mutB (mem_carB.1 hp).1 j), mul_zero]
    have h4 : (∑ p ∈ carC s.st.1,
        (if ((recL s.st.1 p, s.st.2.1, s.st.2.2) : TSt n KA KB) = t.st then (1 : ℝ)
          else 0)) = 0 :=
      Finset.sum_eq_zero fun p hp =>
        hne _ (hs'.recomb (mem_carC.1 hp).1 (mem_carC.1 hp).2.1 (mem_carC.1 hp).2.2)
    rw [transS, transT_of_dtot_pos hd, stepT, h1, h2, h3, h4]
    simp
  · rw [transS_of_nonpos hd]
    exact ite_eq_right fun (hc : t = s) => ht' (hc ▸ hs')

theorem argChainT_pathLaw_real_sample_explicit (h : Adm θA θB ρ πA πB) (hθA : 0 < θA)
    (hθB : 0 < θB) (σA : Fin n → Fin KA) (σB : Fin n → Fin KB) :
    ((argChainT θA θB ρ πA πB h).pathLaw ⟨initT n KA KB⟩).real
        {ω | ∃ k, (ω k).st = (∅, fun i => some (σA i), fun i => some (σB i))} =
      qProb θA θB ρ πA πB (cSample σA σB) := by
  classical
  rw [← argChainT_pathLaw_real_sample h hθA hθB σA σB]
  set W : Finset (TS n KA KB) := Finset.univ.filter fun s : TS n KA KB => WFT s.st with hW
  have hcl : (argChainT (n := n) θA θB ρ πA πB h).IsClosedSet W :=
    argChainT_isClosedSet_wft h
  have hinit : (⟨initT n KA KB⟩ : TS n KA KB) ∈ W :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, initT_wft⟩
  have hae : ∀ᵐ ω ∂(argChainT θA θB ρ πA πB h).pathLaw ⟨initT n KA KB⟩,
      ∀ k, WFT (ω k).st := by
    rw [ae_all_iff]
    intro k
    have hz : ((argChainT θA θB ρ πA πB h).pathLaw ⟨initT n KA KB⟩).real
        {ω | ω k ∈ Wᶜ} = 0 := by
      rw [FinChain.pathLaw_real_eval_mem]
      exact Finset.sum_eq_zero fun a ha =>
        hcl.stepN_eq_zero k hinit (Finset.mem_compl.1 ha)
    have hz' := (measureReal_eq_zero_iff (measure_ne_top _ _)).1 hz
    rw [ae_iff]
    refine measure_mono_null (fun ω hω => ?_) hz'
    exact Finset.mem_compl.2 fun hc => hω (Finset.mem_filter.1 hc).2
  refine measureReal_congr ?_
  filter_upwards [hae] with ω hω
  refine propext ⟨?_, ?_⟩
  · rintro ⟨k, hk⟩
    refine ⟨k, (mem_TFin_iff (hω k)).2 ?_⟩
    rw [hk]
    exact ⟨rfl, fun _ => rfl, fun _ => rfl⟩
  · rintro ⟨k, hk⟩
    obtain ⟨h1, h2, h3⟩ := (mem_TFin_iff (hω k)).1 hk
    exact ⟨k, Prod.ext h1 (Prod.ext (funext h2) (funext h3))⟩

def lineagesOf (s : TS n KA KB) : ASt n := s.st.1

theorem lineagesOf_apply (s : TS n KA KB) : lineagesOf s = s.st.1 := rfl

theorem argChainT_lumps (h : Adm θA θB ρ πA πB) :
    (argChainT (n := n) θA θB ρ πA πB h).Lumps (lineagesOf (KA := KA) (KB := KB))
      (argRateChain θA θB ρ h.thA h.thB h.rho).jumpChain := by
  intro s M
  change (∑ t : TS n KA KB with lineagesOf t = M, (argChainT θA θB ρ πA πB h).P s t) =
    (argRateChain θA θB ρ h.thA h.thB h.rho).jumpChain.P (lineagesOf s) M
  have h2 : 2 * (argRateChain θA θB ρ h.thA h.thB h.rho).rate (lineagesOf s) =
      dtot θA θB ρ s.st.1 :=
    (congrArg (fun x : ℝ => 2 * x) (argRateChain_rate h.thA h.thB h.rho (lineagesOf s))).trans
      (two_mul_rateTot (θA := θA) (θB := θB) (ρ := ρ) s.st.1)
  by_cases hd : 0 < dtot θA θB ρ s.st.1
  · have hJ : (argRateChain θA θB ρ h.thA h.thB h.rho).jumpChain.P (lineagesOf s) M =
        stepU θA θB ρ (fun M' : ASt n => if M' = M then (1 : ℝ) else 0) s.st.1 /
          dtot θA θB ρ s.st.1 :=
      (argRateChain_jumpChain_P h.thA h.thB h.rho (lineagesOf s) M (Or.inl hd)).trans
        (trans_of_pos (L := s.st.1) M hd)
    rw [hJ]
    have hterm : ∀ t : TS n KA KB, (argChainT θA θB ρ πA πB h).P s t =
        stepT θA θB ρ πA πB (fun t' => if t' = t.st then 1 else 0) s.st /
          dtot θA θB ρ s.st.1 := fun t => transT_of_dtot_pos hd
    rw [Finset.sum_congr rfl fun t _ => hterm t, ← Finset.sum_div, Finset.sum_filter]
    congr 1
    have hmul : ∀ t : TS n KA KB,
        (if lineagesOf t = M then
          stepT θA θB ρ πA πB (fun t' => if t' = t.st then 1 else 0) s.st else 0) =
        (if lineagesOf t = M then (1 : ℝ) else 0) *
          stepT θA θB ρ πA πB (fun t' => if t' = t.st then 1 else 0) s.st := by
      intro t
      split_ifs <;> simp
    rw [Finset.sum_congr rfl fun t _ => hmul t,
      stepT_sum (fun t : TS n KA KB => if lineagesOf t = M then (1 : ℝ) else 0)
        (fun (t : TS n KA KB) (t' : TSt n KA KB) => if t' = t.st then (1 : ℝ) else 0) s.st,
      ← stepT_of_fst (θA := θA) (θB := θB) (ρ := ρ) h.sumA h.sumB
        (fun M' : ASt n => if M' = M then (1 : ℝ) else 0) s.st]
    congr 1
    funext t'
    rw [Finset.sum_eq_single (⟨t'⟩ : TS n KA KB)]
    · simp [lineagesOf]
      congr
    · intro b _ hb
      have hne : t' ≠ b.st := fun hc => hb (by cases b; simp_all)
      simp [hne]
    · intro hx
      exact absurd (Finset.mem_univ _) hx
  · have hr : (argRateChain θA θB ρ h.thA h.thB h.rho).rate (lineagesOf s) = 0 := by
      have h0 := dtot_nonneg h.thA h.thB h.rho s.st.1
      linarith
    have hterm : ∀ t : TS n KA KB, (argChainT θA θB ρ πA πB h).P s t =
        if t = s then 1 else 0 := fun t => transS_of_nonpos hd
    have hP : (argRateChain θA θB ρ h.thA h.thB h.rho).jumpChain.P (lineagesOf s) M =
        if (lineagesOf s) = M then 1 else 0 := by
      change RateChain.jumpMatrix _ _ _ = _
      unfold RateChain.jumpMatrix
      rw [ite_eq_left hr]
    rw [hP, Finset.sum_congr rfl fun t _ => hterm t, Finset.sum_ite_eq']
    simp [Finset.mem_filter]

theorem argChainT_map_pathLaw (h : Adm θA θB ρ πA πB) (s : TS n KA KB) :
    ((argChainT θA θB ρ πA πB h).pathLaw s).map (fun ω k => lineagesOf (ω k)) =
      (argRateChain θA θB ρ h.thA h.thB h.rho).jumpChain.pathLaw (lineagesOf s) :=
  (argChainT_lumps h).map_pathLaw s

theorem sum_transS_fibre_eq_trans (h : Adm θA θB ρ πA πB) (s : TS n KA KB) (M : ASt n)
    (hs : 0 < dtot θA θB ρ s.st.1 ∨ s.st.1 = (∅ : Finset (Lin n))) :
    (∑ t : TS n KA KB with lineagesOf t = M, transS θA θB ρ πA πB s t) =
      trans θA θB ρ s.st.1 M :=
  (argChainT_lumps h s M).trans (argRateChain_jumpChain_P h.thA h.thB h.rho _ M hs)

theorem qProb_eq_qOne_of_nB (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hπA : ∀ i, 0 ≤ πA i) (hsA : ∑ i, πA i = 1) (hπB : ∀ j, 0 ≤ πB j)
    (hsB : ∑ j, πB j = 1) (ξ : Config KA KB) (hξ : ξ.nB = 0) :
    qProb θA θB ρ πA πB ξ = qOne θA πA ξ.a :=
  (qProb_isSolution hθA hθB hρ hπA hsA hπB hsB).eq_qOne_of_nB hθA ξ hξ

theorem qProb_eq_qOne_of_nA (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hπA : ∀ i, 0 ≤ πA i) (hsA : ∑ i, πA i = 1) (hπB : ∀ j, 0 ≤ πB j)
    (hsB : ∑ j, πB j = 1) (ξ : Config KA KB) (hξ : ξ.nA = 0) :
    qProb θA θB ρ πA πB ξ = qOne θB πB ξ.b :=
  (qProb_isSolution hθA hθB hρ hπA hsA hπB hsB).eq_qOne_of_nA hθB ξ hξ

/-- Source: ewens2004, eq. (5.70)–(5.71), p. 174. -/
theorem qProb_eq_selMoment_of_nB {πA : Fin 2 → ℝ} (hθA : 0 < θA) (hθB : 0 < θB)
    (hρ : 0 ≤ ρ) (h0 : 0 < πA 0) (h1 : 0 < πA 1) (hsum : πA 0 + πA 1 = 1)
    (hπB : ∀ j, 0 ≤ πB j) (hsB : ∑ j, πB j = 1) (ξ : Config 2 KB) (hξ : ξ.nB = 0) :
    qProb θA θB ρ πA πB ξ = selMoment 0 (θA * πA 0) (θA * πA 1) (ξ.a 0) (ξ.a 1) := by
  have hπA : ∀ i, 0 ≤ πA i := by
    intro i
    fin_cases i
    · exact h0.le
    · exact h1.le
  have hsA : ∑ i, πA i = 1 := by rw [Fin.sum_univ_two, hsum]
  rw [qProb_eq_qOne_of_nB hθA hθB hρ hπA hsA hπB hsB ξ hξ,
    selMoment_zero_eq_qOne hθA h0 h1 hsum]

theorem qProb_eC (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (hπA : ∀ i, 0 ≤ πA i)
    (hsA : ∑ i, πA i = 1) (hπB : ∀ j, 0 ≤ πB j) (hsB : ∑ j, πB j = 1) (i : Fin KA)
    (j : Fin KB) :
    qProb θA θB ρ πA πB (Config.eC i j) =
      qProb θA θB ρ πA πB (Config.eA i) * qProb θA θB ρ πA πB (Config.eB j) := by
  have hq := qProb_isSolution hθA hθB hρ hπA hsA hπB hsB
  rw [hq.bdryC, hq.bdryA, hq.bdryB]

end Rhone.Coalescent
