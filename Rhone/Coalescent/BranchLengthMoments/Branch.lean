/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.BranchLengthMoments.Occupation

/-! # Branch-length functionals and total rates for the two-locus genealogy generator -/

@[expose] public section

namespace Rhone.Coalescent.BranchLengthMoments

open Finset TwoLocusGenealogy TypedAncestralChain LinearAlgebra.Recursion
open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

variable {n KA KB : ℕ} {θA θB ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}

noncomputable def rateTotS (θA θB ρ : ℝ) (s : TS n KA KB) : ℝ := rateTot θA θB ρ s.st.1

theorem two_mul_rateTotS (s : TS n KA KB) :
    2 * rateTotS θA θB ρ s = dtotS θA θB ρ s := two_mul_rateTot _

theorem rateTotS_nonneg (hθA : 0 ≤ θA) (hθB : 0 ≤ θB) (hρ : 0 ≤ ρ) (s : TS n KA KB) :
    0 ≤ rateTotS θA θB ρ s := by
  have h2 := two_mul_rateTotS (θA := θA) (θB := θB) (ρ := ρ) s
  have hd : 0 ≤ dtotS θA θB ρ s := dtot_nonneg hθA hθB hρ s.st.1
  linarith

theorem rateTotS_pos_of_transient (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    {s : TS n KA KB} (hs : Transient s) : 0 < rateTotS θA θB ρ s := by
  have h2 := two_mul_rateTotS (θA := θA) (θB := θB) (ρ := ρ) s
  have hd : 0 < dtotS θA θB ρ s := dtotS_pos_of_transient hθA hθB hρ hs
  linarith

@[simp] theorem rateTotS_of_absorbed {s : TS n KA KB} (hs : s.st.1 = ∅) :
    rateTotS θA θB ρ s = 0 := by
  have h2 := two_mul_rateTotS (θA := θA) (θB := θB) (ρ := ρ) s
  have hd : dtotS θA θB ρ s = 0 := by rw [dtotS, hs, dtot_empty]
  linarith

def rA (F : Finset (Finset (Fin n))) (t : TS n KA KB) : ℝ :=
  ((t.st.1.filter fun p => p.1 ∈ F).card : ℝ)

theorem rA_nonneg (F : Finset (Finset (Fin n))) (t : TS n KA KB) : 0 ≤ rA F t :=
  Nat.cast_nonneg _

@[simp] theorem rA_of_absorbed {F : Finset (Finset (Fin n))} {t : TS n KA KB}
    (ht : t.st.1 = ∅) : rA F t = 0 := by
  rw [rA, ht, Finset.filter_empty, Finset.card_empty, Nat.cast_zero]

theorem card_line_le_one {L : Finset (Lin n)} (hw : WF L) {S : Finset (Fin n)}
    (hS : S.Nonempty) : (L.filter fun p => p.1 = S).card ≤ 1 := by
  refine Finset.card_le_one.2 fun p hp q hq => ?_
  rw [Finset.mem_filter] at hp hq
  by_contra hne
  obtain ⟨k, hk⟩ := hS
  have hd := hw.disjA p hp.1 q hq.1 hne
  have hkp : k ∈ p.1 := by rw [hp.2]; exact hk
  have hkq : k ∈ q.1 := by rw [hq.2]; exact hk
  exact (Finset.disjoint_left.1 hd) hkp hkq

theorem rA_eq_sum (F : Finset (Finset (Fin n))) (t : TS n KA KB) :
    rA F t = ∑ S ∈ F, rA {S} t := by
  classical
  have hcast : ∀ G : Finset (Finset (Fin n)),
      rA G t = ∑ p ∈ t.st.1, if p.1 ∈ G then (1 : ℝ) else 0 := by
    intro G
    rw [rA, Finset.card_filter, Nat.cast_sum]
    exact Finset.sum_congr rfl fun p _ => by split_ifs <;> simp
  have hsingle : ∀ S : Finset (Fin n),
      rA ({S} : Finset (Finset (Fin n))) t = ∑ p ∈ t.st.1, if p.1 = S then (1 : ℝ) else 0 := by
    intro S
    rw [hcast]
    exact Finset.sum_congr rfl fun p _ => by simp
  rw [hcast F]
  simp only [hsingle]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_ite_eq F p.1 fun _ => (1 : ℝ)]

def splitFam (S : Finset (Fin n)) : Finset (Finset (Fin n)) := {S, Sᶜ}

def cladeFam (n : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.filter fun S => S.Nonempty ∧ S ≠ Finset.univ

theorem mem_cladeFam {S : Finset (Fin n)} :
    S ∈ cladeFam n ↔ S.Nonempty ∧ S ≠ Finset.univ := by
  simp [cladeFam]

noncomputable def holdA (θA θB ρ : ℝ) (F : Finset (Finset (Fin n))) (t : TS n KA KB) : ℝ :=
  rA F t / rateTotS θA θB ρ t

theorem holdA_nonneg (hθA : 0 ≤ θA) (hθB : 0 ≤ θB) (hρ : 0 ≤ ρ)
    (F : Finset (Finset (Fin n))) (t : TS n KA KB) : 0 ≤ holdA θA θB ρ F t :=
  div_nonneg (rA_nonneg F t) (rateTotS_nonneg hθA hθB hρ t)

@[simp] theorem holdA_of_absorbed {F : Finset (Finset (Fin n))} {t : TS n KA KB}
    (ht : t.st.1 = ∅) : holdA θA θB ρ F t = 0 := by
  rw [holdA, rA_of_absorbed ht, zero_div]

theorem killed_holdA (F : Finset (Finset (Fin n))) :
    killed (holdA θA θB ρ F) = holdA (n := n) (KA := KA) (KB := KB) θA θB ρ F := by
  funext t
  by_cases ht : t.st.1 = ∅
  · rw [killed_of_absorbed ht, holdA_of_absorbed ht]
  · rw [killed_of_not_absorbed ht]

noncomputable def branchLen (θA θB ρ : ℝ) (F : Finset (Finset (Fin n)))
    (ω : (_ : ℕ) → TS n KA KB) : ℝ≥0∞ :=
  occAll (holdA θA θB ρ F) ω

theorem holdA_sum (F : Finset (Finset (Fin n))) (t : TS n KA KB) :
    holdA θA θB ρ F t = ∑ S ∈ F, holdA θA θB ρ {S} t := by
  rw [holdA, rA_eq_sum F t, Finset.sum_div]
  exact Finset.sum_congr rfl fun S _ => rfl

theorem branchLen_sum (hθA : 0 ≤ θA) (hθB : 0 ≤ θB) (hρ : 0 ≤ ρ)
    (F : Finset (Finset (Fin n))) (ω : (_ : ℕ) → TS n KA KB) :
    branchLen θA θB ρ F ω = ∑ S ∈ F, branchLen θA θB ρ {S} ω := by
  have hfun : holdA (n := n) (KA := KA) (KB := KB) θA θB ρ F
      = fun t => ∑ S ∈ F, holdA (n := n) (KA := KA) (KB := KB) θA θB ρ {S} t :=
    funext fun t => holdA_sum F t
  rw [branchLen, hfun]
  exact occAll_finsetSum F (fun S => holdA θA θB ρ {S})
    (fun S t => holdA_nonneg hθA hθB hρ _ t) ω

theorem branchLen_eq_occ (F : Finset (Finset (Fin n))) (ω : (_ : ℕ) → TS n KA KB) :
    branchLen θA θB ρ F ω = occ (holdA θA θB ρ F) ω := by
  rw [occ_eq_occAll_killed, killed_holdA, branchLen]

theorem ae_occ_le_absTime (h : Adm θA θB ρ πA πB) (hθA : 0 < θA) (hθB : 0 < θB)
    {g : TS n KA KB → ℝ} (hg : ∀ t, 0 ≤ g t) {c : ℝ} (hc : ∀ t, g t ≤ c)
    {s : TS n KA KB} (hw : WF s.st.1) :
    ∀ᵐ ω ∂(argTrajT θA θB ρ πA πB h s),
      occ g ω ≤ ENNReal.ofReal c * (absTime ω : ℝ≥0∞) := by
  have hc0 : (0 : ℝ) ≤ c := le_trans (hg default) (hc default)
  filter_upwards [ae_lt_absTime_iff h hθA hθB hw] with ω hω
  have hzero : ∀ k ∉ Finset.range (absTime ω), ENNReal.ofReal (killed g (ω k)) = 0 := by
    intro k hk
    have hk' : ¬ k < absTime ω := by simpa using hk
    have hab : (ω k).st.1 = ∅ := by
      by_contra hcc
      exact hk' ((hω k).2 hcc)
    rw [killed_of_absorbed hab, ENNReal.ofReal_zero]
  have hsum : occ g ω = ∑ k ∈ Finset.range (absTime ω), ENNReal.ofReal (killed g (ω k)) :=
    tsum_eq_sum hzero
  rw [hsum]
  refine le_trans (Finset.sum_le_card_nsmul _ _ (ENNReal.ofReal c) ?_) ?_
  · intro k _
    refine ENNReal.ofReal_le_ofReal ?_
    rw [killed]
    split_ifs
    · exact hc0
    · exact hc _
  · rw [Finset.card_range, nsmul_eq_mul]
    exact le_of_eq (mul_comm _ _)

theorem measurable_absTime_enn :
    Measurable fun ω : (_ : ℕ) → TS n KA KB => (absTime ω : ℝ≥0∞) :=
  (measurable_of_countable fun k : ℕ => (k : ℝ≥0∞)).comp measurable_absTime

theorem lintegral_occ_pow_ne_top (h : Adm θA θB ρ πA πB) (hθA : 0 < θA) (hθB : 0 < θB)
    {g : TS n KA KB → ℝ} (hg : ∀ t, 0 ≤ g t) {c : ℝ} (hc : ∀ t, g t ≤ c) (m : ℕ)
    {s : TS n KA KB} (hw : WF s.st.1) :
    (∫⁻ ω, (occ g ω) ^ m ∂(argTrajT θA θB ρ πA πB h s)) ≠ ⊤ := by
  have hbound : ∀ᵐ ω ∂(argTrajT θA θB ρ πA πB h s),
      (occ g ω) ^ m ≤ (ENNReal.ofReal c) ^ m * (absTime ω : ℝ≥0∞) ^ m := by
    filter_upwards [ae_occ_le_absTime h hθA hθB hg hc hw] with ω hω
    calc (occ g ω) ^ m ≤ (ENNReal.ofReal c * (absTime ω : ℝ≥0∞)) ^ m := pow_le_pow_left' hω m
      _ = (ENNReal.ofReal c) ^ m * (absTime ω : ℝ≥0∞) ^ m := mul_pow _ _ _
  refine ne_top_of_le_ne_top ?_ (lintegral_mono_ae hbound)
  rw [lintegral_const_mul _ (measurable_absTime_enn.pow_const m)]
  exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    (lintegral_absTime_pow_lt_top h hθA hθB m hw)

theorem lintegral_occ_mul_ne_top (h : Adm θA θB ρ πA πB) (hθA : 0 < θA) (hθB : 0 < θB)
    {g₁ g₂ : TS n KA KB → ℝ} (hg₁ : ∀ t, 0 ≤ g₁ t) (hg₂ : ∀ t, 0 ≤ g₂ t) {c₁ c₂ : ℝ}
    (hc₁ : ∀ t, g₁ t ≤ c₁) (hc₂ : ∀ t, g₂ t ≤ c₂) {s : TS n KA KB} (hw : WF s.st.1) :
    (∫⁻ ω, occ g₁ ω * occ g₂ ω ∂(argTrajT θA θB ρ πA πB h s)) ≠ ⊤ := by
  have hbound : ∀ᵐ ω ∂(argTrajT θA θB ρ πA πB h s),
      occ g₁ ω * occ g₂ ω
        ≤ (ENNReal.ofReal c₁ * ENNReal.ofReal c₂) * (absTime ω : ℝ≥0∞) ^ 2 := by
    filter_upwards [ae_occ_le_absTime h hθA hθB hg₁ hc₁ hw,
      ae_occ_le_absTime h hθA hθB hg₂ hc₂ hw] with ω hω₁ hω₂
    calc occ g₁ ω * occ g₂ ω
        ≤ (ENNReal.ofReal c₁ * (absTime ω : ℝ≥0∞))
          * (ENNReal.ofReal c₂ * (absTime ω : ℝ≥0∞)) := mul_le_mul' hω₁ hω₂
      _ = (ENNReal.ofReal c₁ * ENNReal.ofReal c₂) * (absTime ω : ℝ≥0∞) ^ 2 := by ring
  refine ne_top_of_le_ne_top ?_ (lintegral_mono_ae hbound)
  rw [lintegral_const_mul _ (measurable_absTime_enn.pow_const 2)]
  exact ENNReal.mul_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    (lintegral_absTime_pow_lt_top h hθA hθB 2 hw)

theorem exists_holdA_bound (F : Finset (Finset (Fin n))) :
    ∃ c : ℝ, ∀ t : TS n KA KB, holdA θA θB ρ F t ≤ c := by
  obtain ⟨t₀, ht₀⟩ := Finite.exists_max fun t : TS n KA KB => holdA θA θB ρ F t
  exact ⟨holdA θA θB ρ F t₀, ht₀⟩

theorem lintegral_branchLen_pow_ne_top (h : Adm θA θB ρ πA πB) (hθA : 0 < θA) (hθB : 0 < θB)
    (F : Finset (Finset (Fin n))) (m : ℕ) {s : TS n KA KB} (hw : WF s.st.1) :
    (∫⁻ ω, (branchLen θA θB ρ F ω) ^ m ∂(argTrajT θA θB ρ πA πB h s)) ≠ ⊤ := by
  obtain ⟨c, hc⟩ := exists_holdA_bound (θA := θA) (θB := θB) (ρ := ρ) (KA := KA) (KB := KB) F
  have hcongr : ∀ ω : (_ : ℕ) → TS n KA KB,
      (branchLen θA θB ρ F ω) ^ m = (occ (holdA θA θB ρ F) ω) ^ m :=
    fun ω => by rw [branchLen_eq_occ]
  rw [lintegral_congr hcongr]
  exact lintegral_occ_pow_ne_top h hθA hθB (holdA_nonneg h.thA h.thB h.rho F) hc m hw

theorem lintegral_branchLen_mul_ne_top (h : Adm θA θB ρ πA πB) (hθA : 0 < θA) (hθB : 0 < θB)
    (F G : Finset (Finset (Fin n))) {s : TS n KA KB} (hw : WF s.st.1) :
    (∫⁻ ω, branchLen θA θB ρ F ω * branchLen θA θB ρ G ω
      ∂(argTrajT θA θB ρ πA πB h s)) ≠ ⊤ := by
  obtain ⟨c₁, hc₁⟩ := exists_holdA_bound (θA := θA) (θB := θB) (ρ := ρ) (KA := KA) (KB := KB) F
  obtain ⟨c₂, hc₂⟩ := exists_holdA_bound (θA := θA) (θB := θB) (ρ := ρ) (KA := KA) (KB := KB) G
  have hcongr : ∀ ω : (_ : ℕ) → TS n KA KB,
      branchLen θA θB ρ F ω * branchLen θA θB ρ G ω
        = occ (holdA θA θB ρ F) ω * occ (holdA θA θB ρ G) ω :=
    fun ω => by rw [branchLen_eq_occ, branchLen_eq_occ]
  rw [lintegral_congr hcongr]
  exact lintegral_occ_mul_ne_top h hθA hθB (holdA_nonneg h.thA h.thB h.rho F)
    (holdA_nonneg h.thA h.thB h.rho G) hc₁ hc₂ hw

def IsGenSol (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ) (r u : TS n KA KB → ℝ) : Prop :=
  (∀ t, ¬ Transient t → u t = 0)
    ∧ ∀ t, Transient t →
      rateTotS θA θB ρ t * ((∑ t', transS θA θB ρ πA πB t t' * u t') - u t) = - r t

theorem existsUnique_genSol (h : Adm θA θB ρ πA πB) (hθA : 0 < θA) (hθB : 0 < θB)
    (r : TS n KA KB → ℝ) : ∃! u : TS n KA KB → ℝ, IsGenSol θA θB ρ πA πB r u := by
  refine (existsUnique_congr fun u => ?_).1
    (existsUnique_generator h hθA hθB fun t => 2 * r t)
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun t ht => ?_⟩
    have hd := h2 t ht
    rw [← two_mul_rateTotS t] at hd
    linear_combination hd / 2
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun t ht => ?_⟩
    have hd := h2 t ht
    rw [← two_mul_rateTotS t]
    linear_combination 2 * hd

theorem isGenSol_step (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) {r u : TS n KA KB → ℝ}
    (hu : IsGenSol θA θB ρ πA πB r u) {t : TS n KA KB} (ht : Transient t) :
    u t - (∑ t', transS θA θB ρ πA πB t t' * u t') = r t / rateTotS θA θB ρ t := by
  have hpos : 0 < rateTotS θA θB ρ t := rateTotS_pos_of_transient hθA hθB hρ ht
  have hd := hu.2 t ht
  field_simp
  linarith

theorem lintegral_branchLen_eq (h : Adm θA θB ρ πA πB) (hθA : 0 < θA) (hθB : 0 < θB)
    (F : Finset (Finset (Fin n))) {u : TS n KA KB → ℝ}
    (hu : IsGenSol θA θB ρ πA πB (rA F) u) {s : TS n KA KB} (hw : WF s.st.1) :
    (∫⁻ ω, branchLen θA θB ρ F ω ∂(argTrajT θA θB ρ πA πB h s)) = ENNReal.ofReal (u s) := by
  have hu0 : ∀ t : TS n KA KB, WF t.st.1 → t.st.1 = ∅ → u t = 0 :=
    fun t _ hab => hu.1 t fun hc => hc.2 hab
  have hu2 : ∀ t : TS n KA KB, WF t.st.1 →
      u t = holdA θA θB ρ F t + ∑ t', transS θA θB ρ πA πB t t' * u t' := by
    intro t hwt
    by_cases htr : Transient t
    · have hst := isGenSol_step hθA hθB h.rho hu htr
      rw [holdA]
      linarith
    · have hab : t.st.1 = ∅ := by
        by_contra hc
        exact htr ⟨hwt, hc⟩
      rw [sum_transS_of_not_transient hwt htr u, hu0 t hwt hab, holdA_of_absorbed hab]
      ring
  exact lintegral_occAll_eq h closed_wf (holdA_nonneg h.thA h.thB h.rho F) hu2
    (tendsto_mstep_zero h hθA hθB hu0 hw) hw

theorem lintegral_occUpTo_branchLen (h : Adm θA θB ρ πA πB) (hθA : 0 < θA) (hθB : 0 < θB)
    (F : Finset (Finset (Fin n))) {u : TS n KA KB → ℝ}
    (hu : IsGenSol θA θB ρ πA πB (rA F) u) {s : TS n KA KB} (hw : WF s.st.1) :
    (∫⁻ ω, occUpTo (holdA θA θB ρ F) ω ∂(argTrajT θA θB ρ πA πB h s))
      = ENNReal.ofReal (u s) := by
  have hcongr : ∀ ω : (_ : ℕ) → TS n KA KB,
      occ (holdA θA θB ρ F) ω = branchLen θA θB ρ F ω := by
    intro ω
    rw [occ_eq_occAll_killed, killed_holdA F, branchLen]
  rw [lintegral_congr_ae (occUpTo_ae_eq_occ h hθA hθB (holdA θA θB ρ F) hw),
    lintegral_congr hcongr]
  exact lintegral_branchLen_eq h hθA hθB F hu hw

theorem existsUnique_branchLen_potential (h : Adm θA θB ρ πA πB) (hθA : 0 < θA) (hθB : 0 < θB)
    (F : Finset (Finset (Fin n))) {s : TS n KA KB} (hw : WF s.st.1) :
    ∃! u : TS n KA KB → ℝ, IsGenSol θA θB ρ πA πB (rA F) u
      ∧ (∫⁻ ω, branchLen θA θB ρ F ω ∂(argTrajT θA θB ρ πA πB h s)) = ENNReal.ofReal (u s) := by
  obtain ⟨u, hu, huniq⟩ := existsUnique_genSol h hθA hθB (rA F)
  exact ⟨u, ⟨hu, lintegral_branchLen_eq h hθA hθB F hu hw⟩, fun v hv => huniq v hv.1⟩

end Rhone.Coalescent.BranchLengthMoments
