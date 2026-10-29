/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.Converse.Reduced

/-! # The low-mutation degeneration of the rank-one source and the sign law -/

@[expose] public section

namespace Rhone.Probability.Converse

open Filter Topology Finset LinearAlgebra.Recursion

section Lead

variable {d d' : ℕ} {f g : ℝ → ℝ} {c : ℝ}

def LeadCoeff (d : ℕ) (f : ℝ → ℝ) (c : ℝ) : Prop :=
  Tendsto (fun ε => f ε / ε ^ d) (𝓝[>] 0) (𝓝 c)

def LeadNonneg (d : ℕ) (f : ℝ → ℝ) : Prop := ∃ c, 0 ≤ (-1 : ℝ) ^ d * c ∧ LeadCoeff d f c

def LeadPos (d : ℕ) (f : ℝ → ℝ) : Prop := ∃ c, 0 < (-1 : ℝ) ^ d * c ∧ LeadCoeff d f c

theorem LeadPos.toNonneg (h : LeadPos d f) : LeadNonneg d f := by
  obtain ⟨c, hc, hlc⟩ := h
  exact ⟨c, hc.le, hlc⟩

theorem eventually_pos : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε :=
  eventually_mem_nhdsWithin

theorem LeadCoeff.congr' (h : LeadCoeff d f c) (he : ∀ᶠ ε in 𝓝[>] (0 : ℝ), f ε = g ε) :
    LeadCoeff d g c := by
  have ht : Tendsto (fun ε => f ε / ε ^ d) (𝓝[>] 0) (𝓝 c) := h
  refine Filter.Tendsto.congr' ?_ ht
  filter_upwards [he] with ε hε
  rw [hε]

theorem LeadNonneg.congr' (h : LeadNonneg d f) (he : ∀ᶠ ε in 𝓝[>] (0 : ℝ), f ε = g ε) :
    LeadNonneg d g := by
  obtain ⟨c, hc, hlc⟩ := h
  exact ⟨c, hc, hlc.congr' he⟩

theorem LeadPos.congr' (h : LeadPos d f) (he : ∀ᶠ ε in 𝓝[>] (0 : ℝ), f ε = g ε) :
    LeadPos d g := by
  obtain ⟨c, hc, hlc⟩ := h
  exact ⟨c, hc, hlc.congr' he⟩

theorem leadCoeff_zero (h : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 c)) : LeadCoeff 0 f c := by
  simpa [LeadCoeff] using h

theorem leadPos_of_tendsto (h : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 c)) (hc : 0 < c) : LeadPos 0 f :=
  ⟨c, by rw [pow_zero, one_mul]; exact hc, leadCoeff_zero h⟩

theorem leadNonneg_zero_fun (d : ℕ) : LeadNonneg d (fun _ => (0 : ℝ)) := by
  refine ⟨0, by simp, ?_⟩
  simp [LeadCoeff]

theorem LeadCoeff.add {c' : ℝ} (h : LeadCoeff d f c) (h' : LeadCoeff d g c') :
    LeadCoeff d (fun ε => f ε + g ε) (c + c') := by
  have ht : Tendsto (fun ε => f ε / ε ^ d) (𝓝[>] 0) (𝓝 c) := h
  have ht' : Tendsto (fun ε => g ε / ε ^ d) (𝓝[>] 0) (𝓝 c') := h'
  refine (ht.add ht').congr fun ε => ?_
  ring

theorem LeadNonneg.add (h : LeadNonneg d f) (h' : LeadNonneg d g) :
    LeadNonneg d (fun ε => f ε + g ε) := by
  obtain ⟨c, hc, hlc⟩ := h
  obtain ⟨c', hc', hlc'⟩ := h'
  refine ⟨c + c', ?_, hlc.add hlc'⟩
  have hsplit : (-1 : ℝ) ^ d * (c + c') = (-1 : ℝ) ^ d * c + (-1 : ℝ) ^ d * c' := by ring
  rw [hsplit]
  linarith

theorem LeadPos.add_nonneg (h : LeadPos d f) (h' : LeadNonneg d g) :
    LeadPos d (fun ε => f ε + g ε) := by
  obtain ⟨c, hc, hlc⟩ := h
  obtain ⟨c', hc', hlc'⟩ := h'
  refine ⟨c + c', ?_, hlc.add hlc'⟩
  have hsplit : (-1 : ℝ) ^ d * (c + c') = (-1 : ℝ) ^ d * c + (-1 : ℝ) ^ d * c' := by ring
  rw [hsplit]
  linarith

theorem LeadNonneg.add_pos (h : LeadNonneg d f) (h' : LeadPos d g) :
    LeadPos d (fun ε => f ε + g ε) := by
  refine (h'.add_nonneg h).congr' ?_
  filter_upwards with ε
  ring

theorem LeadNonneg.sum {ι : Type*} (s : Finset ι) (F : ι → ℝ → ℝ)
    (h : ∀ i ∈ s, LeadNonneg d (F i)) : LeadNonneg d (fun ε => ∑ i ∈ s, F i ε) := by
  classical
  revert h
  induction s using Finset.cons_induction with
  | empty =>
    intro _
    simpa using leadNonneg_zero_fun d
  | cons i s hi ih =>
    intro h
    have h1 : LeadNonneg d (F i) := h i (Finset.mem_cons_self i s)
    have h2 : LeadNonneg d (fun ε => ∑ k ∈ s, F k ε) :=
      ih fun k hk => h k (Finset.mem_cons_of_mem hk)
    refine (h1.add h2).congr' ?_
    filter_upwards with ε
    rw [Finset.sum_cons]

theorem LeadPos.sum_of_mem {ι : Type*} (s : Finset ι) (F : ι → ℝ → ℝ) {i₀ : ι} (hi₀ : i₀ ∈ s)
    (hpos : LeadPos d (F i₀)) (hrest : ∀ i ∈ s, LeadNonneg d (F i)) :
    LeadPos d (fun ε => ∑ i ∈ s, F i ε) := by
  classical
  refine (hpos.add_nonneg (LeadNonneg.sum (s.erase i₀) F fun i hi =>
    hrest i (Finset.mem_of_mem_erase hi))).congr' ?_
  filter_upwards with ε
  exact Finset.add_sum_erase s (fun i => F i ε) hi₀

theorem LeadCoeff.mul {d₁ d₂ : ℕ} {c₁ c₂ : ℝ} (h : LeadCoeff d₁ f c₁) (h' : LeadCoeff d₂ g c₂) :
    LeadCoeff (d₁ + d₂) (fun ε => f ε * g ε) (c₁ * c₂) := by
  have ht : Tendsto (fun ε => f ε / ε ^ d₁) (𝓝[>] 0) (𝓝 c₁) := h
  have ht' : Tendsto (fun ε => g ε / ε ^ d₂) (𝓝[>] 0) (𝓝 c₂) := h'
  refine (ht.mul ht').congr fun ε => ?_
  rw [pow_add, div_mul_div_comm]

theorem LeadNonneg.mul {d₁ d₂ : ℕ} (h : LeadNonneg d₁ f) (h' : LeadNonneg d₂ g) :
    LeadNonneg (d₁ + d₂) (fun ε => f ε * g ε) := by
  obtain ⟨c, hc, hlc⟩ := h
  obtain ⟨c', hc', hlc'⟩ := h'
  refine ⟨c * c', ?_, hlc.mul hlc'⟩
  have hsplit : (-1 : ℝ) ^ (d₁ + d₂) * (c * c')
      = ((-1 : ℝ) ^ d₁ * c) * ((-1 : ℝ) ^ d₂ * c') := by rw [pow_add]; ring
  rw [hsplit]
  exact mul_nonneg hc hc'

theorem LeadPos.mul {d₁ d₂ : ℕ} (h : LeadPos d₁ f) (h' : LeadPos d₂ g) :
    LeadPos (d₁ + d₂) (fun ε => f ε * g ε) := by
  obtain ⟨c, hc, hlc⟩ := h
  obtain ⟨c', hc', hlc'⟩ := h'
  refine ⟨c * c', ?_, hlc.mul hlc'⟩
  have hsplit : (-1 : ℝ) ^ (d₁ + d₂) * (c * c')
      = ((-1 : ℝ) ^ d₁ * c) * ((-1 : ℝ) ^ d₂ * c') := by rw [pow_add]; ring
  rw [hsplit]
  exact mul_pos hc hc'

theorem LeadNonneg.unit_mul {u : ℝ → ℝ} {cu : ℝ} (h : LeadNonneg d f)
    (hu : Tendsto u (𝓝[>] (0 : ℝ)) (𝓝 cu)) (hcu : 0 < cu) :
    LeadNonneg d (fun ε => u ε * f ε) := by
  obtain ⟨c, hc, hlc⟩ := h
  refine ⟨cu * c, ?_, ?_⟩
  · have hsplit : (-1 : ℝ) ^ d * (cu * c) = cu * ((-1 : ℝ) ^ d * c) := by ring
    rw [hsplit]
    exact mul_nonneg hcu.le hc
  · refine (hu.mul hlc).congr fun ε => ?_
    ring

theorem LeadPos.unit_mul {u : ℝ → ℝ} {cu : ℝ} (h : LeadPos d f)
    (hu : Tendsto u (𝓝[>] (0 : ℝ)) (𝓝 cu)) (hcu : 0 < cu) :
    LeadPos d (fun ε => u ε * f ε) := by
  obtain ⟨c, hc, hlc⟩ := h
  refine ⟨cu * c, ?_, ?_⟩
  · have hsplit : (-1 : ℝ) ^ d * (cu * c) = cu * ((-1 : ℝ) ^ d * c) := by ring
    rw [hsplit]
    exact mul_pos hcu hc
  · refine (hu.mul hlc).congr fun ε => ?_
    ring

theorem LeadNonneg.const_mul {k : ℝ} (h : LeadNonneg d f) (hk : 0 < k) :
    LeadNonneg d (fun ε => k * f ε) :=
  h.unit_mul (u := fun _ => k) tendsto_const_nhds hk

theorem LeadPos.const_mul {k : ℝ} (h : LeadPos d f) (hk : 0 < k) :
    LeadPos d (fun ε => k * f ε) :=
  h.unit_mul (u := fun _ => k) tendsto_const_nhds hk

theorem LeadCoeff.mono_zero (h : LeadCoeff d f c) (hlt : d' < d) : LeadCoeff d' f 0 := by
  obtain ⟨k, hk⟩ : ∃ k, d = d' + (k + 1) := ⟨d - d' - 1, by omega⟩
  have hpow : Tendsto (fun ε : ℝ => ε ^ (k + 1)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h0 : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have h1 := h0.pow (k + 1)
    rwa [zero_pow (by omega : k + 1 ≠ 0)] at h1
  have ht : Tendsto (fun ε => f ε / ε ^ d) (𝓝[>] 0) (𝓝 c) := h
  have hmul := hpow.mul ht
  rw [zero_mul] at hmul
  refine Filter.Tendsto.congr' ?_ hmul
  filter_upwards [eventually_pos] with ε hε
  have hne : (ε : ℝ) ≠ 0 := ne_of_gt hε
  rw [hk, pow_add]
  field_simp
  ring

theorem LeadNonneg.mono (h : LeadNonneg d f) (hle : d' ≤ d) : LeadNonneg d' f := by
  rcases eq_or_lt_of_le hle with rfl | hlt
  · exact h
  · obtain ⟨c, _, hlc⟩ := h
    exact ⟨0, by simp, hlc.mono_zero hlt⟩

theorem LeadPos.eventually_sign (h : LeadPos d f) :
    ∃ ε₀ > 0, ∀ ε ∈ Set.Ioo (0 : ℝ) ε₀, 0 < (-1 : ℝ) ^ d * f ε := by
  obtain ⟨c, hc, hlc⟩ := h
  have hmul : Tendsto (fun ε => (-1 : ℝ) ^ d * (f ε / ε ^ d)) (𝓝[>] (0 : ℝ))
      (𝓝 ((-1 : ℝ) ^ d * c)) := tendsto_const_nhds.mul hlc
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < (-1 : ℝ) ^ d * f ε := by
    filter_upwards [hmul.eventually (eventually_gt_nhds hc), eventually_pos] with ε h1 h2
    have hpow : (0 : ℝ) < ε ^ d := pow_pos h2 d
    have hx : (-1 : ℝ) ^ d * (f ε / ε ^ d) = ((-1 : ℝ) ^ d * f ε) / ε ^ d := by ring
    rw [hx] at h1
    have h3 := mul_pos h1 hpow
    rwa [div_mul_cancel₀ _ (ne_of_gt hpow)] at h3
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  exact ⟨u, hu, fun ε hε => hsub hε⟩

end Lead

section Gamma

variable {K : ℕ} {β : Fin K → ℝ}

theorem GcoefA_ray (β : Fin K → ℝ) (m : Fin K → ℕ) (i : Fin K) (ε : ℝ) :
    GcoefA (fun k => ε * β k) m i
      = ε * ((((∑ k, m k : ℕ) : ℝ) - 1) * β i - (((m i : ℕ) : ℝ) - 1) * ∑ k, β k)
        / (ε * β i + ((m i : ℕ) : ℝ) - 1) := by
  simp only [GcoefA, ← Finset.mul_sum]
  ring

theorem beta_lt_sum (hβ : ∀ k, 0 < β k) (hK : 2 ≤ K) (i : Fin K) : β i < ∑ k, β k := by
  have hcard : 1 < Fintype.card (Fin K) := by rw [Fintype.card_fin]; omega
  obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card hcard i
  exact Finset.single_lt_sum hj (Finset.mem_univ i) (Finset.mem_univ j) (hβ j)
    fun k _ _ => (hβ k).le

theorem eq_sum_of_mono {m : Fin K → ℕ} (hm : Mono m) {i : Fin K} (hi : m i ≠ 0) :
    m i = ∑ k, m k := by
  obtain ⟨l, hl⟩ := hm
  have hil : i = l := by
    by_contra hne
    exact hi (hl i hne)
  subst hil
  exact (Finset.sum_eq_single i (fun k _ hk => hl k hk)
    (fun h => absurd (Finset.mem_univ i) h)).symm

theorem lead_G (hβ : ∀ k, 0 < β k) (hK : 2 ≤ K) {m : Fin K → ℕ} (hn : 2 ≤ ∑ k, m k)
    {i : Fin K} (hi : m i ≠ 0) :
    LeadNonneg (mu m) (fun ε => GcoefA (fun k => ε * β k) m i) := by
  have hn2 : (2 : ℝ) ≤ ((∑ k, m k : ℕ) : ℝ) := by exact_mod_cast hn
  by_cases h1 : m i = 1
  · have hnm : ¬ Mono m := fun hm => by
      have hs := eq_sum_of_mono hm hi
      omega
    rw [mu_of_not_mono hnm]
    refine ⟨((∑ k, m k : ℕ) : ℝ) - 1, by rw [pow_zero, one_mul]; linarith, ?_⟩
    refine LeadCoeff.congr' (leadCoeff_zero (f := fun _ : ℝ => ((∑ k, m k : ℕ) : ℝ) - 1)
      tendsto_const_nhds) ?_
    filter_upwards [eventually_pos] with ε hε
    exact (GcoefA_of_mi_one (α := fun k => ε * β k) h1 (ne_of_gt (mul_pos hε (hβ i)))).symm
  · have h2 : 2 ≤ m i := by omega
    have hmi2 : (2 : ℝ) ≤ ((m i : ℕ) : ℝ) := by exact_mod_cast h2
    have hden : ((m i : ℕ) : ℝ) - 1 ≠ 0 := by linarith
    have hlim : Tendsto (fun ε : ℝ =>
        ((((∑ k, m k : ℕ) : ℝ) - 1) * β i - (((m i : ℕ) : ℝ) - 1) * ∑ k, β k)
          / (ε * β i + ((m i : ℕ) : ℝ) - 1)) (𝓝[>] (0 : ℝ))
        (𝓝 (((((∑ k, m k : ℕ) : ℝ) - 1) * β i - (((m i : ℕ) : ℝ) - 1) * ∑ k, β k)
          / (((m i : ℕ) : ℝ) - 1))) := by
      have hd : Tendsto (fun ε : ℝ => ε * β i + ((m i : ℕ) : ℝ) - 1) (𝓝 (0 : ℝ))
          (𝓝 (((m i : ℕ) : ℝ) - 1)) := by
        have hcont : Continuous (fun ε : ℝ => ε * β i + ((m i : ℕ) : ℝ) - 1) := by fun_prop
        simpa using hcont.tendsto 0
      exact (tendsto_const_nhds.div hd hden).mono_left nhdsWithin_le_nhds
    have hlc : LeadCoeff 1 (fun ε => GcoefA (fun k => ε * β k) m i)
        (((((∑ k, m k : ℕ) : ℝ) - 1) * β i - (((m i : ℕ) : ℝ) - 1) * ∑ k, β k)
          / (((m i : ℕ) : ℝ) - 1)) := by
      refine Tendsto.congr' ?_ hlim
      filter_upwards [eventually_pos] with ε hε
      have hne : (ε : ℝ) ≠ 0 := ne_of_gt hε
      have hD : ε * β i + ((m i : ℕ) : ℝ) - 1 ≠ 0 := by
        have := mul_pos hε (hβ i)
        linarith
      rw [GcoefA_ray, pow_one]
      field_simp
    by_cases hm : Mono m
    · have hmi : m i = ∑ k, m k := eq_sum_of_mono hm hi
      have hcast : ((m i : ℕ) : ℝ) = ((∑ k, m k : ℕ) : ℝ) := by rw [hmi]
      have hd1 : ((∑ k, m k : ℕ) : ℝ) - 1 ≠ 0 := by linarith
      have hval : ((((∑ k, m k : ℕ) : ℝ) - 1) * β i - (((m i : ℕ) : ℝ) - 1) * ∑ k, β k)
          / (((m i : ℕ) : ℝ) - 1) = β i - ∑ k, β k := by
        rw [hcast]
        field_simp
      rw [mu_of_mono hm]
      refine ⟨((((∑ k, m k : ℕ) : ℝ) - 1) * β i - (((m i : ℕ) : ℝ) - 1) * ∑ k, β k)
        / (((m i : ℕ) : ℝ) - 1), ?_, hlc⟩
      rw [hval, pow_one]
      have hlt := beta_lt_sum hβ hK i
      linarith
    · rw [mu_of_not_mono hm]
      exact ⟨0, by simp, hlc.mono_zero (by omega)⟩

end Gamma

section PhiRay

variable {K : ℕ} {β : Fin K → ℝ}

theorem PhiA_ray_alt (hβ : ∀ k, 0 < β k) (m : Fin K → ℕ) {ε : ℝ} (hε : 0 < ε) :
    PhiA (fun k => ε * β k) m
      = ((∑ k, m k : ℕ) : ℝ) * (((∑ k, m k : ℕ) : ℝ) - 1)
        - (((∑ k, m k : ℕ) : ℝ) - 1 + ε * ∑ k, β k)
          * ∑ i, ((m i : ℕ) : ℝ) * (((m i : ℕ) : ℝ) - 1)
              / (ε * β i + ((m i : ℕ) : ℝ) - 1) := by
  have hd : ∀ i, m i ≠ 0 → (fun k => ε * β k) i + ((m i : ℕ) : ℝ) - 1 ≠ 0 := by
    intro i hi
    have h1 : (1 : ℝ) ≤ ((m i : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hi
    have h2 : (0 : ℝ) < ε * β i := mul_pos hε (hβ i)
    simp only
    linarith
  rw [PhiA_eq_alt _ m hd, uu, ← Finset.mul_sum]

theorem tendsto_alt_term (β : Fin K → ℝ) (m : Fin K → ℕ) (i : Fin K) :
    Tendsto (fun ε : ℝ => ((m i : ℕ) : ℝ) * (((m i : ℕ) : ℝ) - 1)
        / (ε * β i + ((m i : ℕ) : ℝ) - 1)) (𝓝 (0 : ℝ))
      (𝓝 (if 2 ≤ m i then ((m i : ℕ) : ℝ) else 0)) := by
  by_cases h2 : 2 ≤ m i
  · have hmi2 : (2 : ℝ) ≤ ((m i : ℕ) : ℝ) := by exact_mod_cast h2
    have hden : ((m i : ℕ) : ℝ) - 1 ≠ 0 := by linarith
    have hd : Tendsto (fun ε : ℝ => ε * β i + ((m i : ℕ) : ℝ) - 1) (𝓝 (0 : ℝ))
        (𝓝 (((m i : ℕ) : ℝ) - 1)) := by
      have hcont : Continuous (fun ε : ℝ => ε * β i + ((m i : ℕ) : ℝ) - 1) := by fun_prop
      simpa using hcont.tendsto 0
    have hval : ((m i : ℕ) : ℝ) * (((m i : ℕ) : ℝ) - 1) / (((m i : ℕ) : ℝ) - 1)
        = ((m i : ℕ) : ℝ) := by field_simp
    have hlim : Tendsto (fun ε : ℝ => ((m i : ℕ) : ℝ) * (((m i : ℕ) : ℝ) - 1)
        / (ε * β i + ((m i : ℕ) : ℝ) - 1)) (𝓝 (0 : ℝ))
        (𝓝 (((m i : ℕ) : ℝ) * (((m i : ℕ) : ℝ) - 1) / (((m i : ℕ) : ℝ) - 1))) :=
      tendsto_const_nhds.div hd hden
    rw [ite_eq_left h2]
    rwa [hval] at hlim
  · have hz : m i = 0 ∨ m i = 1 := by omega
    have hnum : ((m i : ℕ) : ℝ) * (((m i : ℕ) : ℝ) - 1) = 0 := by
      rcases hz with h | h <;> rw [h] <;> norm_num
    rw [ite_eq_right h2]
    simp only [hnum, zero_div]
    exact tendsto_const_nhds

theorem sum_ge_two_eq (m : Fin K → ℕ) :
    (∑ i, if 2 ≤ m i then ((m i : ℕ) : ℝ) else 0)
      = ((∑ k, m k : ℕ) : ℝ) - ((sing m : ℕ) : ℝ) := by
  have hterm : ∀ i : Fin K, (if 2 ≤ m i then ((m i : ℕ) : ℝ) else 0)
      = ((m i : ℕ) : ℝ) - (if m i = 1 then (1 : ℝ) else 0) := by
    intro i
    by_cases h : 2 ≤ m i
    · rw [ite_eq_left h, ite_eq_right (by omega : ¬ m i = 1)]
      ring
    · have hz : m i = 0 ∨ m i = 1 := by omega
      rcases hz with h0 | h0 <;> rw [ite_eq_right h, h0] <;> norm_num
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_sub_distrib, ← Nat.cast_sum,
    Finset.sum_boole]
  rfl

theorem tendsto_Phi_zero (hβ : ∀ k, 0 < β k) (m : Fin K → ℕ) :
    Tendsto (fun ε => PhiA (fun k => ε * β k) m) (𝓝[>] (0 : ℝ))
      (𝓝 ((((∑ k, m k : ℕ) : ℝ) - 1) * ((sing m : ℕ) : ℝ))) := by
  have hsum : Tendsto (fun ε : ℝ => ∑ i, ((m i : ℕ) : ℝ) * (((m i : ℕ) : ℝ) - 1)
      / (ε * β i + ((m i : ℕ) : ℝ) - 1)) (𝓝 (0 : ℝ))
      (𝓝 (∑ i, if 2 ≤ m i then ((m i : ℕ) : ℝ) else 0)) :=
    tendsto_finsetSum _ fun i _ => tendsto_alt_term β m i
  have hfac : Tendsto (fun ε : ℝ => ((∑ k, m k : ℕ) : ℝ) - 1 + ε * ∑ k, β k) (𝓝 (0 : ℝ))
      (𝓝 (((∑ k, m k : ℕ) : ℝ) - 1)) := by
    have hcont : Continuous (fun ε : ℝ => ((∑ k, m k : ℕ) : ℝ) - 1 + ε * ∑ k, β k) := by fun_prop
    simpa using hcont.tendsto 0
  have halt := (tendsto_const_nhds
    (x := ((∑ k, m k : ℕ) : ℝ) * (((∑ k, m k : ℕ) : ℝ) - 1))).sub (hfac.mul hsum)
  rw [sum_ge_two_eq m] at halt
  have hval : ((∑ k, m k : ℕ) : ℝ) * (((∑ k, m k : ℕ) : ℝ) - 1)
      - (((∑ k, m k : ℕ) : ℝ) - 1) * (((∑ k, m k : ℕ) : ℝ) - ((sing m : ℕ) : ℝ))
      = (((∑ k, m k : ℕ) : ℝ) - 1) * ((sing m : ℕ) : ℝ) := by ring
  rw [hval] at halt
  refine (halt.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [eventually_pos] with ε hε
  exact (PhiA_ray_alt hβ m hε).symm

theorem lead_Phi_mono (hβ : ∀ k, 0 < β k) (hK : 2 ≤ K) {m : Fin K → ℕ} (hm : Mono m)
    (hn : 2 ≤ ∑ k, m k) : LeadPos 1 (fun ε => PhiA (fun k => ε * β k) m) := by
  obtain ⟨i₁, hl⟩ := hm
  have hmi : m i₁ = ∑ k, m k :=
    (Finset.sum_eq_single i₁ (fun k _ hk => hl k hk)
      (fun h => absurd (Finset.mem_univ i₁) h)).symm
  have hn2 : (2 : ℝ) ≤ ((∑ k, m k : ℕ) : ℝ) := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < ((∑ k, m k : ℕ) : ℝ) - 1 := by linarith
  have hlim : Tendsto (fun ε : ℝ => ((∑ k, m k : ℕ) : ℝ) * (((∑ k, m k : ℕ) : ℝ) - 1)
      * (β i₁ - ∑ k, β k) / (ε * β i₁ + ((∑ k, m k : ℕ) : ℝ) - 1)) (𝓝 (0 : ℝ))
      (𝓝 (((∑ k, m k : ℕ) : ℝ) * (((∑ k, m k : ℕ) : ℝ) - 1) * (β i₁ - ∑ k, β k)
        / (((∑ k, m k : ℕ) : ℝ) - 1))) := by
    have hd : Tendsto (fun ε : ℝ => ε * β i₁ + ((∑ k, m k : ℕ) : ℝ) - 1) (𝓝 (0 : ℝ))
        (𝓝 (((∑ k, m k : ℕ) : ℝ) - 1)) := by
      have hcont : Continuous (fun ε : ℝ => ε * β i₁ + ((∑ k, m k : ℕ) : ℝ) - 1) := by fun_prop
      simpa using hcont.tendsto 0
    exact tendsto_const_nhds.div hd (ne_of_gt hn1)
  refine ⟨((∑ k, m k : ℕ) : ℝ) * (((∑ k, m k : ℕ) : ℝ) - 1) * (β i₁ - ∑ k, β k)
    / (((∑ k, m k : ℕ) : ℝ) - 1), ?_, ?_⟩
  · have hlt := beta_lt_sum hβ hK i₁
    have hnpos : (0 : ℝ) < ((∑ k, m k : ℕ) : ℝ) := by linarith
    rw [pow_one, show (-1 : ℝ) * (((∑ k, m k : ℕ) : ℝ) * (((∑ k, m k : ℕ) : ℝ) - 1)
        * (β i₁ - ∑ k, β k) / (((∑ k, m k : ℕ) : ℝ) - 1))
      = ((∑ k, m k : ℕ) : ℝ) * (((∑ k, m k : ℕ) : ℝ) - 1) * ((∑ k, β k) - β i₁)
        / (((∑ k, m k : ℕ) : ℝ) - 1) by ring]
    exact div_pos (mul_pos (mul_pos hnpos hn1) (by linarith)) hn1
  · refine Tendsto.congr' ?_ (hlim.mono_left nhdsWithin_le_nhds)
    filter_upwards [eventually_pos] with ε hε
    have hne : (ε : ℝ) ≠ 0 := ne_of_gt hε
    have hDpos : (0 : ℝ) < ε * β i₁ + ((∑ k, m k : ℕ) : ℝ) - 1 := by
      have := mul_pos hε (hβ i₁)
      linarith
    have hDne : ε * β i₁ + ((∑ k, m k : ℕ) : ℝ) - 1 ≠ 0 := ne_of_gt hDpos
    have hDne2 : -1 + β i₁ * ε + ((∑ k, m k : ℕ) : ℝ) ≠ 0 := fun h => hDne (by linarith)
    have hsingle : (∑ i, ((m i : ℕ) : ℝ) * (((m i : ℕ) : ℝ) - 1)
        / (ε * β i + ((m i : ℕ) : ℝ) - 1))
        = ((∑ k, m k : ℕ) : ℝ) * (((∑ k, m k : ℕ) : ℝ) - 1)
          / (ε * β i₁ + ((∑ k, m k : ℕ) : ℝ) - 1) := by
      rw [Finset.sum_eq_single i₁ (fun k _ hk => by rw [hl k hk]; norm_num)
        (fun h => absurd (Finset.mem_univ i₁) h), hmi]
    have hdiv : ((∑ k, m k : ℕ) : ℝ) * (((∑ k, m k : ℕ) : ℝ) - 1)
        / (ε * β i₁ + ((∑ k, m k : ℕ) : ℝ) - 1) * (ε * β i₁ + ((∑ k, m k : ℕ) : ℝ) - 1)
        = ((∑ k, m k : ℕ) : ℝ) * (((∑ k, m k : ℕ) : ℝ) - 1) := by
      field_simp
    have hmul : PhiA (fun k => ε * β k) m * (ε * β i₁ + ((∑ k, m k : ℕ) : ℝ) - 1)
        = ε * (((∑ k, m k : ℕ) : ℝ) * (((∑ k, m k : ℕ) : ℝ) - 1) * (β i₁ - ∑ k, β k)) := by
      rw [PhiA_ray_alt hβ m hε, hsingle]
      linear_combination (-(((∑ k, m k : ℕ) : ℝ) - 1 + ε * ∑ k, β k)) * hdiv
    rw [pow_one, div_eq_div_iff hDne hne]
    linear_combination -hmul

theorem lead_Phi (hβ : ∀ k, 0 < β k) (hK : 2 ≤ K) {m : Fin K → ℕ} (hn : 2 ≤ ∑ k, m k) :
    LeadNonneg (mu m) (fun ε => PhiA (fun k => ε * β k) m) := by
  by_cases hm : Mono m
  · rw [mu_of_mono hm]
    exact (lead_Phi_mono hβ hK hm hn).toNonneg
  · rw [mu_of_not_mono hm]
    refine ⟨(((∑ k, m k : ℕ) : ℝ) - 1) * ((sing m : ℕ) : ℝ), ?_,
      leadCoeff_zero (tendsto_Phi_zero hβ m)⟩
    have h1 : (0 : ℝ) ≤ ((∑ k, m k : ℕ) : ℝ) - 1 := by
      have h2 : (2 : ℝ) ≤ ((∑ k, m k : ℕ) : ℝ) := by exact_mod_cast hn
      linarith
    rw [pow_zero, one_mul]
    exact mul_nonneg h1 (Nat.cast_nonneg _)

theorem lead_Phi_two (hβ : ∀ k, 0 < β k) (hK : 2 ≤ K) {m : Fin K → ℕ} (hn : (∑ k, m k) = 2) :
    LeadPos (mu m) (fun ε => PhiA (fun k => ε * β k) m) := by
  by_cases hm : Mono m
  · rw [mu_of_mono hm]
    exact lead_Phi_mono hβ hK hm (by omega)
  · rw [mu_of_not_mono hm]
    have hKpos : 0 < K := by omega
    obtain ⟨i, j, hij, hi, hj⟩ := exists_pair_of_not_mono hKpos hm
    have hpair := Rhone.LinearAlgebra.Recursion.pair_le_sum m hij
    rw [hn] at hpair
    have hi1 : m i = 1 := by omega
    have hmem : i ∈ Finset.univ.filter fun k => m k = 1 := by simp [hi1]
    have hsing : 1 ≤ sing m := Finset.card_pos.2 ⟨i, hmem⟩
    refine ⟨(((∑ k, m k : ℕ) : ℝ) - 1) * ((sing m : ℕ) : ℝ), ?_,
      leadCoeff_zero (tendsto_Phi_zero hβ m)⟩
    have h1 : ((∑ k, m k : ℕ) : ℝ) - 1 = 1 := by rw [hn]; norm_num
    have h2 : (1 : ℝ) ≤ ((sing m : ℕ) : ℝ) := by exact_mod_cast hsing
    rw [pow_zero, one_mul, h1, one_mul]
    linarith

end PhiRay

theorem exists_drop_preserving_mono {K : ℕ} (a : Fin K → ℕ) (h : 3 ≤ ∑ i, a i) :
    ∃ i, a i ≠ 0 ∧ mu (decf a i) = mu a := by
  have hK : 0 < K := by
    rcases Nat.eq_zero_or_pos K with hk | hk
    · subst hk
      simp at h
    · exact hk
  by_cases hm : Mono a
  · obtain ⟨l, hl⟩ := id hm
    have hal : a l = ∑ i, a i :=
      (Finset.sum_eq_single l (fun k _ hk => hl k hk)
        (fun hh => absurd (Finset.mem_univ l) hh)).symm
    refine ⟨l, by omega, ?_⟩
    rw [mu_of_mono hm, mu_of_mono ⟨l, fun k hk => by rw [decf_of_ne _ hk, hl k hk]⟩]
  · obtain ⟨i, j, hij, hi, hj⟩ := exists_pair_of_not_mono hK hm
    rw [mu_of_not_mono hm]
    by_cases h2i : 2 ≤ a i
    · refine ⟨i, hi, mu_of_not_mono (not_mono_of_pair hij ?_ ?_)⟩
      · rw [decf_self]; omega
      · rw [decf_of_ne _ (Ne.symm hij)]; exact hj
    · by_cases h2j : 2 ≤ a j
      · refine ⟨j, hj, mu_of_not_mono (not_mono_of_pair (Ne.symm hij) ?_ ?_)⟩
        · rw [decf_self]; omega
        · rw [decf_of_ne _ hij]; exact hi
      · have hai : a i = 1 := by omega
        have haj : a j = 1 := by omega
        have hex : ∃ l, l ≠ i ∧ l ≠ j ∧ a l ≠ 0 := by
          by_contra hc
          push Not at hc
          have hsub : (∑ k ∈ ({i, j} : Finset (Fin K)), a k) = ∑ k, a k := by
            refine Finset.sum_subset (Finset.subset_univ _) ?_
            intro x _ hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            push Not at hx
            exact hc x hx.1 hx.2
          rw [Finset.sum_pair hij] at hsub
          omega
        obtain ⟨l, hli, hlj, hl0⟩ := hex
        refine ⟨i, hi, mu_of_not_mono (not_mono_of_pair (fun hh => hlj hh.symm) ?_ ?_)⟩
        · rw [decf_of_ne _ (Ne.symm hij)]; exact hj
        · rw [decf_of_ne _ hli]; exact hl0

section Induction

variable {KA KB : ℕ} {βA : Fin KA → ℝ} {βB : Fin KB → ℝ}

structure RayRec (βA : Fin KA → ℝ) (βB : Fin KB → ℝ)
    (g : ℝ → (Fin KA → ℕ) → (Fin KB → ℕ) → ℝ) : Prop where
  bdryA : ∀ ε a b, (∑ i, a i) ≤ 1 → g ε a b = 0
  bdryB : ∀ ε a b, (∑ j, b j) ≤ 1 → g ε a b = 0
  step : ∀ ε : ℝ, 0 < ε → ∀ (a : Fin KA → ℕ) (b : Fin KB → ℕ),
    2 ≤ (∑ i, a i) → 2 ≤ (∑ j, b j) →
    (((∑ i, a i : ℕ) : ℝ) * uu (ε * ∑ k, βA k) (∑ i, a i)
        + ((∑ j, b j : ℕ) : ℝ) * uu (ε * ∑ k, βB k) (∑ j, b j)) * g ε a b
      = uu (ε * ∑ k, βA k) (∑ i, a i) * ∑ i, ((a i : ℕ) : ℝ) * g ε (decf a i) b
        + uu (ε * ∑ k, βB k) (∑ j, b j) * ∑ j, ((b j : ℕ) : ℝ) * g ε a (decf b j)
        + 4 * PhiA (fun k => ε * βA k) a * PhiA (fun k => ε * βB k) b

theorem ord_sign_g (hβA : ∀ k, 0 < βA k) (hKA : 2 ≤ KA) (hβB : ∀ k, 0 < βB k) (hKB : 2 ≤ KB)
    {g : ℝ → (Fin KA → ℕ) → (Fin KB → ℕ) → ℝ} (hg : RayRec βA βB g) :
    ∀ N : ℕ, ∀ (a : Fin KA → ℕ) (b : Fin KB → ℕ),
      (∑ i, a i) + (∑ j, b j) ≤ N → 2 ≤ (∑ i, a i) → 2 ≤ (∑ j, b j) →
      LeadPos (mu a + mu b) (fun ε => g ε a b) := by
  have hnA : Nonempty (Fin KA) := ⟨⟨0, by omega⟩⟩
  have hnB : Nonempty (Fin KB) := ⟨⟨0, by omega⟩⟩
  have hθA : (0 : ℝ) < ∑ k, βA k :=
    Finset.sum_pos (fun k _ => hβA k) Finset.univ_nonempty
  have hθB : (0 : ℝ) < ∑ k, βB k :=
    Finset.sum_pos (fun k _ => hβB k) Finset.univ_nonempty
  intro N
  induction N with
  | zero =>
    intro a b hN ha _
    omega
  | succ N ih =>
    intro a b hN ha hb
    have hna : (2 : ℝ) ≤ ((∑ i, a i : ℕ) : ℝ) := by exact_mod_cast ha
    have hnb : (2 : ℝ) ≤ ((∑ j, b j : ℕ) : ℝ) := by exact_mod_cast hb
    have htA : Tendsto (fun ε : ℝ => uu (ε * ∑ k, βA k) (∑ i, a i)) (𝓝[>] (0 : ℝ))
        (𝓝 (((∑ i, a i : ℕ) : ℝ) - 1)) := by
      have hcont : Continuous
          (fun ε : ℝ => ((∑ i, a i : ℕ) : ℝ) - 1 + ε * ∑ k, βA k) := by fun_prop
      have h0 := hcont.tendsto 0
      simp only [zero_mul, add_zero] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    have htB : Tendsto (fun ε : ℝ => uu (ε * ∑ k, βB k) (∑ j, b j)) (𝓝[>] (0 : ℝ))
        (𝓝 (((∑ j, b j : ℕ) : ℝ) - 1)) := by
      have hcont : Continuous
          (fun ε : ℝ => ((∑ j, b j : ℕ) : ℝ) - 1 + ε * ∑ k, βB k) := by fun_prop
      have h0 := hcont.tendsto 0
      simp only [zero_mul, add_zero] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    have hM0 : (0 : ℝ) < ((∑ i, a i : ℕ) : ℝ) * (((∑ i, a i : ℕ) : ℝ) - 1)
        + ((∑ j, b j : ℕ) : ℝ) * (((∑ j, b j : ℕ) : ℝ) - 1) := by nlinarith
    have htM : Tendsto (fun ε : ℝ => ((∑ i, a i : ℕ) : ℝ) * uu (ε * ∑ k, βA k) (∑ i, a i)
        + ((∑ j, b j : ℕ) : ℝ) * uu (ε * ∑ k, βB k) (∑ j, b j)) (𝓝[>] (0 : ℝ))
        (𝓝 (((∑ i, a i : ℕ) : ℝ) * (((∑ i, a i : ℕ) : ℝ) - 1)
          + ((∑ j, b j : ℕ) : ℝ) * (((∑ j, b j : ℕ) : ℝ) - 1))) :=
      (tendsto_const_nhds.mul htA).add (tendsto_const_nhds.mul htB)
    have hMpos : ∀ ε : ℝ, 0 < ε →
        (0 : ℝ) < ((∑ i, a i : ℕ) : ℝ) * uu (ε * ∑ k, βA k) (∑ i, a i)
          + ((∑ j, b j : ℕ) : ℝ) * uu (ε * ∑ k, βB k) (∑ j, b j) := by
      intro ε hε
      have h1 : (0 : ℝ) < uu (ε * ∑ k, βA k) (∑ i, a i) := by
        have := mul_pos hε hθA
        simp only [uu]
        linarith
      have h2 : (0 : ℝ) < uu (ε * ∑ k, βB k) (∑ j, b j) := by
        have := mul_pos hε hθB
        simp only [uu]
        linarith
      nlinarith
    have hAterm : ∀ i : Fin KA, LeadNonneg (mu a + mu b)
        (fun ε => ((a i : ℕ) : ℝ) * g ε (decf a i) b) := by
      intro i
      by_cases h0 : a i = 0
      · refine (leadNonneg_zero_fun (mu a + mu b)).congr' ?_
        filter_upwards with ε
        rw [h0]
        norm_num
      · have hda := Rhone.LinearAlgebra.Recursion.sum_decf (f := a) (i := i) h0
        by_cases hsmall : (∑ k, decf a i k) ≤ 1
        · refine (leadNonneg_zero_fun (mu a + mu b)).congr' ?_
          filter_upwards with ε
          rw [hg.bdryA ε (decf a i) b hsmall]
          norm_num
        · have h2 : 2 ≤ (∑ k, decf a i k) := by omega
          have hIH := ih (decf a i) b (by omega) h2 hb
          have hmono : mu a + mu b ≤ mu (decf a i) + mu b :=
            Nat.add_le_add_right (mu_le_mu_decf h0) _
          have hposc : (0 : ℝ) < ((a i : ℕ) : ℝ) := by
            have : 0 < a i := Nat.pos_of_ne_zero h0
            exact_mod_cast this
          exact (hIH.toNonneg.mono hmono).const_mul hposc
    have hBterm : ∀ j : Fin KB, LeadNonneg (mu a + mu b)
        (fun ε => ((b j : ℕ) : ℝ) * g ε a (decf b j)) := by
      intro j
      by_cases h0 : b j = 0
      · refine (leadNonneg_zero_fun (mu a + mu b)).congr' ?_
        filter_upwards with ε
        rw [h0]
        norm_num
      · have hdb := Rhone.LinearAlgebra.Recursion.sum_decf (f := b) (i := j) h0
        by_cases hsmall : (∑ k, decf b j k) ≤ 1
        · refine (leadNonneg_zero_fun (mu a + mu b)).congr' ?_
          filter_upwards with ε
          rw [hg.bdryB ε a (decf b j) hsmall]
          norm_num
        · have h2 : 2 ≤ (∑ k, decf b j k) := by omega
          have hIH := ih a (decf b j) (by omega) ha h2
          have hmono : mu a + mu b ≤ mu a + mu (decf b j) :=
            Nat.add_le_add_left (mu_le_mu_decf h0) _
          have hposc : (0 : ℝ) < ((b j : ℕ) : ℝ) := by
            have : 0 < b j := Nat.pos_of_ne_zero h0
            exact_mod_cast this
          exact (hIH.toNonneg.mono hmono).const_mul hposc
    have hSA : LeadNonneg (mu a + mu b)
        (fun ε => ∑ i, ((a i : ℕ) : ℝ) * g ε (decf a i) b) :=
      LeadNonneg.sum Finset.univ (fun i ε => ((a i : ℕ) : ℝ) * g ε (decf a i) b)
        fun i _ => hAterm i
    have hSB : LeadNonneg (mu a + mu b)
        (fun ε => ∑ j, ((b j : ℕ) : ℝ) * g ε a (decf b j)) :=
      LeadNonneg.sum Finset.univ (fun j ε => ((b j : ℕ) : ℝ) * g ε a (decf b j))
        fun j _ => hBterm j
    have hSAu : LeadNonneg (mu a + mu b) (fun ε => uu (ε * ∑ k, βA k) (∑ i, a i)
        * ∑ i, ((a i : ℕ) : ℝ) * g ε (decf a i) b) :=
      hSA.unit_mul htA (by linarith)
    have hSBu : LeadNonneg (mu a + mu b) (fun ε => uu (ε * ∑ k, βB k) (∑ j, b j)
        * ∑ j, ((b j : ℕ) : ℝ) * g ε a (decf b j)) :=
      hSB.unit_mul htB (by linarith)
    have hSrc : LeadNonneg (mu a + mu b) (fun ε =>
        4 * PhiA (fun k => ε * βA k) a * PhiA (fun k => ε * βB k) b) := by
      refine (((lead_Phi hβA hKA ha).mul (lead_Phi hβB hKB hb)).const_mul
        (by norm_num : (0 : ℝ) < 4)).congr' ?_
      filter_upwards with ε
      ring
    have hRHS : LeadPos (mu a + mu b) (fun ε =>
        uu (ε * ∑ k, βA k) (∑ i, a i) * ∑ i, ((a i : ℕ) : ℝ) * g ε (decf a i) b
          + uu (ε * ∑ k, βB k) (∑ j, b j) * ∑ j, ((b j : ℕ) : ℝ) * g ε a (decf b j)
          + 4 * PhiA (fun k => ε * βA k) a * PhiA (fun k => ε * βB k) b) := by
      rcases Nat.lt_or_ge (∑ i, a i) 3 with hsa | h3a
      · rcases Nat.lt_or_ge (∑ j, b j) 3 with hsb | h3b
        · have hSrcPos : LeadPos (mu a + mu b) (fun ε =>
              4 * PhiA (fun k => ε * βA k) a * PhiA (fun k => ε * βB k) b) := by
            refine (((lead_Phi_two hβA hKA (by omega)).mul
              (lead_Phi_two hβB hKB (by omega))).const_mul
              (by norm_num : (0 : ℝ) < 4)).congr' ?_
            filter_upwards with ε
            ring
          exact (hSAu.add hSBu).add_pos hSrcPos
        · obtain ⟨j₀, hj₀, hmu₀⟩ := exists_drop_preserving_mono b h3b
          have hdb := Rhone.LinearAlgebra.Recursion.sum_decf (f := b) (i := j₀) hj₀
          have h2' : 2 ≤ (∑ k, decf b j₀ k) := by omega
          have hIH := ih a (decf b j₀) (by omega) ha h2'
          have hposc : (0 : ℝ) < ((b j₀ : ℕ) : ℝ) := by
            have : 0 < b j₀ := Nat.pos_of_ne_zero hj₀
            exact_mod_cast this
          have hTermPos : LeadPos (mu a + mu b)
              (fun ε => ((b j₀ : ℕ) : ℝ) * g ε a (decf b j₀)) := by
            rw [← hmu₀]
            exact hIH.const_mul hposc
          have hSBpos : LeadPos (mu a + mu b)
              (fun ε => ∑ j, ((b j : ℕ) : ℝ) * g ε a (decf b j)) :=
            LeadPos.sum_of_mem Finset.univ (fun j ε => ((b j : ℕ) : ℝ) * g ε a (decf b j))
              (Finset.mem_univ j₀) hTermPos fun j _ => hBterm j
          exact (hSAu.add_pos (hSBpos.unit_mul htB (by linarith))).add_nonneg hSrc
      · obtain ⟨i₀, hi₀, hmu₀⟩ := exists_drop_preserving_mono a h3a
        have hda := Rhone.LinearAlgebra.Recursion.sum_decf (f := a) (i := i₀) hi₀
        have h2' : 2 ≤ (∑ k, decf a i₀ k) := by omega
        have hIH := ih (decf a i₀) b (by omega) h2' hb
        have hposc : (0 : ℝ) < ((a i₀ : ℕ) : ℝ) := by
          have : 0 < a i₀ := Nat.pos_of_ne_zero hi₀
          exact_mod_cast this
        have hTermPos : LeadPos (mu a + mu b)
            (fun ε => ((a i₀ : ℕ) : ℝ) * g ε (decf a i₀) b) := by
          rw [← hmu₀]
          exact hIH.const_mul hposc
        have hSApos : LeadPos (mu a + mu b)
            (fun ε => ∑ i, ((a i : ℕ) : ℝ) * g ε (decf a i) b) :=
          LeadPos.sum_of_mem Finset.univ (fun i ε => ((a i : ℕ) : ℝ) * g ε (decf a i) b)
            (Finset.mem_univ i₀) hTermPos fun i _ => hAterm i
        exact ((hSApos.unit_mul htA (by linarith)).add_nonneg hSBu).add_nonneg hSrc
    have hfinal := (leadPos_of_tendsto htM hM0).mul hRHS
    have hinv : LeadPos 0 (fun ε : ℝ => (((∑ i, a i : ℕ) : ℝ) * uu (ε * ∑ k, βA k) (∑ i, a i)
        + ((∑ j, b j : ℕ) : ℝ) * uu (ε * ∑ k, βB k) (∑ j, b j))⁻¹) :=
      leadPos_of_tendsto (htM.inv₀ (ne_of_gt hM0)) (inv_pos.2 hM0)
    have hres := hinv.mul hRHS
    rw [zero_add] at hres
    refine hres.congr' ?_
    filter_upwards [eventually_pos] with ε hε
    have hstep := hg.step ε hε a b ha hb
    have hMne := ne_of_gt (hMpos ε hε)
    rw [← hstep, ← mul_assoc, inv_mul_cancel₀ hMne, one_mul]

end Induction

end Rhone.Probability.Converse
