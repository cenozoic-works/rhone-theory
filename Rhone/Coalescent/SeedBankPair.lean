/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SeedBank
public import Rhone.Coalescent.Kingman
public import Rhone.MarkovChain.ClosedHitting
public import Rhone.MarkovChain.RateReach

/-!
# The seed-bank coalescent: time to the most recent common ancestor of two lineages

Source: blath_etal2015, p. 927, eq. (11)–(12). -/

@[expose] public section

namespace Rhone.Coalescent.SeedBank

open Finset MeasureTheory Filter Topology MarkovChain
open scoped ENNReal

section Closed

variable {S : Type*} [Fintype S] [DecidableEq S] {R : RateChain S} {A : Finset S}

theorem jumpChain_isClosedSet (h : ∀ x ∈ A, ∀ y, y ∉ A → R.Q x y = 0) :
    R.jumpChain.IsClosedSet A := by
  intro x hx y hy
  have hxy : x ≠ y := fun h' => hy (h' ▸ hx)
  simp only [RateChain.jumpChain_P, RateChain.jumpMatrix, hxy, ↓reduceIte, h x hx y hy,
    zero_div, ite_self]

theorem eq_expectedCost_of_generator_of_isClosedSet (hA : R.jumpChain.IsClosedSet A)
    (hR : R.jumpChain.Reaches A) (hq : ∀ x, x ∉ A → R.rate x ≠ 0) {c u : S → ℝ}
    (h0 : ∀ a ∈ A, u a = 0) (hgen : ∀ x, x ∉ A → ∑ y, R.Q x y * u y = -c x) :
    u = R.expectedCost A c := by
  refine funext fun z => congrFun (hA.eq_potential_of_step hR h0 fun x hx => ?_) z
  rw [RateChain.jumpChain_P, R.sum_jumpMatrix_mul (hq x hx), hgen x hx]
  ring

variable [MeasurableSpace S] [DiscreteMeasurableSpace S]

theorem lintegral_costBefore_of_isClosedSet (hA : R.jumpChain.IsClosedSet A)
    (hR : R.jumpChain.Reaches A) {c : S → ℝ} (hc : ∀ y, 0 ≤ c y) (x : S) :
    ∫⁻ p, R.costBefore A c p ∂R.jumpHoldLaw x = ENNReal.ofReal (R.expectedCost A c x) := by
  set φ : S → ℝ≥0∞ := fun y => if y ∈ A then 0 else ENNReal.ofReal (c y / R.rate y) with hφ
  have hterm : ∀ (k : ℕ) (p : (ℕ → S) × (ℕ → ℝ)),
      (if p.1 k ∈ A then (0 : ℝ≥0∞) else ENNReal.ofReal (c (p.1 k) * R.holdTime p k)) =
        φ (p.1 k) * ENNReal.ofReal (p.2 k) := by
    intro k p
    by_cases hp : p.1 k ∈ A
    · simp [hφ, hp]
    · simp only [hφ, hp, ↓reduceIte, RateChain.holdTime]
      rw [← ENNReal.ofReal_mul (div_nonneg (hc _) (R.rate_nonneg _))]
      congr 1
      ring
  have hmφ : ∀ k : ℕ, Measurable fun ω : ℕ → S => φ (ω k) := fun k =>
    (Measurable.of_discrete (f := φ)).comp (measurable_pi_apply k)
  have hme : ∀ k : ℕ, Measurable fun e : ℕ → ℝ => ENNReal.ofReal (e k) := fun k =>
    ENNReal.measurable_ofReal.comp (measurable_pi_apply k)
  have hmeas : ∀ k : ℕ, AEMeasurable
      (fun p : (ℕ → S) × (ℕ → ℝ) => φ (p.1 k) * ENNReal.ofReal (p.2 k)) (R.jumpHoldLaw x) :=
    fun k => (((hmφ k).comp measurable_fst).mul ((hme k).comp measurable_snd)).aemeasurable
  have hk : ∀ k : ℕ, ∫⁻ p : (ℕ → S) × (ℕ → ℝ), φ (p.1 k) * ENNReal.ofReal (p.2 k)
      ∂R.jumpHoldLaw x = ∫⁻ ω, φ (ω k) ∂R.jumpChain.pathLaw x := by
    intro k
    rw [RateChain.jumpHoldLaw, lintegral_prod_mul (hmφ k).aemeasurable (hme k).aemeasurable,
      lintegral_ofReal_clockLaw, mul_one]
  unfold RateChain.costBefore
  simp only [hterm]
  rw [lintegral_tsum hmeas]
  simp only [hk]
  rw [← lintegral_tsum fun k => (hmφ k).aemeasurable]
  exact hA.lintegral_pathCost hR (fun y => div_nonneg (hc y) (R.rate_nonneg y)) x

end Closed

section Events

variable {S ι : Type*} [DecidableEq S] [Fintype ι]

theorem eventQ_pos {r : ι → S → ℝ} {e : ι → S → S} (hr : ∀ i x, 0 ≤ r i x) {x y : S}
    (hxy : x ≠ y) (i : ι) (hy : y = e i x) (hpos : 0 < r i x) : 0 < eventQ r e x y := by
  simp only [eventQ, hxy, ↓reduceIte, sub_zero]
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun j => if y = e j x then r j x else 0)
    (fun j _ => ?_) (mem_univ i))
  · simp only [hy, ↓reduceIte]
    exact hpos
  · split_ifs
    · exact hr j x
    · exact le_rfl

end Events

namespace CountState

variable {n : ℕ} {p : CountState n}

theorem toDormant_active (h : 1 ≤ p.active) : p.toDormant.active = p.active - 1 := by
  rw [toDormant, dite_eq_left h]

theorem toDormant_dormant (h : 1 ≤ p.active) : p.toDormant.dormant = p.dormant + 1 := by
  rw [toDormant, dite_eq_left h]

theorem toActive_active (h : 1 ≤ p.dormant) : p.toActive.active = p.active + 1 := by
  rw [toActive, dite_eq_left h]

theorem toActive_dormant (h : 1 ≤ p.dormant) : p.toActive.dormant = p.dormant - 1 := by
  rw [toActive, dite_eq_left h]

theorem coalesce_active (h : 1 ≤ p.active) : p.coalesce.active = p.active - 1 := by
  rw [coalesce, dite_eq_left h]

theorem coalesce_dormant (p : CountState n) : p.coalesce.dormant = p.dormant := by
  unfold coalesce
  split_ifs <;> rfl

theorem countTarget_total_le (i : Fin 3) (p : CountState n) :
    (countTarget i p).active + (countTarget i p).dormant ≤ p.active + p.dormant := by
  fin_cases i
  · change p.toDormant.active + p.toDormant.dormant ≤ _
    by_cases h : 1 ≤ p.active
    · rw [toDormant_active h, toDormant_dormant h]
      omega
    · rw [toDormant, dite_eq_right h]
  · change p.toActive.active + p.toActive.dormant ≤ _
    by_cases h : 1 ≤ p.dormant
    · rw [toActive_active h, toActive_dormant h]
      omega
    · rw [toActive, dite_eq_right h]
  · change p.coalesce.active + p.coalesce.dormant ≤ _
    by_cases h : 1 ≤ p.active
    · rw [coalesce_active h, coalesce_dormant]
      omega
    · rw [coalesce, dite_eq_right h]

end CountState

noncomputable def coalesced (n : ℕ) : Finset (CountState n) :=
  univ.filter fun p => p.active + p.dormant ≤ 1

theorem mem_coalesced {n : ℕ} {p : CountState n} :
    p ∈ coalesced n ↔ p.active + p.dormant ≤ 1 := by
  simp [coalesced]

variable {c K : ℝ} {n : ℕ}

theorem countChain_isClosedSet (hc : 0 ≤ c) (hK : 0 ≤ K) :
    (countChain n c K hc hK).jumpChain.IsClosedSet (coalesced n) := by
  refine jumpChain_isClosedSet fun p hp q hq => ?_
  have hpq : p ≠ q := fun h => hq (h ▸ hp)
  refine eventQ_eq_zero hpq fun i hi => ?_
  exfalso
  have h1 := CountState.countTarget_total_le i p
  rw [← hi] at h1
  exact hq (mem_coalesced.2 (h1.trans (mem_coalesced.1 hp)))

theorem adj_toActive (hc : 0 < c) (hK : 0 < K) {p : CountState n} (hd : 1 ≤ p.dormant) :
    (countChain n c K hc.le hK.le).Adj p p.toActive :=
  ⟨(CountState.toActive_ne hd).symm, eventQ_pos (countRate_nonneg hc.le hK.le)
    (CountState.toActive_ne hd).symm 1 rfl
    (mul_pos (mul_pos hc hK) (Nat.cast_pos.2 hd) : 0 < c * K * (p.dormant : ℝ))⟩

theorem adj_coalesce (hc : 0 ≤ c) (hK : 0 ≤ K) {p : CountState n} (ha : 2 ≤ p.active) :
    (countChain n c K hc hK).Adj p p.coalesce :=
  ⟨(CountState.coalesce_ne (by omega)).symm, eventQ_pos (countRate_nonneg hc hK)
    (CountState.coalesce_ne (by omega)).symm 2 rfl
    (Nat.cast_pos.2 (Nat.choose_pos ha) : (0 : ℝ) < (p.active.choose 2 : ℕ))⟩

theorem countChain_reflTransGen (hc : 0 < c) (hK : 0 < K) (p : CountState n) :
    ∃ a ∈ coalesced n, Relation.ReflTransGen (countChain n c K hc.le hK.le).Adj p a := by
  generalize hm : 2 * (p.active + p.dormant) + p.dormant = m
  induction m using Nat.strong_induction_on generalizing p with
  | _ m ih =>
    by_cases h1 : p.active + p.dormant ≤ 1
    · exact ⟨p, mem_coalesced.2 h1, Relation.ReflTransGen.refl⟩
    · by_cases hd : 1 ≤ p.dormant
      · obtain ⟨a, ha, hpa⟩ := ih (2 * (p.toActive.active + p.toActive.dormant) +
          p.toActive.dormant) (by
            rw [CountState.toActive_active hd, CountState.toActive_dormant hd]
            omega) p.toActive rfl
        exact ⟨a, ha, Relation.ReflTransGen.head (adj_toActive hc hK hd) hpa⟩
      · have h2 : 2 ≤ p.active := by omega
        obtain ⟨a, ha, hpa⟩ := ih (2 * (p.coalesce.active + p.coalesce.dormant) +
          p.coalesce.dormant) (by
            rw [CountState.coalesce_active (by omega), CountState.coalesce_dormant]
            omega) p.coalesce rfl
        exact ⟨a, ha, Relation.ReflTransGen.head (adj_coalesce hc.le hK.le h2) hpa⟩

theorem countChain_reaches (hc : 0 < c) (hK : 0 < K) :
    (countChain n c K hc.le hK.le).jumpChain.Reaches (coalesced n) :=
  RateChain.reaches_of_reflTransGen (countChain_reflTransGen hc hK)

theorem countChain_rate_ne_zero (hc : 0 < c) (hK : 0 < K) {p : CountState n}
    (hp : p ∉ coalesced n) : (countChain n c K hc.le hK.le).rate p ≠ 0 := by
  rw [mem_coalesced] at hp
  by_cases hd : 1 ≤ p.dormant
  · exact (RateChain.rate_pos_of_adj (adj_toActive hc hK hd)).ne'
  · exact (RateChain.rate_pos_of_adj (adj_coalesce hc.le hK.le (by omega))).ne'

noncomputable def pairTime (c K : ℝ) (p : CountState n) : ℝ :=
  if p.active = 2 ∧ p.dormant = 0 then (1 + 1 / K) ^ 2
  else if p.active = 1 ∧ p.dormant = 1 then (1 + 1 / K) ^ 2 + (2 * K + 1) / (2 * c * K ^ 2)
  else if p.active = 0 ∧ p.dormant = 2 then (1 + 1 / K) ^ 2 + (3 * K + 1) / (2 * c * K ^ 2)
  else 0

theorem pairTime_of_mem_coalesced {p : CountState n} (hp : p ∈ coalesced n) :
    pairTime c K p = 0 := by
  rw [mem_coalesced] at hp
  have h1 : ¬(p.active = 2 ∧ p.dormant = 0) := by omega
  have h2 : ¬(p.active = 1 ∧ p.dormant = 1) := by omega
  have h3 : ¬(p.active = 0 ∧ p.dormant = 2) := by omega
  simp [pairTime, h1, h2, h3]

theorem sum_countChain_Q_mul_pairTime (hc : 0 < c) (hK : 0 < K) {p : CountState 2}
    (hp : p ∉ coalesced 2) :
    ∑ q, (countChain 2 c K hc.le hK.le).Q p q * pairTime c K q = -1 := by
  rw [mem_coalesced] at hp
  have hc' := hc.ne'
  have hK' := hK.ne'
  rw [sum_countChain_Q_mul]
  obtain ⟨a, d, hle⟩ := p
  have hcases : (a = 2 ∧ d = 0) ∨ (a = 1 ∧ d = 1) ∨ (a = 0 ∧ d = 2) := by
    simp only at hp
    omega
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [pairTime, CountState.toDormant, CountState.toActive, CountState.coalesce]
    field_simp
    ring
  · simp [pairTime, CountState.toDormant, CountState.toActive, CountState.coalesce]
    field_simp
    ring
  · simp [pairTime, CountState.toDormant, CountState.toActive, CountState.coalesce]
    field_simp
    ring

theorem pairTime_eq_expectedTime (hc : 0 < c) (hK : 0 < K) :
    pairTime c K = (countChain 2 c K hc.le hK.le).expectedTime (coalesced 2) :=
  eq_expectedCost_of_generator_of_isClosedSet (countChain_isClosedSet hc.le hK.le)
    (countChain_reaches hc hK) (fun _ hp => countChain_rate_ne_zero hc hK hp)
    (fun _ hp => pairTime_of_mem_coalesced hp)
    fun _ hp => sum_countChain_Q_mul_pairTime hc hK hp

/-- Source: blath_etal2015, p. 927, eq. (12). -/
theorem expectedTime_two_active (hc : 0 < c) (hK : 0 < K) :
    (countChain 2 c K hc.le hK.le).expectedTime (coalesced 2) ⟨2, 0, le_rfl⟩ =
      (1 + 1 / K) ^ 2 := by
  rw [← pairTime_eq_expectedTime hc hK]
  simp [pairTime]

theorem expectedTime_active_dormant (hc : 0 < c) (hK : 0 < K) :
    (countChain 2 c K hc.le hK.le).expectedTime (coalesced 2) ⟨1, 1, le_rfl⟩ =
      (1 + 1 / K) ^ 2 + (2 * K + 1) / (2 * c * K ^ 2) := by
  rw [← pairTime_eq_expectedTime hc hK]
  simp [pairTime]

theorem expectedTime_two_dormant (hc : 0 < c) (hK : 0 < K) :
    (countChain 2 c K hc.le hK.le).expectedTime (coalesced 2) ⟨0, 2, le_rfl⟩ =
      (1 + 1 / K) ^ 2 + (3 * K + 1) / (2 * c * K ^ 2) := by
  rw [← pairTime_eq_expectedTime hc hK]
  simp [pairTime]

theorem one_lt_expectedTime_two_active (hc : 0 < c) (hK : 0 < K) :
    1 < (countChain 2 c K hc.le hK.le).expectedTime (coalesced 2) ⟨2, 0, le_rfl⟩ := by
  rw [expectedTime_two_active hc hK]
  have h : 0 < 1 / K := one_div_pos.2 hK
  nlinarith

theorem expectedTime_two_active_one_one :
    (countChain 2 1 1 zero_le_one zero_le_one).expectedTime (coalesced 2) ⟨2, 0, le_rfl⟩ = 4 := by
  rw [expectedTime_two_active one_pos one_pos]
  norm_num

theorem tendsto_pairTime_atTop (hc : 0 < c) {p : CountState 2} (hp : p ∉ coalesced 2) :
    Tendsto (fun K : ℝ => pairTime c K p) atTop (𝓝 ((expTMRCA 2 : ℚ) : ℝ)) := by
  rw [expTMRCA_two, Rat.cast_one]
  rw [mem_coalesced] at hp
  have hc' := hc.ne'
  have hinv : Tendsto (fun K : ℝ => K⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  obtain ⟨a, d, hle⟩ := p
  have hcases : (a = 2 ∧ d = 0) ∨ (a = 1 ∧ d = 1) ∨ (a = 0 ∧ d = 2) := by
    simp only at hp
    omega
  have key : ∀ G : ℝ → ℝ, Continuous G → G 0 = 1 →
      (∀ K : ℝ, K ≠ 0 → pairTime c K (⟨a, d, hle⟩ : CountState 2) = G K⁻¹) →
      Tendsto (fun K : ℝ => pairTime c K (⟨a, d, hle⟩ : CountState 2)) atTop (𝓝 1) := by
    intro G hG hG0 hGK
    have h1 : Tendsto (fun K : ℝ => G K⁻¹) atTop (𝓝 1) := hG0 ▸ (hG.tendsto 0).comp hinv
    refine h1.congr' ?_
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with K hK
    exact (hGK K hK).symm
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine key (fun t => (1 + t) ^ 2) (by fun_prop) (by norm_num) fun K hK => ?_
    simp [pairTime]
  · refine key (fun t => (1 + t) ^ 2 + (2 * t + t ^ 2) / (2 * c)) (by fun_prop) (by norm_num)
      fun K hK => ?_
    simp [pairTime]
    field_simp
  · refine key (fun t => (1 + t) ^ 2 + (3 * t + t ^ 2) / (2 * c)) (by fun_prop) (by norm_num)
      fun K hK => ?_
    simp [pairTime]
    field_simp

variable {α : Type*} [Fintype α] [DecidableEq α]

variable (α) in
def allActive : Marked α where
  partition := ⊥
  dormant := fun _ => false
  dormant_eq' := fun _ _ _ _ _ _ => rfl

theorem activeParts_allActive :
    activeParts (allActive α) = (⊥ : Finpartition (univ : Finset α)).parts := by
  ext B
  rw [mem_activeParts]
  exact ⟨fun h => h.1, fun h => ⟨h, fun _ _ => rfl⟩⟩

theorem dormantParts_allActive : dormantParts (allActive α) = ∅ := by
  ext B
  rw [mem_dormantParts]
  refine ⟨fun h => ?_, fun h => absurd h (notMem_empty B)⟩
  obtain ⟨a, ha⟩ := (allActive α).partition.nonempty_of_mem_parts h.1
  exact absurd (h.2 a ha) Bool.false_ne_true

theorem count_allActive_active : (count (allActive α)).active = Fintype.card α := by
  change (activeParts (allActive α)).card = _
  rw [activeParts_allActive]
  simp

theorem count_allActive_dormant : (count (allActive α)).dormant = 0 := by
  change (dormantParts (allActive α)).card = _
  rw [dormantParts_allActive, card_empty]

variable (α) in
noncomputable def coalescedStates : Finset (Marked α) :=
  preimageFinset count (coalesced (Fintype.card α))

theorem mem_coalescedStates {x : Marked α} :
    x ∈ coalescedStates α ↔ x.partition.parts.card ≤ 1 := by
  rw [coalescedStates, mem_preimageFinset, mem_coalesced,
    ← card_activeParts_add_card_dormantParts]
  rfl

noncomputable def tmrca (c K : ℝ) (hc : 0 ≤ c) (hK : 0 ≤ K)
    (p : (ℕ → Marked α) × (ℕ → ℝ)) : ℝ≥0∞ :=
  (chain α c K hc hK).timeBefore (coalescedStates α) p

/-- Source: blath_etal2015, p. 927, eq. (12). -/
theorem lintegral_tmrca_two (hα : Fintype.card α = 2) (hc : 0 < c) (hK : 0 < K) :
    ∫⁻ p, tmrca c K hc.le hK.le p ∂(chain α c K hc.le hK.le).jumpHoldLaw (allActive α) =
      ENNReal.ofReal ((1 + 1 / K) ^ 2) := by
  have h := (chain_lumps_count (α := α) hc.le hK.le).lintegral_costBefore_preimage
    (fun _ _ => chain_Q_eq_zero_of_count_eq hc.le hK.le) (coalesced (Fintype.card α))
    (fun _ => 1) (allActive α)
  refine h.trans ?_
  rw [lintegral_costBefore_of_isClosedSet (countChain_isClosedSet hc.le hK.le)
    (countChain_reaches hc hK) (fun _ => zero_le_one)]
  congr 1
  have key : ∀ (n : ℕ) (p : CountState n), n = 2 → p.active = 2 → p.dormant = 0 →
      (countChain n c K hc.le hK.le).expectedCost (coalesced n) (fun _ => 1) p =
        (1 + 1 / K) ^ 2 := by
    intro n p hn ha hd
    subst hn
    have hp : p = ⟨2, 0, le_rfl⟩ := CountState.ext ha hd
    rw [hp]
    exact expectedTime_two_active hc hK
  exact key _ _ hα (count_allActive_active.trans hα) count_allActive_dormant

end Rhone.Coalescent.SeedBank
