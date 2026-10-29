/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ACComparisonBounds
public import Rhone.Statistics.Identifiability.IntegrablePanLaw
public import Rhone.Statistics.Identifiability.PanDiagonalSufficiency
public import Rhone.Statistics.Identifiability.PanRecombinationUniqueness

/-! # Volterra uniqueness and Gronwall bounds for the common-clock equations -/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability

theorem commonClock_integral_gronwall_zero {h : ℝ → ℝ} {T K : ℝ}
    (hT : 0 ≤ T) (hi : IntervalIntegrable h volume 0 T)
    (hn : ∀ t ∈ Icc 0 T, 0 ≤ h t)
    (hb : ∀ t ∈ Icc 0 T, h t ≤ K * ∫ s in (0 : ℝ)..t, h s) :
    EqOn h (fun _ => 0) (Icc 0 T) := by
  intro t ht
  have his : IntervalIntegrable h volume 0 t :=
    hi.mono_set (by simpa only [uIcc_of_le hT, uIcc_of_le ht.1] using
      (Icc_subset_Icc le_rfl ht.2))
  have hF := his.absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp)
  have hFd : ∀ᵐ x, x ∈ uIcc 0 t →
      HasDerivAt (fun y => ∫ s in (0 : ℝ)..y, h s) (h x) x := by
    filter_upwards [his.ae_hasDerivAt_integral] with x hx hxmem
    exact hx hxmem 0 (by simp)
  have hH : AbsolutelyContinuousOnInterval (fun x : ℝ => -K * x) 0 t :=
    (LipschitzWith.id.lipschitzOnWith.absolutelyContinuousOnInterval).const_mul (-K)
  have hHd : ∀ᵐ x, x ∈ uIcc 0 t → HasDerivAt (fun y : ℝ => -K * y) (-K) x := by
    filter_upwards with x hx
    simpa using (hasDerivAt_id x).const_mul (-K)
  have hbound : ∀ᵐ x, x ∈ uIcc 0 t →
      h x ≤ -(-K) * ∫ s in (0 : ℝ)..x, h s := by
    filter_upwards with x hx
    have hx' : x ∈ Icc 0 t := by simpa only [uIcc_of_le ht.1] using hx
    simpa using hb x ⟨hx'.1, hx'.2.trans ht.2⟩
  have hle := ac_comparison_upper (fun y => ∫ s in (0 : ℝ)..y, h s) h
    (fun x => -K * x) (fun _ => -K) 0 t ht.1 hF hH hFd hHd hbound
  simp only [intervalIntegral.integral_same, mul_zero, zero_mul] at hle
  have hnonneg : 0 ≤ ∫ s in (0 : ℝ)..t, h s :=
    intervalIntegral.integral_nonneg ht.1 (fun s hs => hn s ⟨hs.1, hs.2.trans ht.2⟩)
  have he : (∫ s in (0 : ℝ)..t, h s) = 0 := le_antisymm hle hnonneg
  have hh := hb t ht
  rw [he, mul_zero] at hh
  exact le_antisymm hh (hn t ht)

theorem commonClock_volterra_unique {K : ℝ → ℝ → ℝ} {b u v : ℝ → ℝ} {T M : ℝ}
    (hT : 0 ≤ T) (hu : ContinuousOn u (Icc 0 T)) (hv : ContinuousOn v (Icc 0 T))
    (hKi : ∀ t ∈ Icc 0 T, IntervalIntegrable (K t) volume 0 t)
    (hKb : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 t, |K t s| ≤ M)
    (huEq : ∀ t ∈ Icc 0 T, u t = b t + ∫ s in (0 : ℝ)..t, K t s * u s)
    (hvEq : ∀ t ∈ Icc 0 T, v t = b t + ∫ s in (0 : ℝ)..t, K t s * v s) :
    EqOn u v (Icc 0 T) := by
  have hcont : ContinuousOn (fun s => |u s - v s|) (Icc 0 T) :=
    (hu.sub hv).abs
  have hz := commonClock_integral_gronwall_zero hT
    (hcont.intervalIntegrable_of_Icc hT) (fun _ _ => abs_nonneg _) (K := M) ?_
  · intro t ht
    exact sub_eq_zero.mp (abs_eq_zero.mp (hz ht))
  intro t ht
  have hs : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
  have hui : IntervalIntegrable (fun s => K t s * u s) volume 0 t :=
    (hKi t ht).mul_continuousOn ((hu.mono hs).mono (by rw [uIcc_of_le ht.1]))
  have hvi : IntervalIntegrable (fun s => K t s * v s) volume 0 t :=
    (hKi t ht).mul_continuousOn ((hv.mono hs).mono (by rw [uIcc_of_le ht.1]))
  have he : u t - v t = ∫ s in (0 : ℝ)..t, K t s * (u s - v s) := by
    rw [huEq t ht, hvEq t ht]
    simp_rw [mul_sub]
    rw [intervalIntegral.integral_sub hui hvi]
    ring
  rw [he]
  calc
    |∫ s in (0 : ℝ)..t, K t s * (u s - v s)| ≤
        ∫ s in (0 : ℝ)..t, |K t s * (u s - v s)| :=
      by
        simpa only [Real.norm_eq_abs] using
          (intervalIntegral.norm_integral_le_integral_norm
            (f := fun s => K t s * (u s - v s)) ht.1)
    _ ≤ ∫ s in (0 : ℝ)..t, M * |u s - v s| := by
      apply intervalIntegral.integral_mono_on ht.1
      · simpa only [mul_sub] using (hui.sub hvi).abs
      · exact ((hcont.mono hs).intervalIntegrable_of_Icc ht.1).const_mul M
      · intro s hs'
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hKb t ht s hs') (abs_nonneg _)
    _ = M * ∫ s in (0 : ℝ)..t, |u s - v s| := intervalIntegral.integral_const_mul _ _

theorem commonClock_exists_abs_bound {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc a b, |f t| ≤ M := by
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab) hf.abs
  exact ⟨|f x|, abs_nonneg _, fun t ht => hmax ht⟩

theorem commonClock_volterra_pair_unique
    {k₁₁ k₁₂ k₂₁ k₂₂ : ℝ → ℝ → ℝ} {b₁ b₂ u₁ u₂ v₁ v₂ : ℝ → ℝ} {T M : ℝ}
    (hT : 0 ≤ T)
    (hu₁ : ContinuousOn u₁ (Icc 0 T)) (hu₂ : ContinuousOn u₂ (Icc 0 T))
    (hv₁ : ContinuousOn v₁ (Icc 0 T)) (hv₂ : ContinuousOn v₂ (Icc 0 T))
    (hki : ∀ t ∈ Icc 0 T, ∀ k ∈ ({k₁₁, k₁₂, k₂₁, k₂₂} : Set (ℝ → ℝ → ℝ)),
      IntervalIntegrable (k t) volume 0 t)
    (hkb : ∀ t ∈ Icc 0 T, ∀ s ∈ Icc 0 t,
      ∀ k ∈ ({k₁₁, k₁₂, k₂₁, k₂₂} : Set (ℝ → ℝ → ℝ)), |k t s| ≤ M)
    (huEq₁ : ∀ t ∈ Icc 0 T, u₁ t = b₁ t +
      ∫ s in (0 : ℝ)..t, k₁₁ t s * u₁ s + k₁₂ t s * u₂ s)
    (huEq₂ : ∀ t ∈ Icc 0 T, u₂ t = b₂ t +
      ∫ s in (0 : ℝ)..t, k₂₁ t s * u₁ s + k₂₂ t s * u₂ s)
    (hvEq₁ : ∀ t ∈ Icc 0 T, v₁ t = b₁ t +
      ∫ s in (0 : ℝ)..t, k₁₁ t s * v₁ s + k₁₂ t s * v₂ s)
    (hvEq₂ : ∀ t ∈ Icc 0 T, v₂ t = b₂ t +
      ∫ s in (0 : ℝ)..t, k₂₁ t s * v₁ s + k₂₂ t s * v₂ s) :
    EqOn u₁ v₁ (Icc 0 T) ∧ EqOn u₂ v₂ (Icc 0 T) := by
  let d₁ := fun s => u₁ s - v₁ s
  let d₂ := fun s => u₂ s - v₂ s
  let h := fun s => |d₁ s| + |d₂ s|
  have hc₁ : ContinuousOn d₁ (Icc 0 T) := hu₁.sub hv₁
  have hc₂ : ContinuousOn d₂ (Icc 0 T) := hu₂.sub hv₂
  have hh : ContinuousOn h (Icc 0 T) := hc₁.abs.add hc₂.abs
  have hi (k) (hk : k ∈ ({k₁₁, k₁₂, k₂₁, k₂₂} : Set (ℝ → ℝ → ℝ)))
      (w : ℝ → ℝ) (hw : ContinuousOn w (Icc 0 T)) (t) (ht : t ∈ Icc 0 T) :
      IntervalIntegrable (fun s => k t s * w s) volume 0 t :=
    (hki t ht k hk).mul_continuousOn
      (hw.mono (by rw [uIcc_of_le ht.1]; exact Icc_subset_Icc le_rfl ht.2))
  have hdiff (k l) (hk : k ∈ ({k₁₁, k₁₂, k₂₁, k₂₂} : Set (ℝ → ℝ → ℝ)))
      (hl : l ∈ ({k₁₁, k₁₂, k₂₁, k₂₂} : Set (ℝ → ℝ → ℝ)))
      (t) (ht : t ∈ Icc 0 T) :
      (∫ s in (0 : ℝ)..t, k t s * u₁ s + l t s * u₂ s) -
      (∫ s in (0 : ℝ)..t, k t s * v₁ s + l t s * v₂ s) =
      ∫ s in (0 : ℝ)..t, k t s * d₁ s + l t s * d₂ s := by
    rw [← intervalIntegral.integral_sub ((hi k hk u₁ hu₁ t ht).add (hi l hl u₂ hu₂ t ht))
      ((hi k hk v₁ hv₁ t ht).add (hi l hl v₂ hv₂ t ht))]
    apply intervalIntegral.integral_congr
    intro s hs
    dsimp [d₁, d₂]
    ring
  have hnorm (k l) (hk : k ∈ ({k₁₁, k₁₂, k₂₁, k₂₂} : Set (ℝ → ℝ → ℝ)))
      (hl : l ∈ ({k₁₁, k₁₂, k₂₁, k₂₂} : Set (ℝ → ℝ → ℝ)))
      (t) (ht : t ∈ Icc 0 T) :
      |∫ s in (0 : ℝ)..t, k t s * d₁ s + l t s * d₂ s| ≤
        M * ∫ s in (0 : ℝ)..t, h s := by
    calc
      _ ≤ ∫ s in (0 : ℝ)..t, |k t s * d₁ s + l t s * d₂ s| :=
        by simpa only [Real.norm_eq_abs] using
          (intervalIntegral.norm_integral_le_integral_norm
            (f := fun s => k t s * d₁ s + l t s * d₂ s) ht.1)
      _ ≤ ∫ s in (0 : ℝ)..t, M * h s := by
        apply intervalIntegral.integral_mono_on ht.1
        · exact ((hi k hk d₁ hc₁ t ht).add (hi l hl d₂ hc₂ t ht)).abs
        · exact (hh.mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1 |>.const_mul M
        · intro s hs
          calc
            _ ≤ |k t s * d₁ s| + |l t s * d₂ s| := abs_add_le _ _
            _ ≤ M * |d₁ s| + M * |d₂ s| := by
              simp only [abs_mul]
              exact add_le_add
                (mul_le_mul_of_nonneg_right (hkb t ht s hs k hk) (abs_nonneg _))
                (mul_le_mul_of_nonneg_right (hkb t ht s hs l hl) (abs_nonneg _))
            _ = _ := by dsimp [h]; ring
      _ = _ := intervalIntegral.integral_const_mul _ _
  have hz : EqOn h (fun _ => 0) (Icc 0 T) := by
    apply commonClock_integral_gronwall_zero hT (hh.intervalIntegrable_of_Icc hT)
      (fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) (K := 2 * M)
    intro t ht
    have h₁ : d₁ t = ∫ s in (0 : ℝ)..t, k₁₁ t s * d₁ s + k₁₂ t s * d₂ s := by
      dsimp [d₁]
      rw [huEq₁ t ht, hvEq₁ t ht]
      simpa only [add_sub_add_left_eq_sub] using hdiff k₁₁ k₁₂ (by simp) (by simp) t ht
    have h₂ : d₂ t = ∫ s in (0 : ℝ)..t, k₂₁ t s * d₁ s + k₂₂ t s * d₂ s := by
      dsimp [d₂]
      rw [huEq₂ t ht, hvEq₂ t ht]
      simpa only [add_sub_add_left_eq_sub] using hdiff k₂₁ k₂₂ (by simp) (by simp) t ht
    dsimp only [h]
    rw [h₁, h₂]
    linarith [hnorm k₁₁ k₁₂ (by simp) (by simp) t ht,
      hnorm k₂₁ k₂₂ (by simp) (by simp) t ht]
  constructor
  · intro t ht
    have he := hz ht
    dsimp [h, d₁, d₂] at he
    have : |u₁ t - v₁ t| = 0 := by linarith [abs_nonneg (u₂ t - v₂ t), abs_nonneg (u₁ t - v₁ t)]
    exact sub_eq_zero.mp (abs_eq_zero.mp this)
  · intro t ht
    have he := hz ht
    dsimp [h, d₁, d₂] at he
    have : |u₂ t - v₂ t| = 0 := by linarith [abs_nonneg (u₂ t - v₂ t), abs_nonneg (u₁ t - v₁ t)]
    exact sub_eq_zero.mp (abs_eq_zero.mp this)

theorem commonClock_sum_equation_linear {f rate S δ G g : ℝ → ℝ} {t : ℝ}
    (he : g t = δ t / 2 + 2 * ∫ s in (0 : ℝ)..t,
      ((rate s * G s - δ s) / S s) * f (2 * t - s)) :
    δ t = 2 * g t + ∫ s in (0 : ℝ)..t,
      (4 * f (2 * t - s) / S s) * δ s +
      (-(4 * f (2 * t - s) / S s) * rate s) * G s := by
  have hi : (∫ s in (0 : ℝ)..t,
      (4 * f (2 * t - s) / S s) * δ s +
      (-(4 * f (2 * t - s) / S s) * rate s) * G s) =
      -4 * ∫ s in (0 : ℝ)..t, ((rate s * G s - δ s) / S s) * f (2 * t - s) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs
    ring
  rw [hi]
  linarith

theorem commonClock_reconstruction_unique_on
    {f rate S δ₁ δ₂ G₁ G₂ g : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hf : ContinuousOn f (Icc 0 (2 * T)))
    (hr : ContinuousOn rate (Icc 0 T)) (hS : ContinuousOn S (Icc 0 T))
    (hSpos : ∀ t ∈ Icc 0 T, 0 < S t)
    (hd₁ : ContinuousOn δ₁ (Icc 0 T)) (hd₂ : ContinuousOn δ₂ (Icc 0 T))
    (hG₁ : ContinuousOn G₁ (Icc 0 T)) (hG₂ : ContinuousOn G₂ (Icc 0 T))
    (hm₁ : ∀ t ∈ Icc 0 T, G₁ t = 1 +
      ∫ s in (0 : ℝ)..t, δ₁ s - 2 * rate s * G₁ s)
    (hm₂ : ∀ t ∈ Icc 0 T, G₂ t = 1 +
      ∫ s in (0 : ℝ)..t, δ₂ s - 2 * rate s * G₂ s)
    (hs₁ : ∀ t ∈ Icc 0 T, g t = δ₁ t / 2 + 2 *
      ∫ s in (0 : ℝ)..t, ((rate s * G₁ s - δ₁ s) / S s) * f (2 * t - s))
    (hs₂ : ∀ t ∈ Icc 0 T, g t = δ₂ t / 2 + 2 *
      ∫ s in (0 : ℝ)..t, ((rate s * G₂ s - δ₂ s) / S s) * f (2 * t - s)) :
    EqOn δ₁ δ₂ (Icc 0 T) ∧ EqOn G₁ G₂ (Icc 0 T) := by
  let A := fun t s => 4 * f (2 * t - s) / S s
  let B := fun t s => -(A t s) * rate s
  let C := fun (_t : ℝ) (_s : ℝ) => (1 : ℝ)
  let D := fun (_t : ℝ) s => -2 * rate s
  have hSi : ContinuousOn (fun t => (S t)⁻¹) (Icc 0 T) :=
    hS.inv₀ (fun t ht => (hSpos t ht).ne')
  obtain ⟨F, hF, hFb⟩ := commonClock_exists_abs_bound (by linarith : 0 ≤ 2 * T) hf
  obtain ⟨L, hL, hLb⟩ := commonClock_exists_abs_bound hT hr
  obtain ⟨J, hJ, hJb⟩ := commonClock_exists_abs_bound hT hSi
  let M := 4 * F * J + 4 * F * J * L + 1 + 2 * L
  have hcA (t : ℝ) (ht : t ∈ Icc 0 T) : ContinuousOn (A t) (Icc 0 t) := by
    apply ContinuousOn.mul
    · exact (hf.comp (continuous_const.sub continuous_id).continuousOn
        (by intro s hs; change 0 ≤ 2 * t - s ∧ 2 * t - s ≤ 2 * T; constructor <;> linarith
          [hs.1, hs.2, ht.1, ht.2])).const_mul 4
    · exact hSi.mono (Icc_subset_Icc le_rfl ht.2)
  have hcB (t : ℝ) (ht : t ∈ Icc 0 T) : ContinuousOn (B t) (Icc 0 t) :=
    (hcA t ht).neg.mul (hr.mono (Icc_subset_Icc le_rfl ht.2))
  have hcD (t : ℝ) (ht : t ∈ Icc 0 T) : ContinuousOn (D t) (Icc 0 t) :=
    (hr.mono (Icc_subset_Icc le_rfl ht.2)).const_mul (-2)
  have hAb (t : ℝ) (ht : t ∈ Icc 0 T) (s : ℝ) (hs : s ∈ Icc 0 t) :
      |A t s| ≤ 4 * F * J := by
    have hfs := hFb (2 * t - s) (by constructor <;> linarith [hs.1, hs.2, ht.1, ht.2])
    have hjs := hJb s ⟨hs.1, hs.2.trans ht.2⟩
    dsimp [A]
    rw [div_eq_mul_inv, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hfs (by norm_num)) hjs
      (abs_nonneg _) (by positivity)
  apply commonClock_volterra_pair_unique (k₁₁ := A) (k₁₂ := B) (k₂₁ := C) (k₂₂ := D)
    (b₁ := fun t => 2 * g t) (b₂ := fun _ => 1) (M := M)
    hT hd₁ hG₁ hd₂ hG₂
  · intro t ht k hk
    simp only [mem_insert_iff, mem_singleton_iff] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · exact (hcA t ht).intervalIntegrable_of_Icc ht.1
    · exact (hcB t ht).intervalIntegrable_of_Icc ht.1
    · exact intervalIntegrable_const
    · exact (hcD t ht).intervalIntegrable_of_Icc ht.1
  · intro t ht s hs k hk
    have hsT : s ∈ Icc 0 T := ⟨hs.1, hs.2.trans ht.2⟩
    have hproducts : 0 ≤ 4 * F * J ∧ 0 ≤ 4 * F * J * L := by constructor <;> positivity
    have ha := hAb t ht s hs
    have hb : |B t s| ≤ 4 * F * J * L := by
      dsimp [B]
      rw [abs_mul, abs_neg]
      exact mul_le_mul ha (hLb s hsT) (abs_nonneg _) hproducts.1
    have hd : |D t s| ≤ 2 * L := by
      dsimp [D]
      rw [abs_mul]
      rw [abs_of_neg (by norm_num : (-2 : ℝ) < 0)]
      norm_num only [neg_neg]
      exact mul_le_mul_of_nonneg_left (hLb s hsT) (by norm_num : (0 : ℝ) ≤ 2)
    simp only [mem_insert_iff, mem_singleton_iff] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · dsimp [M]; linarith
    · dsimp [M]; linarith
    · dsimp [C, M]; rw [abs_one]; linarith
    · dsimp [M]; linarith
  · intro t ht
    exact commonClock_sum_equation_linear (hs₁ t ht)
  · intro t ht
    convert hm₁ t ht using 1
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    dsimp [C, D]
    ring
  · intro t ht
    exact commonClock_sum_equation_linear (hs₂ t ht)
  · intro t ht
    convert hm₂ t ht using 1
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    dsimp [C, D]
    ring

theorem commonClock_reconstruction_unique
    {f rate S δ₁ δ₂ G₁ G₂ g : ℝ → ℝ}
    (hf : ContinuousOn f (Ici 0)) (hr : ContinuousOn rate (Ici 0))
    (hS : ContinuousOn S (Ici 0)) (hSpos : ∀ t ∈ Ici 0, 0 < S t)
    (hd₁ : ContinuousOn δ₁ (Ici 0)) (hd₂ : ContinuousOn δ₂ (Ici 0))
    (hG₁ : ContinuousOn G₁ (Ici 0)) (hG₂ : ContinuousOn G₂ (Ici 0))
    (hm₁ : ∀ t ∈ Ici 0, G₁ t = 1 + ∫ s in (0 : ℝ)..t, δ₁ s - 2 * rate s * G₁ s)
    (hm₂ : ∀ t ∈ Ici 0, G₂ t = 1 + ∫ s in (0 : ℝ)..t, δ₂ s - 2 * rate s * G₂ s)
    (hs₁ : ∀ t ∈ Ici 0, g t = δ₁ t / 2 + 2 *
      ∫ s in (0 : ℝ)..t, ((rate s * G₁ s - δ₁ s) / S s) * f (2 * t - s))
    (hs₂ : ∀ t ∈ Ici 0, g t = δ₂ t / 2 + 2 *
      ∫ s in (0 : ℝ)..t, ((rate s * G₂ s - δ₂ s) / S s) * f (2 * t - s)) :
    EqOn δ₁ δ₂ (Ici 0) ∧ EqOn G₁ G₂ (Ici 0) := by
  have he (t : ℝ) (ht : 0 ≤ t) := commonClock_reconstruction_unique_on ht
    (hf.mono Icc_subset_Ici_self) (hr.mono Icc_subset_Ici_self)
    (hS.mono Icc_subset_Ici_self) (fun s hs => hSpos s hs.1)
    (hd₁.mono Icc_subset_Ici_self) (hd₂.mono Icc_subset_Ici_self)
    (hG₁.mono Icc_subset_Ici_self) (hG₂.mono Icc_subset_Ici_self)
    (fun s hs => hm₁ s hs.1) (fun s hs => hm₂ s hs.1)
    (fun s hs => hs₁ s hs.1) (fun s hs => hs₂ s hs.1)
  exact ⟨fun t ht => (he t ht).1 ⟨ht, le_rfl⟩,
    fun t ht => (he t ht).2 ⟨ht, le_rfl⟩⟩

end Rhone.Statistics.Identifiability
