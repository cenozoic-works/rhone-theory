/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Opposing haploid viability in two symmetrically migrating demes

Source: burger2013_migration_selection, sec. 3.1, eq. (3.5), sec. 2.3, eq. (2.9). -/

@[expose] public section
namespace Rhone.Dynamics

/-- Source: burger2013_migration_selection, sec. 3.1, eq. (3.5), sec. 2.3, eq. (2.9). -/
noncomputable def twoDemeFirst (s m p q : ℝ) : ℝ :=
  (1 - m) * (1 + s) * p / (1 + s * p) + m * q / (1 + s * (1 - q))

/-- Source: burger2013_migration_selection, sec. 3.1, eq. (3.5), sec. 2.3, eq. (2.9). -/
noncomputable def twoDemeSecond (s m p q : ℝ) : ℝ :=
  m * (1 + s) * p / (1 + s * p) + (1 - m) * q / (1 + s * (1 - q))

/-- Source: burger2013_migration_selection, sec. 3.1, eq. (3.5), sec. 2.3, eq. (2.9). -/
noncomputable def twoDemeEquilibrium (s m : ℝ) : ℝ :=
  (s - 2 * m - m * s + Real.sqrt ((s - 2 * m - m * s)^2 + 4 * s * m)) / (2 * s)

theorem two_deme_symmetric_mem {s m p q : ℝ} (hs : 0 < s)
    (hm0 : 0 < m) (hm1 : m ≤ 1 / 2)
    (hp : p ∈ Set.Icc 0 1) (hq : q ∈ Set.Icc 0 1) :
    twoDemeFirst s m p q ∈ Set.Icc 0 1 ∧
    twoDemeSecond s m p q ∈ Set.Icc 0 1 := by
  have hp0 := hp.1
  have hp1 := hp.2
  have hq0 := hq.1
  have hq1 := hq.2
  have hd1 : 0 < 1 + s * p := by positivity
  have hd2 : 0 < 1 + s * (1 - q) := by
    have hq' : 0 ≤ 1 - q := sub_nonneg.mpr hq.2
    positivity
  have hf0 : 0 ≤ (1 + s) * p / (1 + s * p) := by positivity
  have hg0 : 0 ≤ q / (1 + s * (1 - q)) := div_nonneg hq.1 hd2.le
  have hf1 : (1 + s) * p / (1 + s * p) ≤ 1 := by
    apply (div_le_one hd1).mpr
    nlinarith [hp.2]
  have hg1 : q / (1 + s * (1 - q)) ≤ 1 := by
    apply (div_le_one hd2).mpr
    nlinarith [hq.2]
  have hm' : 0 ≤ 1 - m := by linarith
  unfold twoDemeFirst twoDemeSecond
  simp only [mul_div_assoc] at hf0 hf1 hg0 hg1 ⊢
  constructor <;> constructor
  · positivity
  · nlinarith [mul_le_mul_of_nonneg_left hf1 hm', mul_le_mul_of_nonneg_left hg1 hm0.le]
  · positivity
  · nlinarith [mul_le_mul_of_nonneg_left hf1 hm0.le, mul_le_mul_of_nonneg_left hg1 hm']

theorem two_deme_equilibrium_interior {s m : ℝ} (hs : 0 < s)
    (hm0 : 0 < m) (_hm1 : m ≤ 1 / 2) :
    twoDemeEquilibrium s m ∈ Set.Ioo 0 1 := by
  let b := s - 2 * m - m * s
  have hb : b ^ 2 < b ^ 2 + 4 * s * m := by nlinarith [mul_pos hs hm0]
  have hr : |b| < Real.sqrt (b ^ 2 + 4 * s * m) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg b) hb
  have hn : 0 < b + Real.sqrt (b ^ 2 + 4 * s * m) := by
    have h := (abs_lt.mp hr).1
    linarith
  have hbound : 0 < 2 * s - b := by dsimp [b]; nlinarith [mul_pos hs hm0]
  have hb2 : b ^ 2 + 4 * s * m < (2 * s - b)^2 := by
    dsimp [b]
    nlinarith [mul_pos hs hm0, mul_pos (mul_pos hs hs) hm0]
  have hu : Real.sqrt (b ^ 2 + 4 * s * m) < 2 * s - b := by
    have hh := Real.sqrt_lt_sqrt (by positivity : 0 ≤ b ^ 2 + 4 * s * m) hb2
    simpa [Real.sqrt_sq_eq_abs, abs_of_pos hbound] using hh
  change (b + Real.sqrt (b ^ 2 + 4 * s * m)) / (2 * s) ∈ Set.Ioo 0 1
  constructor
  · exact div_pos hn (by positivity)
  · apply (div_lt_one (by positivity)).mpr
    linarith

theorem two_deme_equilibrium_polynomial {s m : ℝ} (hs : 0 < s)
    (hm0 : 0 < m) (_hm1 : m ≤ 1 / 2) :
    s * (twoDemeEquilibrium s m)^2 + (2 * m + m * s - s) * twoDemeEquilibrium s m - m = 0 := by
  have hd : 0 ≤ (s - 2 * m - m * s)^2 + 4 * s * m := by positivity
  have hsq := Real.sq_sqrt hd
  unfold twoDemeEquilibrium
  generalize hr : Real.sqrt ((s - 2 * m - m * s)^2 + 4 * s * m) = v at hsq ⊢
  field_simp [hs.ne']
  nlinarith

theorem two_deme_fixed_order {s m p q : ℝ} (hs : 0 < s)
    (hm0 : 0 < m) (hm1 : m ≤ 1 / 2)
    (hp : p ∈ Set.Icc 0 1) (_hq : q ∈ Set.Icc 0 1)
    (hf : twoDemeFirst s m p q = p) (hg : twoDemeSecond s m p q = q) : q ≤ p := by
  let a := (1 + s) * p / (1 + s * p)
  let b := q / (1 + s * (1 - q))
  have hd : 0 < 1 + s * p := by have := hp.1; positivity
  have ha : p ≤ a := by
    apply (le_div_iff₀ hd).mpr
    have := mul_nonneg hs.le (mul_nonneg hp.1 (sub_nonneg.mpr hp.2))
    nlinarith
  have hf' : (1 - m) * a + m * b = p := by simpa [twoDemeFirst,a,b,mul_div_assoc,mul_assoc] using hf
  have hg' : m * a + (1 - m) * b = q := by
    simpa [twoDemeSecond,a,b,mul_div_assoc,mul_assoc] using hg
  have hab : 0 ≤ a - b := by nlinarith
  have hm : 0 ≤ 1 - 2 * m := by linarith
  nlinarith [mul_nonneg hm hab]

theorem two_deme_fixed_factor {s m p q : ℝ} (hs : 0 < s)
    (hp : p ∈ Set.Icc 0 1) (hq : q ∈ Set.Icc 0 1)
    (hf : twoDemeFirst s m p q = p) (hg : twoDemeSecond s m p q = q) :
    (p + q - 1) * (q - p - s * p * (1 - q)) = 0 := by
  have hd1 : 1 + s * p ≠ 0 := by have := hp.1; positivity
  have hd2 : 1 + s * (1 - q) ≠ 0 := by have := sub_nonneg.mpr hq.2; positivity
  unfold twoDemeFirst at hf
  unfold twoDemeSecond at hg
  field_simp [hd1,hd2] at hf hg
  have h : s * ((p + q - 1) * (q - p - s * p * (1 - q))) = 0 := by nlinarith [hf,hg]
  exact (mul_eq_zero.mp h).resolve_left hs.ne'

theorem two_deme_fixed_anti_or_corner {s m p q : ℝ} (hs : 0 < s)
    (hm0 : 0 < m) (hm1 : m ≤ 1 / 2)
    (hp : p ∈ Set.Icc 0 1) (hq : q ∈ Set.Icc 0 1)
    (hf : twoDemeFirst s m p q = p) (hg : twoDemeSecond s m p q = q) :
    (p = 0 ∧ q = 0) ∨ (p = 1 ∧ q = 1) ∨ p + q = 1 := by
  have ho := two_deme_fixed_order hs hm0 hm1 hp hq hf hg
  rcases mul_eq_zero.mp (two_deme_fixed_factor hs hp hq hf hg) with h | h
  · exact Or.inr (Or.inr (by linarith))
  · have hn := mul_nonneg hp.1 (sub_nonneg.mpr hq.2)
    have he : q = p := by nlinarith [mul_nonneg hs.le hn]
    have hz : p * (1 - q) = 0 := by nlinarith
    rcases mul_eq_zero.mp hz with hz | hz
    · exact Or.inl ⟨hz,by linarith⟩
    · exact Or.inr (Or.inl ⟨by linarith,by linarith⟩)

theorem two_deme_anti_fixed_iff {s m p : ℝ} (hs : 0 < s)
    (hp : p ∈ Set.Icc 0 1) :
    (twoDemeFirst s m p (1 - p) = p ∧ twoDemeSecond s m p (1 - p) = 1 - p) ↔
      s * p ^ 2 + (2 * m + m * s - s) * p - m = 0 := by
  have hd : 1 + s * p ≠ 0 := by have := hp.1; positivity
  unfold twoDemeFirst twoDemeSecond
  simp only [sub_sub_cancel]
  constructor
  · rintro ⟨h,_⟩
    field_simp [hd] at h
    nlinarith
  · intro h
    constructor <;> field_simp [hd] <;> nlinarith

theorem two_deme_equilibrium_unique_nonneg {s m p : ℝ} (hs : 0 < s)
    (hm0 : 0 < m) (hm1 : m ≤ 1 / 2) (hp : 0 ≤ p)
    (hpoly : s * p ^ 2 + (2 * m + m * s - s) * p - m = 0) : p = twoDemeEquilibrium s m := by
  let r := twoDemeEquilibrium s m
  have hr : 0 < r := (two_deme_equilibrium_interior hs hm0 hm1).1
  have hroot := two_deme_equilibrium_polynomial hs hm0 hm1
  change s * r ^ 2 + (2 * m + m * s - s) * r - m = 0 at hroot
  have hfactor : (p - r) * (s * (p + r) + (2 * m + m * s - s)) = 0 := by nlinarith
  rcases mul_eq_zero.mp hfactor with he | he
  · dsimp [r] at he ⊢; linarith
  · have hx : s * p * r = -m := by nlinarith [hroot,hpoly]
    have := mul_nonneg (mul_nonneg hs.le hp) hr.le
    nlinarith

theorem two_deme_symmetric_equilibria {s m p q : ℝ} (hs : 0 < s)
    (hm0 : 0 < m) (hm1 : m ≤ 1 / 2)
    (hp : p ∈ Set.Icc 0 1) (hq : q ∈ Set.Icc 0 1) :
    (twoDemeFirst s m p q = p ∧ twoDemeSecond s m p q = q) ↔
      (p = 0 ∧ q = 0) ∨ (p = 1 ∧ q = 1) ∨
      (p = twoDemeEquilibrium s m ∧ q = 1 - twoDemeEquilibrium s m) := by
  constructor
  · rintro ⟨hf,hg⟩
    rcases two_deme_fixed_anti_or_corner hs hm0 hm1 hp hq hf hg with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · have hq' : q = 1 - p := by linarith
      have hpoly := (two_deme_anti_fixed_iff hs hp).mp (by simpa [← hq'] using And.intro hf hg)
      have he := two_deme_equilibrium_unique_nonneg hs hm0 hm1 hp.1 hpoly
      exact Or.inr (Or.inr ⟨he,by linarith⟩)
  · intro h
    rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · simp [twoDemeFirst,twoDemeSecond]
    · have hd : 1 + s ≠ 0 := by positivity
      simp [twoDemeFirst,twoDemeSecond,hd]
    · exact (two_deme_anti_fixed_iff hs
        ⟨(two_deme_equilibrium_interior hs hm0 hm1).1.le,
         (two_deme_equilibrium_interior hs hm0 hm1).2.le⟩).mpr
        (two_deme_equilibrium_polynomial hs hm0 hm1)

/-- Source: burger2013_migration_selection, sec. 3.1, eq. (3.5), sec. 2.3, eq. (2.9). -/
noncomputable def twoDemeFullMix (s p q : ℝ) : ℝ :=
  ((1 + s) * p / (1 + s * p) + q / (1 + s * (1 - q))) / 2

theorem two_deme_full_mix_mem {s p q : ℝ} (hs : 0 < s)
    (hp : p ∈ Set.Icc 0 1) (hq : q ∈ Set.Icc 0 1) :
    twoDemeFullMix s p q ∈ Set.Icc 0 1 := by
  have h := (two_deme_symmetric_mem hs (by norm_num : (0:ℝ)<1 / 2)
    (by norm_num : (1:ℝ) / 2≤1 / 2) hp hq).1
  have he : twoDemeFirst s (1 / 2) p q = twoDemeFullMix s p q := by
    unfold twoDemeFirst twoDemeFullMix
    ring
  rwa [he] at h

theorem two_deme_full_mix_equilibria {s p q : ℝ} (hs : 0 < s)
    (hp : p ∈ Set.Icc 0 1) (hq : q ∈ Set.Icc 0 1) :
    (twoDemeFullMix s p q = p ∧ twoDemeFullMix s p q = q) ↔
      p = q ∧ (p = 0 ∨ p = 1 / 2 ∨ p = 1) := by
  have hf : twoDemeFirst s (1 / 2) p q = twoDemeFullMix s p q := by
    unfold twoDemeFirst twoDemeFullMix
    ring
  have hg : twoDemeSecond s (1 / 2) p q = twoDemeFullMix s p q := by
    unfold twoDemeSecond twoDemeFullMix
    ring
  have hr : twoDemeEquilibrium s (1 / 2) = 1 / 2 := by
    symm
    exact two_deme_equilibrium_unique_nonneg hs (by norm_num) (by norm_num)
      (by norm_num) (by ring)
  conv_lhs => lhs; rw [← hf]
  conv_lhs => rhs; rw [← hg]
  rw [two_deme_symmetric_equilibria hs (by norm_num) (by norm_num) hp hq,hr]
  constructor
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) <;> norm_num
  · rintro ⟨he,h | h | h⟩
    · exact Or.inl ⟨h,by linarith⟩
    · exact Or.inr (Or.inr ⟨h,by linarith⟩)
    · exact Or.inr (Or.inl ⟨h,by linarith⟩)
end Rhone.Dynamics
