/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.AbsorptionProb

/-! # Absorption into a closed set of states -/

@[expose] public section

namespace Rhone.MarkovChain.FinChain

open Finset Filter Topology

variable {S : Type*} [Fintype S] [DecidableEq S] (C : FinChain S)

def IsClosedSet (A : Finset S) : Prop := ∀ x ∈ A, ∀ y, y ∉ A → C.P x y = 0

noncomputable def enterProb (A : Finset S) (x : S) : ℝ := ⨆ n, ∑ a ∈ A, C.stepN n x a

variable {C} {A B : Finset S}

omit [DecidableEq S] in
theorem IsAbsorbingSet.isClosedSet (hA : C.IsAbsorbingSet A) : C.IsClosedSet A := by
  classical
  intro x hx y hy
  rw [(hA x hx).P_apply]
  exact ite_eq_right fun h : x = y => hy (h ▸ hx)

omit [DecidableEq S] in
theorem isClosedSet_univ (C : FinChain S) : C.IsClosedSet univ :=
  fun _ _ y hy => absurd (mem_univ y) hy

theorem IsClosedSet.union (hA : C.IsClosedSet A) (hB : C.IsClosedSet B) :
    C.IsClosedSet (A ∪ B) := by
  intro x hx y hy
  rw [mem_union, not_or] at hy
  rcases mem_union.1 hx with h | h
  · exact hA x h y hy.1
  · exact hB x h y hy.2

theorem IsClosedSet.biUnion {ι : Type*} (s : Finset ι) (A : ι → Finset S)
    (h : ∀ i ∈ s, C.IsClosedSet (A i)) : C.IsClosedSet (s.biUnion A) := by
  intro x hx y hy
  obtain ⟨i, hi, hxi⟩ := mem_biUnion.1 hx
  exact h i hi x hxi y fun hyi => hy (mem_biUnion.2 ⟨i, hi, hyi⟩)

omit [DecidableEq S] in
theorem IsClosedSet.sum_P (hA : C.IsClosedSet A) {x : S} (hx : x ∈ A) :
    ∑ y ∈ A, C.P x y = 1 := by
  classical
  have h := C.row_sum x
  rw [← Finset.sum_add_sum_compl A] at h
  have h0 : ∑ y ∈ Aᶜ, C.P x y = 0 :=
    Finset.sum_eq_zero fun y hy => hA x hx y (mem_compl.1 hy)
  linarith

theorem IsClosedSet.stepN_eq_zero (hA : C.IsClosedSet A) (n : ℕ) {x : S} (hx : x ∈ A) {y : S}
    (hy : y ∉ A) : C.stepN n x y = 0 := by
  induction n generalizing x with
  | zero =>
    rw [stepN_zero, Matrix.one_apply_ne]
    rintro rfl
    exact hy hx
  | succ n ih =>
    rw [stepN_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun z _ => ?_
    by_cases hz : z ∈ A
    · rw [ih hz, mul_zero]
    · rw [hA x hx z hz, zero_mul]

omit [DecidableEq S] in
theorem IsClosedSet.expect_eq_of_const (hA : C.IsClosedSet A) {h : S → ℝ} {c : ℝ}
    (hc : ∀ a ∈ A, h a = c) {x : S} (hx : x ∈ A) : C.expect h x = c := by
  classical
  rw [expect_apply, ← Finset.sum_add_sum_compl A]
  have h1 : ∑ y ∈ A, C.P x y * h y = c := by
    rw [Finset.sum_congr rfl fun y hy => by rw [hc y hy], ← Finset.sum_mul, hA.sum_P hx, one_mul]
  have h2 : ∑ y ∈ Aᶜ, C.P x y * h y = 0 :=
    Finset.sum_eq_zero fun y hy => by rw [hA x hx y (mem_compl.1 hy), zero_mul]
  rw [h1, h2, add_zero]

theorem IsClosedSet.survival_of_mem (hA : C.IsClosedSet A) {a : S} (ha : a ∈ A) (n : ℕ) :
    C.survival A n a = 0 :=
  Finset.sum_eq_zero fun _ hy => hA.stepN_eq_zero n ha (mem_compl.1 hy)

theorem IsClosedSet.survival_add (hA : C.IsClosedSet A) (m n : ℕ) (x : S) :
    C.survival A (m + n) x = ∑ z ∈ Aᶜ, C.stepN m x z * C.survival A n z := by
  have h1 : C.survival A (m + n) x = ∑ z, C.stepN m x z * C.survival A n z := by
    simp only [survival, stepN_add_apply, Finset.mul_sum]
    exact Finset.sum_comm
  rw [h1, ← Finset.sum_add_sum_compl A]
  have : ∑ z ∈ A, C.stepN m x z * C.survival A n z = 0 :=
    Finset.sum_eq_zero fun z hz => by rw [hA.survival_of_mem hz, mul_zero]
  rw [this, zero_add]

theorem IsClosedSet.survival_antitone (hA : C.IsClosedSet A) (x : S) :
    Antitone fun n => C.survival A n x := by
  intro m n hmn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  change C.survival A (m + k) x ≤ C.survival A m x
  rw [hA.survival_add]
  refine Finset.sum_le_sum fun z _ => ?_
  exact mul_le_of_le_one_right (C.stepN_nonneg m x z) (C.survival_le_one A k z)

theorem IsClosedSet.exists_uniform_survival_bound (hA : C.IsClosedSet A) (hR : C.Reaches A) :
    ∃ m : ℕ, 0 < m ∧ ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∀ x, C.survival A m x ≤ c := by
  choose N hN using hR.exists_survival_lt_one
  set m : ℕ := 1 + ∑ x, N x with hm
  have hlt : ∀ x, C.survival A m x < 1 := by
    intro x
    have hle : N x ≤ m := by
      have := Finset.single_le_sum (f := N) (fun _ _ => Nat.zero_le _) (mem_univ x)
      omega
    exact lt_of_le_of_lt (hA.survival_antitone x hle) (hN x)
  refine ⟨m, by omega, ?_⟩
  rcases isEmpty_or_nonempty S with hS | hS
  · exact ⟨0, le_rfl, zero_lt_one, fun x => (hS.false x).elim⟩
  · obtain ⟨x0, -, hmax⟩ := Finset.exists_max_image univ (fun x => C.survival A m x)
      ⟨hS.some, mem_univ _⟩
    exact ⟨C.survival A m x0, C.survival_nonneg A m x0, hlt x0, fun x => hmax x (mem_univ x)⟩

theorem IsClosedSet.survival_le_pow (hA : C.IsClosedSet A) {m : ℕ} {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ x, C.survival A m x ≤ c) (q r : ℕ) (x : S) :
    C.survival A (m * q + r) x ≤ c ^ q := by
  induction q generalizing x with
  | zero => simpa using C.survival_le_one A r x
  | succ q ih =>
    have e : m * (q + 1) + r = m + (m * q + r) := by ring
    rw [e, hA.survival_add]
    calc ∑ z ∈ Aᶜ, C.stepN m x z * C.survival A (m * q + r) z
        ≤ ∑ z ∈ Aᶜ, C.stepN m x z * c ^ q :=
          Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (ih z) (C.stepN_nonneg m x z)
      _ = C.survival A m x * c ^ q := by rw [survival, Finset.sum_mul]
      _ ≤ c * c ^ q := mul_le_mul_of_nonneg_right (hc x) (pow_nonneg hc0 q)
      _ = c ^ (q + 1) := by ring

theorem IsClosedSet.summable_survival (hA : C.IsClosedSet A) (hR : C.Reaches A) (x : S) :
    Summable fun n => C.survival A n x := by
  obtain ⟨m, hm, c, hc0, hc1, hc⟩ := hA.exists_uniform_survival_bound hR
  have hgeom : ∀ q : ℕ, ∑ j ∈ range q, c ^ j ≤ 1 / (1 - c) := by
    intro q
    rw [le_div_iff₀ (by linarith), geom_sum_mul_neg]
    have := pow_nonneg hc0 q
    linarith
  have hblock : ∀ q : ℕ, ∑ i ∈ range (m * q), C.survival A i x ≤ m * ∑ j ∈ range q, c ^ j := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, Finset.sum_range_succ, mul_add]
      refine add_le_add ih ?_
      calc ∑ r ∈ range m, C.survival A (m * q + r) x
          ≤ ∑ _r ∈ range m, c ^ q :=
            Finset.sum_le_sum fun r _ => hA.survival_le_pow hc0 hc q r x
        _ = m * c ^ q := by simp
  refine summable_of_sum_range_le (c := m * (1 / (1 - c)))
    (fun n => C.survival_nonneg A n x) fun n => ?_
  calc ∑ i ∈ range n, C.survival A i x
      ≤ ∑ i ∈ range (m * n), C.survival A i x :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_mono (Nat.le_mul_of_pos_left n hm))
          fun i _ _ => C.survival_nonneg A i x
    _ ≤ m * ∑ j ∈ range n, c ^ j := hblock n
    _ ≤ m * (1 / (1 - c)) := mul_le_mul_of_nonneg_left (hgeom n) (Nat.cast_nonneg m)

theorem IsClosedSet.tendsto_survival (hA : C.IsClosedSet A) (hR : C.Reaches A) (x : S) :
    Tendsto (fun n => C.survival A n x) atTop (𝓝 0) :=
  (hA.summable_survival hR x).tendsto_atTop_zero

omit [DecidableEq S] in
theorem IsClosedSet.isHarmonic_of_harmonicOff (hA : C.IsClosedSet A) {g : S → ℝ}
    (hg : ∀ x, x ∉ A → C.expect g x = g x) (h0 : ∀ a ∈ A, g a = 0) : C.IsHarmonic g := by
  funext x
  by_cases hx : x ∈ A
  · rw [hA.expect_eq_of_const h0 hx, h0 x hx]
  · exact hg x hx

theorem IsClosedSet.eq_zero_of_harmonicOff (hA : C.IsClosedSet A) (hR : C.Reaches A)
    {g : S → ℝ} (hg : ∀ x, x ∉ A → C.expect g x = g x) (h0 : ∀ a ∈ A, g a = 0) : g = 0 := by
  have hh := hA.isHarmonic_of_harmonicOff hg h0
  funext x
  have hM : ∀ y, |g y| ≤ ∑ z, |g z| := fun y =>
    Finset.single_le_sum (f := fun z => |g z|) (fun z _ => abs_nonneg _) (mem_univ y)
  have hbound : ∀ n, |g x| ≤ (∑ z, |g z|) * C.survival A n x := by
    intro n
    have := C.abs_expectN_le_survival h0 hM n x
    rwa [hh.expectN_eq n] at this
  have hlim : Tendsto (fun n => (∑ z, |g z|) * C.survival A n x) atTop (𝓝 0) := by
    simpa using (hA.tendsto_survival hR x).const_mul (∑ z, |g z|)
  have : |g x| ≤ 0 := ge_of_tendsto' hlim hbound
  exact abs_nonpos_iff.1 this

theorem IsClosedSet.eq_of_harmonicOff (hA : C.IsClosedSet A) (hR : C.Reaches A) {g h : S → ℝ}
    (hg : ∀ x, x ∉ A → C.expect g x = g x) (hh : ∀ x, x ∉ A → C.expect h x = h x)
    (hgh : ∀ a ∈ A, g a = h a) : g = h := by
  have := hA.eq_zero_of_harmonicOff hR (g := g - h)
    (fun x hx => by rw [expect_sub_fun, Pi.sub_apply, hg x hx, hh x hx, Pi.sub_apply])
    fun a ha => by simp [hgh a ha]
  exact sub_eq_zero.1 this

theorem IsClosedSet.sum_stepN_mono (hA : C.IsClosedSet A) (x : S) :
    Monotone fun n => ∑ a ∈ A, C.stepN n x a := by
  intro m n hmn
  have h1 := C.survival_add_sum A m x
  have h2 := C.survival_add_sum A n x
  have h3 := hA.survival_antitone x hmn
  simp only at h3 ⊢
  linarith

theorem bddAbove_sum_stepN (C : FinChain S) (A : Finset S) (x : S) :
    BddAbove (Set.range fun n => ∑ a ∈ A, C.stepN n x a) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨n, rfl⟩
  have h := C.survival_add_sum A n x
  have := C.survival_nonneg A n x
  simp only
  linarith

theorem IsClosedSet.tendsto_enterProb (hA : C.IsClosedSet A) (x : S) :
    Tendsto (fun n => ∑ a ∈ A, C.stepN n x a) atTop (𝓝 (C.enterProb A x)) :=
  tendsto_atTop_ciSup (hA.sum_stepN_mono x) (C.bddAbove_sum_stepN A x)

theorem enterProb_nonneg (C : FinChain S) (A : Finset S) (x : S) : 0 ≤ C.enterProb A x :=
  le_ciSup_of_le (C.bddAbove_sum_stepN A x) 0
    (Finset.sum_nonneg fun a _ => C.stepN_nonneg 0 x a)

theorem enterProb_le_one (C : FinChain S) (A : Finset S) (x : S) : C.enterProb A x ≤ 1 :=
  ciSup_le fun n => by
    have h := C.survival_add_sum A n x
    have := C.survival_nonneg A n x
    linarith

theorem enterProb_singleton (C : FinChain S) (a : S) : C.enterProb {a} = C.absorbProb a := by
  funext x
  simp [enterProb, absorbProb]

theorem IsClosedSet.enterProb_isHarmonic (hA : C.IsClosedSet A) :
    C.IsHarmonic (C.enterProb A) := by
  funext x
  have h1 : Tendsto (fun n => ∑ y, C.P x y * ∑ a ∈ A, C.stepN n y a) atTop
      (𝓝 (∑ y, C.P x y * C.enterProb A y)) :=
    tendsto_finsetSum _ fun y _ => (hA.tendsto_enterProb y).const_mul _
  have h2 : Tendsto (fun n => ∑ y, C.P x y * ∑ a ∈ A, C.stepN n y a) atTop
      (𝓝 (C.enterProb A x)) := by
    have := (tendsto_add_atTop_iff_nat 1).2 (hA.tendsto_enterProb x)
    refine this.congr fun n => ?_
    simp only [stepN_succ, Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_comm
  exact tendsto_nhds_unique h1 h2

theorem IsClosedSet.enterProb_of_mem (hA : C.IsClosedSet A) {x : S} (hx : x ∈ A) :
    C.enterProb A x = 1 := by
  have h : ∀ n, ∑ a ∈ A, C.stepN n x a = 1 := fun n => by
    have h1 := C.survival_add_sum A n x
    rw [hA.survival_of_mem hx, zero_add] at h1
    exact h1
  simp [enterProb, h]

theorem IsClosedSet.enterProb_of_mem_of_disjoint (hB : C.IsClosedSet B) (hAB : Disjoint A B)
    {x : S} (hx : x ∈ B) : C.enterProb A x = 0 := by
  have h : ∀ n, ∑ a ∈ A, C.stepN n x a = 0 := fun n =>
    Finset.sum_eq_zero fun a ha => hB.stepN_eq_zero n hx (Finset.disjoint_left.1 hAB ha)
  simp [enterProb, h]

theorem IsClosedSet.enterProb_eq_one (hA : C.IsClosedSet A) (hR : C.Reaches A) (x : S) :
    C.enterProb A x = 1 := by
  have h2 : Tendsto (fun n => ∑ a ∈ A, C.stepN n x a) atTop (𝓝 1) := by
    have := (hA.tendsto_survival hR x).const_sub 1
    rw [sub_zero] at this
    refine this.congr fun n => ?_
    have := C.survival_add_sum A n x
    linarith
  exact tendsto_nhds_unique (hA.tendsto_enterProb x) h2

theorem enterProb_eq_of_harmonicOff {A₁ A₀ : Finset S} (hA₁ : C.IsClosedSet A₁)
    (hA₀ : C.IsClosedSet A₀) (hd : Disjoint A₁ A₀) (hR : C.Reaches (A₁ ∪ A₀)) {h : S → ℝ}
    (hh : ∀ x, x ∉ A₁ ∪ A₀ → C.expect h x = h x) (h1 : ∀ a ∈ A₁, h a = 1)
    (h0 : ∀ a ∈ A₀, h a = 0) : C.enterProb A₁ = h := by
  refine (hA₁.union hA₀).eq_of_harmonicOff hR
    (fun x _ => congrFun hA₁.enterProb_isHarmonic x) hh fun a ha => ?_
  rcases mem_union.1 ha with ha | ha
  · rw [hA₁.enterProb_of_mem ha, h1 a ha]
  · rw [hA₀.enterProb_of_mem_of_disjoint hd ha, h0 a ha]

theorem enterProb_add_enterProb {A₁ A₀ : Finset S} (hA₁ : C.IsClosedSet A₁)
    (hA₀ : C.IsClosedSet A₀) (hd : Disjoint A₁ A₀) (hR : C.Reaches (A₁ ∪ A₀)) (x : S) :
    C.enterProb A₁ x + C.enterProb A₀ x = 1 := by
  have h1 := (hA₁.tendsto_enterProb x).add (hA₀.tendsto_enterProb x)
  have h2 := (hA₁.union hA₀).tendsto_enterProb x
  rw [(hA₁.union hA₀).enterProb_eq_one hR x] at h2
  refine tendsto_nhds_unique h1 (h2.congr fun n => ?_)
  rw [Finset.sum_union hd]

theorem IsClosedSet.summable_potential (hA : C.IsClosedSet A) (hR : C.Reaches A) (c : S → ℝ)
    (x : S) : Summable fun n => ∑ y ∈ Aᶜ, C.stepN n x y * c y := by
  refine Summable.of_norm_bounded ((hA.summable_survival hR x).mul_left (∑ z, |c z|))
    fun n => ?_
  rw [Real.norm_eq_abs, survival, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ => ?_)
  rw [abs_mul, abs_of_nonneg (C.stepN_nonneg n x y), mul_comm]
  exact mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (f := fun z => |c z|) (fun z _ => abs_nonneg _) (mem_univ y))
    (C.stepN_nonneg n x y)

theorem IsClosedSet.potential_of_mem (hA : C.IsClosedSet A) {a : S} (ha : a ∈ A) (c : S → ℝ) :
    C.potential A c a = 0 := by
  have : ∀ n, ∑ y ∈ Aᶜ, C.stepN n a y * c y = 0 := fun n =>
    Finset.sum_eq_zero fun y hy => by rw [hA.stepN_eq_zero n ha (mem_compl.1 hy), zero_mul]
  simp [potential, this]

theorem IsClosedSet.potential_step (hA : C.IsClosedSet A) (hR : C.Reaches A) (c : S → ℝ)
    (x : S) :
    C.potential A c x = (if x ∈ A then 0 else c x) + ∑ y, C.P x y * C.potential A c y := by
  have hs := hA.summable_potential hR c
  have h0 : ∑ y ∈ Aᶜ, C.stepN 0 x y * c y = if x ∈ A then 0 else c x := by
    simp [stepN_zero, Matrix.one_apply]
  have hsucc : ∀ n, ∑ y ∈ Aᶜ, C.stepN (n + 1) x y * c y =
      ∑ z, C.P x z * ∑ y ∈ Aᶜ, C.stepN n z y * c y := by
    intro n
    simp only [stepN_succ, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm
  rw [potential, (hs x).tsum_eq_zero_add, h0]
  congr 1
  simp only [hsucc]
  rw [Summable.tsum_finsetSum fun z _ => (hs z).mul_left _]
  exact Finset.sum_congr rfl fun z _ => tsum_mul_left

theorem IsClosedSet.eq_potential_of_step (hA : C.IsClosedSet A) (hR : C.Reaches A)
    {c u : S → ℝ} (h0 : ∀ a ∈ A, u a = 0)
    (hstep : ∀ x, x ∉ A → u x = c x + ∑ y, C.P x y * u y) : u = C.potential A c := by
  have := hA.eq_zero_of_harmonicOff hR (g := u - C.potential A c) (fun x hx => by
      rw [expect_apply]
      simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
      have h1 := hstep x hx
      have h2 := hA.potential_step hR c x
      simp only [hx, ↓reduceIte] at h2
      linarith)
    fun a ha => by simp [h0 a ha, hA.potential_of_mem ha]
  exact sub_eq_zero.1 this

theorem IsClosedSet.absorbTime_of_mem (hA : C.IsClosedSet A) {a : S} (ha : a ∈ A) :
    C.absorbTime A a = 0 := by
  rw [absorbTime_eq_potential, hA.potential_of_mem ha]

theorem IsClosedSet.absorbTime_step (hA : C.IsClosedSet A) (hR : C.Reaches A) {x : S}
    (hx : x ∉ A) : C.absorbTime A x = 1 + ∑ y, C.P x y * C.absorbTime A y := by
  rw [absorbTime_eq_potential, hA.potential_step hR]
  simp only [hx, ↓reduceIte]

theorem IsClosedSet.eq_absorbTime_of_step (hA : C.IsClosedSet A) (hR : C.Reaches A)
    {t : S → ℝ} (h0 : ∀ a ∈ A, t a = 0) (hstep : ∀ x, x ∉ A → t x = 1 + ∑ y, C.P x y * t y) :
    t = C.absorbTime A := by
  rw [absorbTime_eq_potential]
  exact hA.eq_potential_of_step hR h0 hstep

end Rhone.MarkovChain.FinChain
