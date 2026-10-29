/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.Recursion.Unique

/-! # Well-posedness: existence, and the sampling probability `q` as a Lean object -/

@[expose] public section

namespace Rhone.LinearAlgebra.Recursion

open Finset Config

variable {KA KB : ℕ} {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}

namespace Config

def bdryVal (πA : Fin KA → F) (πB : Fin KB → F) (ξ : Config KA KB) : F :=
  (∏ i, πA i ^ ξ.a i) * (∏ j, πB j ^ ξ.b j) * ∏ i, ∏ j, (πA i * πB j) ^ ξ.c i j

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem prod_pow_incf {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → F) (i : ι) :
    ∏ k, f k ^ (incf (fun _ => 0) i k) = f i := by
  rw [Finset.prod_eq_single_of_mem i (Finset.mem_univ i)]
  · rw [incf_self]; simp
  · intro k _ hk; rw [incf_of_ne _ hk]; simp

omit [LinearOrder F] [IsStrictOrderedRing F] in
@[simp] theorem bdryVal_zero : bdryVal πA πB (0 : Config KA KB) = 1 := by
  simp [bdryVal]

omit [LinearOrder F] [IsStrictOrderedRing F] in
@[simp] theorem bdryVal_eA (i : Fin KA) : bdryVal πA πB (eA i : Config KA KB) = πA i := by
  simp [bdryVal, eA, prod_pow_incf]

omit [LinearOrder F] [IsStrictOrderedRing F] in
@[simp] theorem bdryVal_eB (j : Fin KB) : bdryVal πA πB (eB j : Config KA KB) = πB j := by
  simp [bdryVal, eB, prod_pow_incf]

omit [LinearOrder F] [IsStrictOrderedRing F] in
@[simp] theorem bdryVal_eC (i : Fin KA) (j : Fin KB) :
    bdryVal πA πB (eC i j : Config KA KB) = πA i * πB j := by
  have h : ∀ i' : Fin KA, (∏ j', (πA i' * πB j') ^ (eC i j : Config KA KB).c i' j')
      = if i' = i then πA i * πB j else 1 := by
    intro i'
    by_cases hi : i' = i
    · subst hi
      have hc : (eC i' j : Config KA KB).c i' = incf (fun _ => 0) j := by
        simp [eC, incC]
      rw [hc, ite_eq_left rfl]
      exact prod_pow_incf (fun j' => πA i' * πB j') j
    · have hc : (eC i j : Config KA KB).c i' = fun _ => 0 := by
        simp [eC, incC, Function.update_of_ne hi]
      rw [hc, ite_eq_right hi]
      simp
  simp only [bdryVal]
  rw [Finset.prod_congr rfl fun i' (_ : i' ∈ Finset.univ) => h i']
  simp [eC]

end Config

structure SolvesUpTo (θA θB ρ : F) (πA : Fin KA → F) (πB : Fin KB → F) (N : ℕ)
    (q : Config KA KB → F) : Prop where
  empty : q 0 = 1
  bdryA : ∀ i, q (Config.eA i) = πA i
  bdryB : ∀ j, q (Config.eB j) = πB j
  bdryC : ∀ i j, q (Config.eC i j) = πA i * πB j
  recursion : ∀ ξ : Config KA KB, 2 ≤ ξ.n → ξ.nA + ξ.nB ≤ N →
    diag θA θB ρ ξ * q ξ = rhs θA θB ρ πA πB q ξ

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem SolvesUpTo.mono {N M : ℕ} (hNM : M ≤ N) {q : Config KA KB → F}
    (h : SolvesUpTo θA θB ρ πA πB N q) : SolvesUpTo θA θB ρ πA πB M q :=
  { empty := h.empty, bdryA := h.bdryA, bdryB := h.bdryB, bdryC := h.bdryC
    recursion := fun ξ hn hl => h.recursion ξ hn (le_trans hl hNM) }

theorem SolvesUpTo.eq_of_le (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) {N : ℕ}
    {q₁ q₂ : Config KA KB → F} (h₁ : SolvesUpTo θA θB ρ πA πB N q₁)
    (h₂ : SolvesUpTo θA θB ρ πA πB N q₂) :
    ∀ ξ : Config KA KB, ξ.nA + ξ.nB ≤ N → q₁ ξ = q₂ ξ := by
  have hbd : ∀ ξ : Config KA KB, ξ.n ≤ 1 → ξ.nA + ξ.nB ≤ N → q₁ ξ - q₂ ξ = 0 := by
    intro ξ hn _
    rcases Nat.lt_or_ge ξ.n 1 with h | h
    · have hz : ξ = 0 := ξ.eq_zero_of_n_eq_zero (by omega)
      subst hz; rw [h₁.empty, h₂.empty, sub_self]
    · rcases ξ.exists_e_of_n_eq_one (by omega) with ⟨i, rfl⟩ | ⟨j, rfl⟩ | ⟨i, j, rfl⟩
      · rw [h₁.bdryA, h₂.bdryA, sub_self]
      · rw [h₁.bdryB, h₂.bdryB, sub_self]
      · rw [h₁.bdryC, h₂.bdryC, sub_self]
  have hrec : ∀ ξ : Config KA KB, 2 ≤ ξ.n → ξ.nA + ξ.nB ≤ N →
      diag θA θB ρ ξ * (q₁ ξ - q₂ ξ) = rhs θA θB ρ πA πB (fun η => q₁ η - q₂ η) ξ := by
    intro ξ hn hl
    rw [rhs_sub, mul_sub, h₁.recursion ξ hn hl, h₂.recursion ξ hn hl]
  intro ξ hξ
  have := homogeneous_eq_zero_le (πA := πA) (πB := πB) hθA hθB hρ hbd hrec ξ hξ
  linarith [this]

noncomputable instance instFintypeLevel (N : ℕ) :
    Fintype ↥{ξ : Config KA KB | ξ.nA + ξ.nB = N} := (Config.finite_level N).fintype

def extZero (N : ℕ) (v : ↥{ξ : Config KA KB | ξ.nA + ξ.nB = N} → F) : Config KA KB → F :=
  fun η => if h : η.nA + η.nB = N then v ⟨η, h⟩ else 0

def offLevel (N : ℕ) (g : Config KA KB → F) : Config KA KB → F :=
  fun η => if η.nA + η.nB = N then 0 else g η

def glue (N : ℕ) (g : Config KA KB → F)
    (v : ↥{ξ : Config KA KB | ξ.nA + ξ.nB = N} → F) : Config KA KB → F :=
  fun η => if h : η.nA + η.nB = N then v ⟨η, h⟩ else g η

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem glue_eq_add (N : ℕ) (g : Config KA KB → F)
    (v : ↥{ξ : Config KA KB | ξ.nA + ξ.nB = N} → F) :
    glue N g v = fun η => extZero N v η + offLevel N g η := by
  funext η
  simp only [glue, extZero, offLevel]
  by_cases h : η.nA + η.nB = N <;> simp [h]

noncomputable def blockOp (θA θB ρ : F) (πA : Fin KA → F) (πB : Fin KB → F) (N : ℕ) :
    (↥{ξ : Config KA KB | ξ.nA + ξ.nB = N} → F) →ₗ[F]
      (↥{ξ : Config KA KB | ξ.nA + ξ.nB = N} → F) where
  toFun v := fun ξ =>
    if 2 ≤ (ξ : Config KA KB).n
      then diag θA θB ρ (ξ : Config KA KB) * v ξ
        - rhs θA θB ρ πA πB (extZero N v) (ξ : Config KA KB)
      else v ξ
  map_add' v w := by
    have hext : extZero N (v + w) = fun η => extZero N v η + extZero N w η := by
      funext η; simp only [extZero]; split_ifs <;> simp
    funext ξ
    simp only [Pi.add_apply, hext, rhs_add]
    split_ifs with hn
    · ring
    · rfl
  map_smul' c v := by
    have hext : extZero N (c • v) = fun η => c * extZero N v η := by
      funext η; simp only [extZero]; split_ifs <;> simp
    funext ξ
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, hext, rhs_smul]
    split_ifs with hn
    · ring
    · rfl

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem blockOp_apply (N : ℕ) (v : ↥{ξ : Config KA KB | ξ.nA + ξ.nB = N} → F)
    (ξ : ↥{ξ : Config KA KB | ξ.nA + ξ.nB = N}) :
    blockOp θA θB ρ πA πB N v ξ =
      if 2 ≤ (ξ : Config KA KB).n
        then diag θA θB ρ (ξ : Config KA KB) * v ξ
          - rhs θA θB ρ πA πB (extZero N v) (ξ : Config KA KB)
        else v ξ := rfl

theorem blockOp_injective (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (N : ℕ) :
    Function.Injective (blockOp θA θB ρ πA πB N) := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  have hv' : ∀ (η : Config KA KB) (hη : η.nA + η.nB = N),
      (if 2 ≤ η.n
        then diag θA θB ρ η * v ⟨η, hη⟩ - rhs θA θB ρ πA πB (extZero N v) η
        else v ⟨η, hη⟩) = 0 := by
    intro η hη
    exact congrFun hv ⟨η, hη⟩
  have hz : ∀ η : Config KA KB, η.nA + η.nB ≠ N → extZero N v η = 0 := by
    intro η hη; simp [extZero, hη]
  have hon : ∀ (η : Config KA KB) (h : η.nA + η.nB = N), extZero N v η = v ⟨η, h⟩ := by
    intro η h; simp [extZero, h]
  have hbd : ∀ ξ : Config KA KB, ξ.n ≤ 1 → ξ.nA + ξ.nB ≤ N → extZero N v ξ = 0 := by
    intro ξ hn _
    by_cases hl : ξ.nA + ξ.nB = N
    · have h3 := hv' ξ hl
      rw [ite_eq_right (show ¬ (2 ≤ ξ.n) by omega)] at h3
      rw [hon ξ hl]; exact h3
    · exact hz ξ hl
  have hrec : ∀ ξ : Config KA KB, 2 ≤ ξ.n → ξ.nA + ξ.nB ≤ N →
      diag θA θB ρ ξ * extZero N v ξ = rhs θA θB ρ πA πB (extZero N v) ξ := by
    intro ξ hn hl
    by_cases hlev : ξ.nA + ξ.nB = N
    · have h2 := hv' ξ hlev
      rw [ite_eq_left hn] at h2
      rw [hon ξ hlev]
      linarith [h2]
    · have hlt : ξ.nA + ξ.nB < N := by omega
      have hb : ∀ η : Config KA KB, η.nA ≤ ξ.nA → η.nB ≤ ξ.nB → extZero N v η = 0 :=
        fun η h1 h2 => hz η (by omega)
      rw [hz ξ (by omega), mul_zero,
        rhs_congr θA θB ρ πA πB (q₂ := fun _ => (0 : F)) ξ hb, rhs_zero]
  have key := homogeneous_eq_zero_le (πA := πA) (πB := πB) hθA hθB hρ hbd hrec
  funext ξ
  have := key ξ (le_of_eq ξ.2)
  rw [hon ξ ξ.2] at this
  simpa using this

theorem exists_glue (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (N : ℕ) (g : Config KA KB → F) :
    ∃ u : Config KA KB → F,
      (∀ η : Config KA KB, η.nA + η.nB ≠ N → u η = g η) ∧
      (∀ ξ : Config KA KB, ξ.nA + ξ.nB = N → ξ.n ≤ 1 → u ξ = Config.bdryVal πA πB ξ) ∧
      (∀ ξ : Config KA KB, ξ.nA + ξ.nB = N → 2 ≤ ξ.n →
        diag θA θB ρ ξ * u ξ = rhs θA θB ρ πA πB u ξ) := by
  obtain ⟨v, hv⟩ := (LinearMap.injective_iff_surjective.mp
      (blockOp_injective (πA := πA) (πB := πB) hθA hθB hρ N))
    (fun ξ => if 2 ≤ (ξ : Config KA KB).n
      then rhs θA θB ρ πA πB (offLevel N g) (ξ : Config KA KB)
      else Config.bdryVal πA πB (ξ : Config KA KB))
  have hv' : ∀ (η : Config KA KB) (hη : η.nA + η.nB = N),
      (if 2 ≤ η.n
        then diag θA θB ρ η * v ⟨η, hη⟩ - rhs θA θB ρ πA πB (extZero N v) η
        else v ⟨η, hη⟩)
      = (if 2 ≤ η.n then rhs θA θB ρ πA πB (offLevel N g) η
          else Config.bdryVal πA πB η) := by
    intro η hη
    exact congrFun hv ⟨η, hη⟩
  refine ⟨glue N g v, fun η hη => by simp [glue, hη], ?_, ?_⟩
  · intro ξ hlev hn
    have h2 := hv' ξ hlev
    rw [ite_eq_right (show ¬ (2 ≤ ξ.n) by omega), ite_eq_right (show ¬ (2 ≤ ξ.n) by omega)] at h2
    simpa [glue, hlev] using h2
  · intro ξ hlev hn
    have h2 := hv' ξ hlev
    rw [ite_eq_left hn, ite_eq_left hn] at h2
    have hu : glue N g v ξ = v ⟨ξ, hlev⟩ := by simp [glue, hlev]
    rw [hu, glue_eq_add, rhs_add]
    linarith [h2]

theorem exists_solvesUpTo (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (N : ℕ) :
    ∃ q : Config KA KB → F, SolvesUpTo θA θB ρ πA πB N q := by
  induction N with
  | zero =>
    refine ⟨Config.bdryVal πA πB, ?_, ?_, ?_, ?_, ?_⟩
    · exact Config.bdryVal_zero
    · exact fun i => Config.bdryVal_eA i
    · exact fun j => Config.bdryVal_eB j
    · exact fun i j => Config.bdryVal_eC i j
    · intro ξ hn hl
      exfalso
      have := ξ.n_add_t
      omega
  | succ N ih =>
    obtain ⟨g, hg⟩ := ih
    obtain ⟨u, hoff, hbdry, hrec⟩ :=
      exists_glue (πA := πA) (πB := πB) hθA hθB hρ (N + 1) g
    have hlow : ∀ η : Config KA KB, η.nA + η.nB ≤ N → u η = g η :=
      fun η hη => hoff η (by omega)
    have hb : ∀ ξ : Config KA KB, ξ.n ≤ 1 → u ξ = Config.bdryVal πA πB ξ := by
      intro ξ hn
      by_cases hlev : ξ.nA + ξ.nB = N + 1
      · exact hbdry ξ hlev hn
      · rw [hoff ξ hlev]
        rcases Nat.lt_or_ge ξ.n 1 with h | h
        · have hz : ξ = 0 := ξ.eq_zero_of_n_eq_zero (by omega)
          subst hz; rw [hg.empty, Config.bdryVal_zero]
        · rcases ξ.exists_e_of_n_eq_one (by omega) with ⟨i, rfl⟩ | ⟨j, rfl⟩ | ⟨i, j, rfl⟩
          · rw [hg.bdryA, Config.bdryVal_eA]
          · rw [hg.bdryB, Config.bdryVal_eB]
          · rw [hg.bdryC, Config.bdryVal_eC]
    refine ⟨u, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hb 0 (by simp), Config.bdryVal_zero]
    · exact fun i => by rw [hb _ (by simp), Config.bdryVal_eA]
    · exact fun j => by rw [hb _ (by simp), Config.bdryVal_eB]
    · exact fun i j => by rw [hb _ (by simp), Config.bdryVal_eC]
    · intro ξ hn hl
      by_cases hlev : ξ.nA + ξ.nB = N + 1
      · exact hrec ξ hlev hn
      · have hle : ξ.nA + ξ.nB ≤ N := by omega
        have hcongr : rhs θA θB ρ πA πB u ξ = rhs θA θB ρ πA πB g ξ :=
          rhs_congr θA θB ρ πA πB ξ fun η h1 h2 => hlow η (by omega)
        rw [hlow ξ hle, hcongr]
        exact hg.recursion ξ hn hle

noncomputable def approx (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (N : ℕ) :
    Config KA KB → F :=
  Classical.choose (exists_solvesUpTo (πA := πA) (πB := πB) hθA hθB hρ N)

theorem approx_spec (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (N : ℕ) :
    SolvesUpTo θA θB ρ πA πB N (approx (πA := πA) (πB := πB) hθA hθB hρ N) :=
  Classical.choose_spec (exists_solvesUpTo (πA := πA) (πB := πB) hθA hθB hρ N)

theorem approx_coherent (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) {M N : ℕ} (hMN : M ≤ N)
    (ξ : Config KA KB) (hξ : ξ.nA + ξ.nB ≤ M) :
    approx (πA := πA) (πB := πB) hθA hθB hρ M ξ
      = approx (πA := πA) (πB := πB) hθA hθB hρ N ξ :=
  SolvesUpTo.eq_of_le hθA hθB hρ (approx_spec hθA hθB hρ M)
    ((approx_spec hθA hθB hρ N).mono hMN) ξ hξ

theorem exists_isSolution (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) :
    ∃ q : Config KA KB → F, IsSolution θA θB ρ πA πB q := by
  refine ⟨fun ξ => approx (πA := πA) (πB := πB) hθA hθB hρ (ξ.nA + ξ.nB) ξ, ?_, ?_, ?_, ?_, ?_⟩
  · exact (approx_spec hθA hθB hρ _).empty
  · exact fun i => (approx_spec hθA hθB hρ _).bdryA i
  · exact fun j => (approx_spec hθA hθB hρ _).bdryB j
  · exact fun i j => (approx_spec hθA hθB hρ _).bdryC i j
  · intro ξ hn
    have hcongr : rhs θA θB ρ πA πB
        (fun η => approx (πA := πA) (πB := πB) hθA hθB hρ (η.nA + η.nB) η) ξ
        = rhs θA θB ρ πA πB (approx (πA := πA) (πB := πB) hθA hθB hρ (ξ.nA + ξ.nB)) ξ :=
      rhs_congr θA θB ρ πA πB ξ fun η h1 h2 =>
        approx_coherent hθA hθB hρ (by omega) η le_rfl
    rw [hcongr]
    exact (approx_spec hθA hθB hρ _).recursion ξ hn le_rfl

noncomputable def q (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) : Config KA KB → F :=
  Classical.choose (exists_isSolution (πA := πA) (πB := πB) hθA hθB hρ)

theorem q_isSolution (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) :
    IsSolution θA θB ρ πA πB (q (πA := πA) (πB := πB) hθA hθB hρ) :=
  Classical.choose_spec (exists_isSolution (πA := πA) (πB := πB) hθA hθB hρ)

theorem q_unique (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) {q' : Config KA KB → F}
    (h : IsSolution θA θB ρ πA πB q') : q' = q (πA := πA) (πB := πB) hθA hθB hρ :=
  IsSolution.unique hθA hθB hρ h (q_isSolution hθA hθB hρ)

end Rhone.LinearAlgebra.Recursion
