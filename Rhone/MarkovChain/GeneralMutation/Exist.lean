/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.GeneralMutation.Unique

/-! # Well-posedness of the general-mutation-matrix system: existence, and `qGen` -/

@[expose] public section

namespace Rhone.MarkovChain.GeneralMutation

open Finset LinearAlgebra.Recursion

variable {KA KB : ℕ} {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {νA : Fin KA → F} {νB : Fin KB → F}
variable {PA : Fin KA → Fin KA → F} {PB : Fin KB → Fin KB → F}

structure SolvesUpToGen (θA θB ρ : F) (νA : Fin KA → F) (νB : Fin KB → F)
    (PA : Fin KA → Fin KA → F) (PB : Fin KB → Fin KB → F) (N : ℕ)
    (q : Config KA KB → F) : Prop where
  empty : q 0 = 1
  bdryA : ∀ i, q (Config.eA i) = νA i
  bdryB : ∀ j, q (Config.eB j) = νB j
  bdryC : ∀ i j, q (Config.eC i j) = νA i * νB j
  recursion : ∀ ξ : Config KA KB, 2 ≤ ξ.n → ξ.nA + ξ.nB ≤ N →
    diag θA θB ρ ξ * q ξ = rhsGen θA θB ρ PA PB q ξ

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem SolvesUpToGen.mono {N Mlev : ℕ} (hNM : Mlev ≤ N) {q : Config KA KB → F}
    (h : SolvesUpToGen θA θB ρ νA νB PA PB N q) : SolvesUpToGen θA θB ρ νA νB PA PB Mlev q :=
  { empty := h.empty, bdryA := h.bdryA, bdryB := h.bdryB, bdryC := h.bdryC
    recursion := fun ξ hn hl => h.recursion ξ hn (le_trans hl hNM) }

theorem SolvesUpToGen.eq_of_le (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hPA : ∀ k i, 0 ≤ PA k i) (hPB : ∀ l j, 0 ≤ PB l j)
    (hνA : ∀ i, 0 < νA i) (hνB : ∀ j, 0 < νB j)
    (hstA : ∀ i, ∑ k, νA k * PA k i = νA i) (hstB : ∀ j, ∑ l, νB l * PB l j = νB j) {N : ℕ}
    {q₁ q₂ : Config KA KB → F} (h₁ : SolvesUpToGen θA θB ρ νA νB PA PB N q₁)
    (h₂ : SolvesUpToGen θA θB ρ νA νB PA PB N q₂) :
    ∀ ξ : Config KA KB, ξ.nA + ξ.nB ≤ N → q₁ ξ = q₂ ξ := by
  have hbd : ∀ ξ : Config KA KB, ξ.n ≤ 1 → ξ.nA + ξ.nB ≤ N → q₁ ξ - q₂ ξ = 0 := by
    intro ξ hn _
    rcases Nat.lt_or_ge ξ.n 1 with hlt | hge
    · have hz : ξ = 0 := ξ.eq_zero_of_n_eq_zero (by omega)
      subst hz
      rw [h₁.empty, h₂.empty, sub_self]
    · rcases ξ.exists_e_of_n_eq_one (by omega) with ⟨i, rfl⟩ | ⟨j, rfl⟩ | ⟨i, j, rfl⟩
      · rw [h₁.bdryA, h₂.bdryA, sub_self]
      · rw [h₁.bdryB, h₂.bdryB, sub_self]
      · rw [h₁.bdryC, h₂.bdryC, sub_self]
  have hrec : ∀ ξ : Config KA KB, 2 ≤ ξ.n → ξ.nA + ξ.nB ≤ N →
      diag θA θB ρ ξ * (q₁ ξ - q₂ ξ) = rhsGen θA θB ρ PA PB (fun η => q₁ η - q₂ η) ξ := by
    intro ξ hn hl
    rw [rhsGen_sub, mul_sub, h₁.recursion ξ hn hl, h₂.recursion ξ hn hl]
  intro ξ hξ
  have := homogeneous_eq_zero_le (νA := νA) (νB := νB) hθA hθB hρ hPA hPB hνA hνB hstA hstB
    hbd hrec ξ hξ
  linarith [this]

noncomputable def blockOpGen (θA θB ρ : F) (PA : Fin KA → Fin KA → F)
    (PB : Fin KB → Fin KB → F) (N : ℕ) :
    (↥{ξ : Config KA KB | ξ.nA + ξ.nB = N} → F) →ₗ[F]
      (↥{ξ : Config KA KB | ξ.nA + ξ.nB = N} → F) where
  toFun v := fun ξ =>
    if 2 ≤ (ξ : Config KA KB).n
      then diag θA θB ρ (ξ : Config KA KB) * v ξ
        - rhsGen θA θB ρ PA PB (extZero N v) (ξ : Config KA KB)
      else v ξ
  map_add' v w := by
    have hext : extZero N (v + w) = fun η => extZero N v η + extZero N w η := by
      funext η; simp only [extZero]; split_ifs <;> simp
    funext ξ
    simp only [Pi.add_apply, hext, rhsGen_add]
    split_ifs with hn
    · ring
    · rfl
  map_smul' s v := by
    have hext : extZero N (s • v) = fun η => s * extZero N v η := by
      funext η; simp only [extZero]; split_ifs <;> simp
    funext ξ
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, hext, rhsGen_smul]
    split_ifs with hn
    · ring
    · rfl

theorem blockOpGen_injective (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hPA : ∀ k i, 0 ≤ PA k i) (hPB : ∀ l j, 0 ≤ PB l j)
    (hνA : ∀ i, 0 < νA i) (hνB : ∀ j, 0 < νB j)
    (hstA : ∀ i, ∑ k, νA k * PA k i = νA i) (hstB : ∀ j, ∑ l, νB l * PB l j = νB j) (N : ℕ) :
    Function.Injective (blockOpGen θA θB ρ PA PB N) := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  have hv' : ∀ (η : Config KA KB) (hη : η.nA + η.nB = N),
      (if 2 ≤ η.n
        then diag θA θB ρ η * v ⟨η, hη⟩ - rhsGen θA θB ρ PA PB (extZero N v) η
        else v ⟨η, hη⟩) = 0 := fun η hη => congrFun hv ⟨η, hη⟩
  have hz : ∀ η : Config KA KB, η.nA + η.nB ≠ N → extZero N v η = 0 := by
    intro η hη; simp [extZero, hη]
  have hon : ∀ (η : Config KA KB) (hh : η.nA + η.nB = N), extZero N v η = v ⟨η, hh⟩ := by
    intro η hh; simp [extZero, hh]
  have hbd : ∀ ξ : Config KA KB, ξ.n ≤ 1 → ξ.nA + ξ.nB ≤ N → extZero N v ξ = 0 := by
    intro ξ hn _
    by_cases hl : ξ.nA + ξ.nB = N
    · have h3 := hv' ξ hl
      rw [ite_eq_right (show ¬ (2 ≤ ξ.n) by omega)] at h3
      rw [hon ξ hl]; exact h3
    · exact hz ξ hl
  have hrec : ∀ ξ : Config KA KB, 2 ≤ ξ.n → ξ.nA + ξ.nB ≤ N →
      diag θA θB ρ ξ * extZero N v ξ = rhsGen θA θB ρ PA PB (extZero N v) ξ := by
    intro ξ hn hl
    by_cases hlev : ξ.nA + ξ.nB = N
    · have h2 := hv' ξ hlev
      rw [ite_eq_left hn] at h2
      rw [hon ξ hlev]
      linarith [h2]
    · have hb : ∀ η : Config KA KB, η.nA ≤ ξ.nA → η.nB ≤ ξ.nB → extZero N v η = 0 :=
        fun η h1 h2 => hz η (by omega)
      rw [hz ξ (by omega), mul_zero,
        rhsGen_congr (θA := θA) (θB := θB) (ρ := ρ) (PA := PA) (PB := PB)
          (q₂ := fun _ => (0 : F)) ξ hb, rhsGen_zero]
  have key := homogeneous_eq_zero_le (νA := νA) (νB := νB) hθA hθB hρ hPA hPB hνA hνB hstA hstB
    hbd hrec
  funext ξ
  have := key ξ (le_of_eq ξ.2)
  rw [hon ξ ξ.2] at this
  simpa using this

theorem exists_glueGen (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hPA : ∀ k i, 0 ≤ PA k i) (hPB : ∀ l j, 0 ≤ PB l j)
    (hνA : ∀ i, 0 < νA i) (hνB : ∀ j, 0 < νB j)
    (hstA : ∀ i, ∑ k, νA k * PA k i = νA i) (hstB : ∀ j, ∑ l, νB l * PB l j = νB j)
    (N : ℕ) (g : Config KA KB → F) :
    ∃ u : Config KA KB → F,
      (∀ η : Config KA KB, η.nA + η.nB ≠ N → u η = g η) ∧
      (∀ ξ : Config KA KB, ξ.nA + ξ.nB = N → ξ.n ≤ 1 → u ξ = Config.bdryVal νA νB ξ) ∧
      (∀ ξ : Config KA KB, ξ.nA + ξ.nB = N → 2 ≤ ξ.n →
        diag θA θB ρ ξ * u ξ = rhsGen θA θB ρ PA PB u ξ) := by
  obtain ⟨v, hv⟩ := (LinearMap.injective_iff_surjective.mp
      (blockOpGen_injective (νA := νA) (νB := νB) hθA hθB hρ hPA hPB hνA hνB hstA hstB N))
    (fun ξ => if 2 ≤ (ξ : Config KA KB).n
      then rhsGen θA θB ρ PA PB (offLevel N g) (ξ : Config KA KB)
      else Config.bdryVal νA νB (ξ : Config KA KB))
  have hv' : ∀ (η : Config KA KB) (hη : η.nA + η.nB = N),
      (if 2 ≤ η.n
        then diag θA θB ρ η * v ⟨η, hη⟩ - rhsGen θA θB ρ PA PB (extZero N v) η
        else v ⟨η, hη⟩)
      = (if 2 ≤ η.n then rhsGen θA θB ρ PA PB (offLevel N g) η
          else Config.bdryVal νA νB η) := fun η hη => congrFun hv ⟨η, hη⟩
  refine ⟨glue N g v, fun η hη => by simp [glue, hη], ?_, ?_⟩
  · intro ξ hlev hn
    have h2 := hv' ξ hlev
    rw [ite_eq_right (show ¬ (2 ≤ ξ.n) by omega), ite_eq_right (show ¬ (2 ≤ ξ.n) by omega)] at h2
    simpa [glue, hlev] using h2
  · intro ξ hlev hn
    have h2 := hv' ξ hlev
    rw [ite_eq_left hn, ite_eq_left hn] at h2
    have hu : glue N g v ξ = v ⟨ξ, hlev⟩ := by simp [glue, hlev]
    rw [hu, glue_eq_add, rhsGen_add]
    linarith [h2]

theorem exists_solvesUpToGen (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hPA : ∀ k i, 0 ≤ PA k i) (hPB : ∀ l j, 0 ≤ PB l j)
    (hνA : ∀ i, 0 < νA i) (hνB : ∀ j, 0 < νB j)
    (hstA : ∀ i, ∑ k, νA k * PA k i = νA i) (hstB : ∀ j, ∑ l, νB l * PB l j = νB j) (N : ℕ) :
    ∃ q : Config KA KB → F, SolvesUpToGen θA θB ρ νA νB PA PB N q := by
  induction N with
  | zero =>
    refine ⟨Config.bdryVal νA νB, Config.bdryVal_zero, fun i => Config.bdryVal_eA i,
      fun j => Config.bdryVal_eB j, fun i j => Config.bdryVal_eC i j, ?_⟩
    intro ξ hn hl
    exfalso
    have := ξ.n_add_t
    omega
  | succ N ih =>
    obtain ⟨g, hg⟩ := ih
    obtain ⟨u, hoff, hbdry, hrec⟩ :=
      exists_glueGen (νA := νA) (νB := νB) hθA hθB hρ hPA hPB hνA hνB hstA hstB (N + 1) g
    have hlow : ∀ η : Config KA KB, η.nA + η.nB ≤ N → u η = g η :=
      fun η hη => hoff η (by omega)
    have hb : ∀ ξ : Config KA KB, ξ.n ≤ 1 → u ξ = Config.bdryVal νA νB ξ := by
      intro ξ hn
      by_cases hlev : ξ.nA + ξ.nB = N + 1
      · exact hbdry ξ hlev hn
      · rw [hoff ξ hlev]
        rcases Nat.lt_or_ge ξ.n 1 with hlt | hge
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
        have hcongr : rhsGen θA θB ρ PA PB u ξ = rhsGen θA θB ρ PA PB g ξ :=
          rhsGen_congr ξ fun η h1 h2 => hlow η (by omega)
        rw [hlow ξ hle, hcongr]
        exact hg.recursion ξ hn hle

noncomputable def approxGen (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hPA : ∀ k i, 0 ≤ PA k i) (hPB : ∀ l j, 0 ≤ PB l j)
    (hνA : ∀ i, 0 < νA i) (hνB : ∀ j, 0 < νB j)
    (hstA : ∀ i, ∑ k, νA k * PA k i = νA i) (hstB : ∀ j, ∑ l, νB l * PB l j = νB j) (N : ℕ) :
    Config KA KB → F :=
  Classical.choose (exists_solvesUpToGen (νA := νA) (νB := νB) hθA hθB hρ hPA hPB hνA hνB
    hstA hstB N)

theorem approxGen_spec (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hPA : ∀ k i, 0 ≤ PA k i) (hPB : ∀ l j, 0 ≤ PB l j)
    (hνA : ∀ i, 0 < νA i) (hνB : ∀ j, 0 < νB j)
    (hstA : ∀ i, ∑ k, νA k * PA k i = νA i) (hstB : ∀ j, ∑ l, νB l * PB l j = νB j) (N : ℕ) :
    SolvesUpToGen θA θB ρ νA νB PA PB N
      (approxGen hθA hθB hρ hPA hPB hνA hνB hstA hstB N) :=
  Classical.choose_spec (exists_solvesUpToGen (νA := νA) (νB := νB) hθA hθB hρ hPA hPB hνA hνB
    hstA hstB N)

theorem approxGen_coherent (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hPA : ∀ k i, 0 ≤ PA k i) (hPB : ∀ l j, 0 ≤ PB l j)
    (hνA : ∀ i, 0 < νA i) (hνB : ∀ j, 0 < νB j)
    (hstA : ∀ i, ∑ k, νA k * PA k i = νA i) (hstB : ∀ j, ∑ l, νB l * PB l j = νB j)
    {Mlev N : ℕ} (hMN : Mlev ≤ N) (ξ : Config KA KB) (hξ : ξ.nA + ξ.nB ≤ Mlev) :
    approxGen hθA hθB hρ hPA hPB hνA hνB hstA hstB Mlev ξ
      = approxGen hθA hθB hρ hPA hPB hνA hνB hstA hstB N ξ :=
  SolvesUpToGen.eq_of_le hθA hθB hρ hPA hPB hνA hνB hstA hstB
    (approxGen_spec hθA hθB hρ hPA hPB hνA hνB hstA hstB Mlev)
    ((approxGen_spec hθA hθB hρ hPA hPB hνA hνB hstA hstB N).mono hMN) ξ hξ

theorem exists_isSolutionGen (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hPA : ∀ k i, 0 ≤ PA k i) (hPB : ∀ l j, 0 ≤ PB l j)
    (hνA : ∀ i, 0 < νA i) (hνB : ∀ j, 0 < νB j)
    (hstA : ∀ i, ∑ k, νA k * PA k i = νA i) (hstB : ∀ j, ∑ l, νB l * PB l j = νB j) :
    ∃ q : Config KA KB → F, IsSolutionGen θA θB ρ νA νB PA PB q := by
  refine ⟨fun ξ => approxGen hθA hθB hρ hPA hPB hνA hνB hstA hstB (ξ.nA + ξ.nB) ξ, ?_, ?_, ?_,
    ?_, ?_⟩
  · exact (approxGen_spec hθA hθB hρ hPA hPB hνA hνB hstA hstB _).empty
  · exact fun i => (approxGen_spec hθA hθB hρ hPA hPB hνA hνB hstA hstB _).bdryA i
  · exact fun j => (approxGen_spec hθA hθB hρ hPA hPB hνA hνB hstA hstB _).bdryB j
  · exact fun i j => (approxGen_spec hθA hθB hρ hPA hPB hνA hνB hstA hstB _).bdryC i j
  · intro ξ hn
    have hcongr : rhsGen θA θB ρ PA PB
        (fun η => approxGen hθA hθB hρ hPA hPB hνA hνB hstA hstB (η.nA + η.nB) η) ξ
        = rhsGen θA θB ρ PA PB
          (approxGen hθA hθB hρ hPA hPB hνA hνB hstA hstB (ξ.nA + ξ.nB)) ξ :=
      rhsGen_congr ξ fun η h1 h2 =>
        approxGen_coherent hθA hθB hρ hPA hPB hνA hνB hstA hstB (by omega) η le_rfl
    rw [hcongr]
    exact (approxGen_spec hθA hθB hρ hPA hPB hνA hνB hstA hstB _).recursion ξ hn le_rfl

noncomputable def qGen (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hPA : ∀ k i, 0 ≤ PA k i) (hPB : ∀ l j, 0 ≤ PB l j)
    (hνA : ∀ i, 0 < νA i) (hνB : ∀ j, 0 < νB j)
    (hstA : ∀ i, ∑ k, νA k * PA k i = νA i) (hstB : ∀ j, ∑ l, νB l * PB l j = νB j) :
    Config KA KB → F :=
  Classical.choose (exists_isSolutionGen (νA := νA) (νB := νB) hθA hθB hρ hPA hPB hνA hνB
    hstA hstB)

theorem qGen_isSolutionGen (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hPA : ∀ k i, 0 ≤ PA k i) (hPB : ∀ l j, 0 ≤ PB l j)
    (hνA : ∀ i, 0 < νA i) (hνB : ∀ j, 0 < νB j)
    (hstA : ∀ i, ∑ k, νA k * PA k i = νA i) (hstB : ∀ j, ∑ l, νB l * PB l j = νB j) :
    IsSolutionGen θA θB ρ νA νB PA PB (qGen hθA hθB hρ hPA hPB hνA hνB hstA hstB) :=
  Classical.choose_spec (exists_isSolutionGen (νA := νA) (νB := νB) hθA hθB hρ hPA hPB hνA hνB
    hstA hstB)

theorem qGen_unique (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hPA : ∀ k i, 0 ≤ PA k i) (hPB : ∀ l j, 0 ≤ PB l j)
    (hνA : ∀ i, 0 < νA i) (hνB : ∀ j, 0 < νB j)
    (hstA : ∀ i, ∑ k, νA k * PA k i = νA i) (hstB : ∀ j, ∑ l, νB l * PB l j = νB j)
    {q' : Config KA KB → F} (hq : IsSolutionGen θA θB ρ νA νB PA PB q') :
    q' = qGen hθA hθB hρ hPA hPB hνA hνB hstA hstB :=
  IsSolutionGen.unique hθA hθB hρ hPA hPB hνA hνB hstA hstB hq
    (qGen_isSolutionGen hθA hθB hρ hPA hPB hνA hνB hstA hstB)

end Rhone.MarkovChain.GeneralMutation
