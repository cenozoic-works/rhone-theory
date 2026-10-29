/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.TwoLocusGenealogy.Moves

/-! # The one-step law of the killed ancestral chain, and the first-step analysis -/

@[expose] public section

namespace Rhone.Coalescent.TwoLocusGenealogy

open Finset LinearAlgebra.Recursion

variable {n KA KB : ℕ} {σA : Fin n → Fin KA} {σB : Fin n → Fin KB}
variable {F : Type*} [Field F]

variable (σA σB)

def matchA (πA : Fin KA → F) (S : Finset (Fin n)) : F :=
  ∑ i, if ∀ k ∈ S, σA k = i then πA i else 0

def matchB (πB : Fin KB → F) (T : Finset (Fin n)) : F :=
  ∑ j, if ∀ k ∈ T, σB k = j then πB j else 0

variable {σA σB}

theorem matchA_eq {πA : Fin KA → F} {S : Finset (Fin n)} {i : Fin KA} (hne : S.Nonempty)
    (h : ∀ k ∈ S, σA k = i) : matchA σA πA S = πA i := by
  obtain ⟨k₀, hk₀⟩ := hne
  rw [matchA, Finset.sum_eq_single i]
  · rw [ite_eq_left h]
  · intro i' _ hne'
    rw [ite_eq_right]
    intro hc
    exact hne' (by rw [← hc k₀ hk₀, h k₀ hk₀])
  · intro hc
    exact absurd (Finset.mem_univ i) hc

theorem matchB_eq {πB : Fin KB → F} {T : Finset (Fin n)} {j : Fin KB} (hne : T.Nonempty)
    (h : ∀ k ∈ T, σB k = j) : matchB σB πB T = πB j := by
  obtain ⟨k₀, hk₀⟩ := hne
  rw [matchB, Finset.sum_eq_single j]
  · rw [ite_eq_left h]
  · intro j' _ hne'
    rw [ite_eq_right]
    intro hc
    exact hne' (by rw [← hc k₀ hk₀, h k₀ hk₀])
  · intro hc
    exact absurd (Finset.mem_univ j) hc

theorem matchA_eq_zero {πA : Fin KA → F} {S : Finset (Fin n)} (h : ¬ MonoA σA (S, S)) :
    matchA σA πA S = (0 : F) := by
  refine Finset.sum_eq_zero fun i _ => ite_eq_right fun hc => h ?_
  exact fun k hk l hl => by rw [hc k hk, hc l hl]

variable (θA θB ρ : F) (πA : Fin KA → F) (πB : Fin KB → F) (σA σB)

def dtot (L : Finset (Lin n)) : F :=
  ((L.card * (L.card - 1) : ℕ) : F) + θA * ((na L : ℕ) : F) + θB * ((nb L : ℕ) : F)
    + ρ * ((tt L : ℕ) : F)

def step (g : Finset (Lin n) → F) (L : Finset (Lin n)) : F :=
  (∑ p ∈ L, ∑ q ∈ L.erase p, g (coalL L p q))
    + θA * (∑ p ∈ carA L, matchA σA πA p.1 * g (mutAL L p))
    + θB * (∑ p ∈ carB L, matchB σB πB p.2 * g (mutBL L p))
    + ρ * (∑ p ∈ carC L, g (recL L p))

variable {θA θB ρ πA πB σA σB}

theorem dtot_eq_diag {L : Finset (Lin n)} (hw : WF L) (hcl : Clean σA σB L) :
    dtot θA θB ρ L = LinearAlgebra.Recursion.diag θA θB ρ (cfg σA σB L) := by
  rw [dtot, LinearAlgebra.Recursion.diag, n_cfg hw hcl, nA_cfg hcl, nB_cfg hcl, t_cfg hcl]

theorem cast_cfgA (L : Finset (Lin n)) (i : Fin KA) :
    ((cfgA σA L i : ℕ) : F) = ∑ p ∈ L, ((uA σA p i : ℕ) : F) := by
  rw [cfgA, Finset.sum_apply, Nat.cast_sum]

theorem cast_cfgB (L : Finset (Lin n)) (j : Fin KB) :
    ((cfgB σB L j : ℕ) : F) = ∑ p ∈ L, ((uB σB p j : ℕ) : F) := by
  rw [cfgB, Finset.sum_apply, Nat.cast_sum]

theorem cast_cfgC (L : Finset (Lin n)) (i : Fin KA) (j : Fin KB) :
    ((cfgC σA σB L i j : ℕ) : F) = ∑ p ∈ L, ((uC σA σB p i j : ℕ) : F) := by
  have h : cfgC σA σB L i = ∑ p ∈ L, uC σA σB p i := by
    rw [cfgC, Finset.sum_apply]
  rw [h, Finset.sum_apply, Nat.cast_sum]

theorem sum_uA_carA (L : Finset (Lin n)) (i : Fin KA) :
    ∑ p ∈ carA L, ((uA σA p i : ℕ) : F) = ((cfgA σA L i : ℕ) : F) := by
  rw [cast_cfgA]
  refine Finset.sum_subset (carA_subset L) fun p hp hnp => ?_
  have h1 : ¬ p.1.Nonempty := fun hc => hnp (mem_carA.2 ⟨hp, hc⟩)
  rw [Finset.not_nonempty_iff_eq_empty] at h1
  rw [uA_eq_zero_of_emptyA h1]
  simp

theorem sum_uB_carB (L : Finset (Lin n)) (j : Fin KB) :
    ∑ p ∈ carB L, ((uB σB p j : ℕ) : F) = ((cfgB σB L j : ℕ) : F) := by
  rw [cast_cfgB]
  refine Finset.sum_subset (carB_subset L) fun p hp hnp => ?_
  have h1 : ¬ p.2.Nonempty := fun hc => hnp (mem_carB.2 ⟨hp, hc⟩)
  rw [Finset.not_nonempty_iff_eq_empty] at h1
  rw [uB_eq_zero_of_emptyB h1]
  simp

theorem sum_uC_carA (L : Finset (Lin n)) (i : Fin KA) (j : Fin KB) :
    ∑ p ∈ carA L, ((uC σA σB p i j : ℕ) : F) = ((cfgC σA σB L i j : ℕ) : F) := by
  rw [cast_cfgC]
  refine Finset.sum_subset (carA_subset L) fun p hp hnp => ?_
  have h1 : ¬ p.1.Nonempty := fun hc => hnp (mem_carA.2 ⟨hp, hc⟩)
  rw [Finset.not_nonempty_iff_eq_empty] at h1
  rw [uC_eq_zero_of_emptyA h1]
  simp

theorem sum_uC_carB (L : Finset (Lin n)) (i : Fin KA) (j : Fin KB) :
    ∑ p ∈ carB L, ((uC σA σB p i j : ℕ) : F) = ((cfgC σA σB L i j : ℕ) : F) := by
  rw [cast_cfgC]
  refine Finset.sum_subset (carB_subset L) fun p hp hnp => ?_
  have h1 : ¬ p.2.Nonempty := fun hc => hnp (mem_carB.2 ⟨hp, hc⟩)
  rw [Finset.not_nonempty_iff_eq_empty] at h1
  rw [uC_eq_zero_of_emptyB h1]
  simp

theorem sum_uC_carC (L : Finset (Lin n)) (i : Fin KA) (j : Fin KB) :
    ∑ p ∈ carC L, ((uC σA σB p i j : ℕ) : F) = ((cfgC σA σB L i j : ℕ) : F) := by
  rw [cast_cfgC]
  refine Finset.sum_subset (carC_subset L) fun p hp hnp => ?_
  rcases Finset.eq_empty_or_nonempty p.1 with h1 | h1
  · rw [uC_eq_zero_of_emptyA h1]; simp
  · rcases Finset.eq_empty_or_nonempty p.2 with h2 | h2
    · rw [uC_eq_zero_of_emptyB h2]; simp
    · exact absurd (mem_carC.2 ⟨hp, h1, h2⟩) hnp

section Parts

variable {g : Finset (Lin n) → F} {f : Config KA KB → F}
variable (hgf : ∀ M, WF M → Clean σA σB M → g M = f (cfg σA σB M))

include hgf

theorem mutA_term {L : Finset (Lin n)} (hw : WF L) (hcl : Clean σA σB L) {p : Lin n}
    (hp : p ∈ carA L) :
    matchA σA πA p.1 * g (mutAL L p)
      = ∑ i, πA i * (((uA σA p i : ℕ) : F) * f ((cfg σA σB L).dropA i)
          + ∑ j, ((uC σA σB p i j : ℕ) : F) * f ((cfg σA σB L).killA i j)) := by
  obtain ⟨hpL, hne⟩ := mem_carA.1 hp
  rcases clean_class hw hcl hpL with ⟨i₀, hi⟩ | ⟨j₀, hj⟩ | ⟨i₀, j₀, hij⟩
  · obtain ⟨hcln, hcfg⟩ := mutA_A hcl hpL hi
    rw [matchA_eq hne hi.2.2, hgf _ (hw.mutA hpL) hcln, hcfg, uA_eq hi,
      uC_eq_zero_of_emptyB hi.2.1]
    simp [eV]
  · exact absurd hj.1 (Finset.nonempty_iff_ne_empty.1 hne)
  · obtain ⟨hcln, hcfg⟩ := mutA_C hw hcl hpL hij
    rw [matchA_eq hne hij.2.2.1, hgf _ (hw.mutA hpL) hcln, hcfg, uA_eq_zero_of_carB hij.2.1,
      uC_eq hij]
    simp [eM_apply]

theorem mutB_term {L : Finset (Lin n)} (hw : WF L) (hcl : Clean σA σB L) {p : Lin n}
    (hp : p ∈ carB L) :
    matchB σB πB p.2 * g (mutBL L p)
      = ∑ j, πB j * (((uB σB p j : ℕ) : F) * f ((cfg σA σB L).dropB j)
          + ∑ i, ((uC σA σB p i j : ℕ) : F) * f ((cfg σA σB L).killB i j)) := by
  obtain ⟨hpL, hne⟩ := mem_carB.1 hp
  rcases clean_class hw hcl hpL with ⟨i₀, hi⟩ | ⟨j₀, hj⟩ | ⟨i₀, j₀, hij⟩
  · exact absurd hi.2.1 (Finset.nonempty_iff_ne_empty.1 hne)
  · obtain ⟨hcln, hcfg⟩ := mutB_B hcl hpL hj
    rw [matchB_eq hne hj.2.2, hgf _ (hw.mutB hpL) hcln, hcfg, uB_eq hj,
      uC_eq_zero_of_emptyA hj.1]
    simp [eV]
  · obtain ⟨hcln, hcfg⟩ := mutB_C hw hcl hpL hij
    rw [matchB_eq hne hij.2.2.2, hgf _ (hw.mutB hpL) hcln, hcfg, uB_eq_zero_of_carA hij.1,
      uC_eq hij]
    simp [eM_apply]

theorem rec_term {L : Finset (Lin n)} (hw : WF L) (hcl : Clean σA σB L) {p : Lin n}
    (hp : p ∈ carC L) :
    g (recL L p)
      = ∑ i, ∑ j, ((uC σA σB p i j : ℕ) : F) * f ((cfg σA σB L).split i j) := by
  obtain ⟨hpL, h1, h2⟩ := mem_carC.1 hp
  rcases clean_class hw hcl hpL with ⟨i₀, hi⟩ | ⟨j₀, hj⟩ | ⟨i₀, j₀, hij⟩
  · exact absurd hi.2.1 (Finset.nonempty_iff_ne_empty.1 h2)
  · exact absurd hj.1 (Finset.nonempty_iff_ne_empty.1 h1)
  · obtain ⟨hcln, hcfg⟩ := rec_C hw hcl hpL hij
    rw [hgf _ (hw.recomb hpL h1 h2) hcln, hcfg, uC_eq hij]
    simp [eM_apply]

end Parts

end Rhone.Coalescent.TwoLocusGenealogy
