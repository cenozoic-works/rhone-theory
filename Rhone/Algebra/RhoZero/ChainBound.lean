/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.RhoZero.Window
public import Rhone.Algebra.BilinearForm.Multiplicity

/-! # A power of `ℓ` of size `|K_n(ℓ)|` clears the denominator of `q` at `ρ = 0` -/

@[expose] public section

namespace Rhone.Algebra.RhoZero

open Finset LinearAlgebra.Recursion Config ClosedForms

variable {KA KB : ℕ}

def PropToPrim (L : Prim) (η : Config KA KB) : Prop := L.propTo η.nA η.nB η.n

theorem propToPrim_iff_propTo (L : Prim) {i₀ j₀ k₀ : ℕ} (hrep : L.propTo i₀ j₀ k₀)
    (η : Config KA KB) : PropToPrim L η ↔ BilinearForm.PropTo i₀ j₀ k₀ η :=
  propTo_iff_Proportional L hrep

theorem ellType_self (L : Prim) {η : Config KA KB} (h2 : 2 ≤ min η.nA η.nB)
    (hP : PropToPrim L η) : EllType L η.n η.nA η.nB η.n := by
  have hnt := η.n_add_t
  exact
    { two_le_i := le_trans h2 (min_le_left _ _)
      two_le_j := le_trans h2 (min_le_right _ _)
      k_le_n := le_rfl
      max_le_k := max_le η.nA_le_n η.nB_le_n
      k_le_add := by omega
      isPropTo := hP }

theorem mem_Kwin_self (L : Prim) {η : Config KA KB} (h2 : 2 ≤ min η.nA η.nB)
    (hP : PropToPrim L η) : η.n ∈ Kwin L η.n :=
  (mem_Kwin_iff L η.n η.n).mpr ⟨η.nA, η.nB, ellType_self L h2 hP⟩

theorem n_lt_of_propToPrim (L : Prim) {η ζ : Config KA KB} (hbel : Below ζ η)
    (hlt : meas ζ < meas η) (h2η : 2 ≤ min η.nA η.nB) (hPη : PropToPrim L η)
    (hPζ : PropToPrim L ζ) : ζ.n < η.n := by
  rcases lt_or_eq_of_le hbel.1 with h | h
  · exact h
  · exfalso
    have hnA : 2 ≤ η.nA := le_trans h2η (min_le_left _ _)
    have hk : 2 ≤ η.n := le_trans hnA η.nA_le_n
    have hPζ' : L.propTo ζ.nA ζ.nB η.n := by rw [← h]; exact hPζ
    obtain ⟨hA, hB⟩ := propTo_unique L hk hPζ' hPη
    simp only [meas] at hlt
    omega

theorem chain_propTo_card (L : Prim) (ξ : Config KA KB) {m : ℕ} (ch : Fin m → Config KA KB)
    (hbelow : ∀ r, Below (ch r) ξ)
    (hdeep : ∀ r, 2 ≤ min (ch r).nA (ch r).nB)
    (hprop : ∀ r, PropToPrim L (ch r))
    (hchain : ∀ r s : Fin m, r < s → Below (ch s) (ch r) ∧ meas (ch s) < meas (ch r)) :
    m ≤ (Kwin L ξ.n).card := by
  have hmem : ∀ r : Fin m, (ch r).n ∈ Kwin L ξ.n := by
    intro r
    exact Kwin_mono L (hbelow r).1 (mem_Kwin_self L (hdeep r) (hprop r))
  have hlt : ∀ r s : Fin m, r < s → (ch s).n < (ch r).n := by
    intro r s hrs
    obtain ⟨hb, hm⟩ := hchain r s hrs
    exact n_lt_of_propToPrim L hb hm (hdeep r) (hprop r) (hprop s)
  have hinj : ∀ r s : Fin m, (ch r).n = (ch s).n → r = s := by
    intro r s h
    rcases lt_trichotomy r s with hrs | hrs | hrs
    · exact absurd h (by have := hlt r s hrs; omega)
    · exact hrs
    · exact absurd h (by have := hlt s r hrs; omega)
  have hcard : (Finset.univ : Finset (Fin m)).card ≤ (Kwin L ξ.n).card :=
    Finset.card_le_card_of_injOn (fun r : Fin m => (ch r).n)
      (fun r _ => hmem r) (fun r _ s _ hrs => hinj r s hrs)
  rw [Finset.card_univ, Fintype.card_fin] at hcard
  exact hcard

def rankK (L : Prim) (η : Config KA KB) : ℕ := max 2 (1 + (Kwin L η.n).card)

theorem rankK_mono (L : Prim) : ∀ ζ η : Config KA KB, Below ζ η → rankK L ζ ≤ rankK L η := by
  intro ζ η h
  have : (Kwin L ζ.n).card ≤ (Kwin L η.n).card := Finset.card_le_card (Kwin_mono L h.1)
  simp only [rankK]
  omega

theorem rankK_two_le (L : Prim) (η : Config KA KB) : 2 ≤ rankK L η := le_max_left _ _

theorem rankK_chain (L : Prim) : ∀ η ζ : Config KA KB, Below ζ η → meas ζ < meas η →
    2 ≤ min η.nA η.nB → 2 ≤ min ζ.nA ζ.nB → PropToPrim L η → PropToPrim L ζ →
    rankK L ζ < rankK L η := by
  intro η ζ hbel hlt h2η h2ζ hPη hPζ
  have hn : ζ.n < η.n := n_lt_of_propToPrim L hbel hlt h2η hPη hPζ
  have hpos : 1 ≤ (Kwin L ζ.n).card :=
    Finset.card_pos.mpr ⟨ζ.n, mem_Kwin_self L h2ζ hPζ⟩
  have hsub : Kwin L ζ.n ⊆ Kwin L η.n := Kwin_mono L (le_of_lt hn)
  have hmem : η.n ∈ Kwin L η.n := mem_Kwin_self L h2η hPη
  have hnot : η.n ∉ Kwin L ζ.n := fun hc => absurd (le_of_mem_Kwin hc) (by omega)
  have hss : Kwin L ζ.n ⊂ Kwin L η.n :=
    (Finset.ssubset_iff_of_subset hsub).mpr ⟨η.n, hmem, hnot⟩
  have hcard : (Kwin L ζ.n).card < (Kwin L η.n).card := Finset.card_lt_card hss
  simp only [rankK]
  omega

theorem rankK_sub_one (L : Prim) (ξ : Config KA KB) :
    rankK L ξ - 1 = max 1 (Kwin L ξ.n).card := by
  simp only [rankK]
  omega

variable {F : Type*} [CommRing F]

theorem q_mem_pow_Kwin {A : Subring F} {θA θB : F} {πA : Fin KA → F} {πB : Fin KB → F}
    {q : Config KA KB → F} (hq : IsSolution θA θB 0 πA πB q)
    (hθA : θA ∈ A) (hθB : θB ∈ A) (hπA : ∀ i, πA i ∈ A) (hπB : ∀ j, πB j ∈ A)
    (ξ : Config KA KB) {ℓ : F} (hℓ : ℓ ∈ A) (L : Prim)
    (hstop : ∀ η : Config KA KB, Below η ξ → min η.nA η.nB ≤ 1 → q η ∈ A)
    (hinv : ∀ η : Config KA KB, Below η ξ → 2 ≤ min η.nA η.nB → ¬ PropToPrim L η →
      ∃ y ∈ A, diag θA θB 0 η * y = 1)
    (hdvd : ∀ η : Config KA KB, Below η ξ → 2 ≤ min η.nA η.nB → PropToPrim L η →
      ∃ y ∈ A, diag θA θB 0 η * y = ℓ) :
    ℓ ^ (max 1 (Kwin L ξ.n).card) * q ξ ∈ A := by
  have key := BilinearForm.q_mem_pow_of_rho_zero hq hθA hθB hπA hπB ξ hℓ (PropToPrim L)
    (rankK L) (rankK_mono L) (fun η _ => rankK_two_le L η) (rankK_chain L) hstop hinv hdvd
  rwa [rankK_sub_one] at key

theorem q_mem_pow_Kwin' {A : Subring F} {θA θB : F} {πA : Fin KA → F} {πB : Fin KB → F}
    {q : Config KA KB → F} (hq : IsSolution θA θB 0 πA πB q)
    (hθA : θA ∈ A) (hθB : θB ∈ A) (hπA : ∀ i, πA i ∈ A) (hπB : ∀ j, πB j ∈ A)
    (ξ : Config KA KB) {ℓ : F} (hℓ : ℓ ∈ A) (L : Prim) (hne : (Kwin L ξ.n).Nonempty)
    (hstop : ∀ η : Config KA KB, Below η ξ → min η.nA η.nB ≤ 1 → q η ∈ A)
    (hinv : ∀ η : Config KA KB, Below η ξ → 2 ≤ min η.nA η.nB → ¬ PropToPrim L η →
      ∃ y ∈ A, diag θA θB 0 η * y = 1)
    (hdvd : ∀ η : Config KA KB, Below η ξ → 2 ≤ min η.nA η.nB → PropToPrim L η →
      ∃ y ∈ A, diag θA θB 0 η * y = ℓ) :
    ℓ ^ (Kwin L ξ.n).card * q ξ ∈ A := by
  have hcard : 1 ≤ (Kwin L ξ.n).card := Finset.card_pos.mpr hne
  have key := q_mem_pow_Kwin hq hθA hθB hπA hπB ξ hℓ L hstop hinv hdvd
  rwa [max_eq_right hcard] at key

end Rhone.Algebra.RhoZero
