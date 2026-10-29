/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.SlotDeletion.Kill

/-! # DL‑1 verbatim — the source `R^{i,j}_t` in the lower `Φ`'s -/

@[expose] public section

universe u

namespace Rhone.Probability.SlotDeletion

open Finset LinearAlgebra.Recursion Denominator LinearAlgebra.Multilinear Multilinear

section Live

variable {SA SB : Type*} [Fintype SA] [DecidableEq SA] [Fintype SB] [DecidableEq SB]
variable {M : Finset (SA × SB)}

theorem liveM_of_free {S : Finset SA} {T : Finset SB} (hS : ∀ x ∈ S, x ∈ freeA M)
    (hT : ∀ y ∈ T, y ∈ freeB M) : liveM M S T = M := by
  rw [liveM]
  refine Finset.filter_true_of_mem fun r hr => ⟨fun hc => ?_, fun hc => ?_⟩
  · exact notMem_freeA_of_mem hr (hS _ hc)
  · exact notMem_freeB_of_mem hr (hT _ hc)

omit [Fintype SB] in
theorem freeA_of_erase {p : SA × SB} {x : SA} (h : x ∈ freeA M) : x ∈ freeA (M.erase p) := by
  rw [mem_freeA] at h ⊢
  exact fun v hv => h v (Finset.mem_of_mem_erase hv)

omit [Fintype SA] in
theorem freeB_of_erase {p : SA × SB} {y : SB} (h : y ∈ freeB M) : y ∈ freeB (M.erase p) := by
  rw [mem_freeB] at h ⊢
  exact fun u hu => h u (Finset.mem_of_mem_erase hu)

omit [Fintype SB] in
theorem fst_freeA_erase (hM : IsMatching M) {p : SA × SB} (hp : p ∈ M) :
    p.1 ∈ freeA (M.erase p) := by
  rw [mem_freeA]
  intro v hv
  rcases Finset.mem_erase.mp hv with ⟨hne, hmem⟩
  exact hne (hM.fst _ hmem _ hp rfl)

omit [Fintype SA] in
theorem snd_freeB_erase (hM : IsMatching M) {p : SA × SB} (hp : p ∈ M) :
    p.2 ∈ freeB (M.erase p) := by
  rw [mem_freeB]
  intro u hu
  rcases Finset.mem_erase.mp hu with ⟨hne, hmem⟩
  exact hne (hM.snd _ hmem _ hp rfl)

end Live

section SumConst

variable {F : Type*} [CommRing F]

theorem sum_erase_const {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : F) :
    (∑ _k ∈ s, ∑ _m ∈ s.erase _k, c) = ((s.card * (s.card - 1) : ℕ) : F) * c := by
  have h1 : ∀ k ∈ s, (∑ _m ∈ s.erase k, c) = ((s.card - 1 : ℕ) : F) * c := by
    intro k hk
    rw [Finset.sum_const, Finset.card_erase_of_mem hk, nsmul_eq_mul]
  rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, Nat.cast_mul]
  ring

theorem sum_prod_const {ι κ : Type*} (s : Finset ι) (v : Finset κ) (c : F) :
    (∑ _k ∈ s, ∑ _p ∈ v, c) = ((s.card * v.card : ℕ) : F) * c := by
  simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_mul]
  ring

end SumConst

theorem gamma_count (i t : ℕ) (h : t ≤ i) :
    (i - t) * (i - t - 1) + 2 * ((i - t) * t) = (i - t) * (i + t - 1) := by
  rcases Nat.lt_or_ge t i with hlt | hge
  · have h1 : i - t - 1 + 2 * t = i + t - 1 := by omega
    calc (i - t) * (i - t - 1) + 2 * ((i - t) * t)
        = (i - t) * (i - t - 1 + 2 * t) := by ring
      _ = (i - t) * (i + t - 1) := by rw [h1]
  · have h0 : i - t = 0 := by omega
    rw [h0]
    simp

theorem card_pair_eq {ι : Type*} [DecidableEq ι] {a b : ι} (h : a ≠ b) :
    (insert a {b} : Finset ι).card = 2 :=
  Finset.card_pair h

section R

variable {F : Type*} [Field F]

noncomputable def phiRecursionSource (q : Config 2 2 → F) (πA πB : Fin 2 → F) (i j t : ℕ) : F :=
  kap πA * ((((i - t) * (i - t - 1) : ℕ) : F) * Phi q πA πB (i - 2) j t
      + 2 * (((i - t) * t : ℕ) : F) * Phi q πA πB (i - 2) j (t - 1))
    + gam πA * (((i - t) * (i + t - 1) : ℕ) : F) * Phi q πA πB (i - 1) j t
    + kap πB * ((((j - t) * (j - t - 1) : ℕ) : F) * Phi q πA πB i (j - 2) t
      + 2 * (((j - t) * t : ℕ) : F) * Phi q πA πB i (j - 2) (t - 1))
    + gam πB * (((j - t) * (j + t - 1) : ℕ) : F) * Phi q πA πB i (j - 1) t
    + ((t * (t - 1) : ℕ) : F) * (kap πA * kap πB * Phi q πA πB (i - 2) (j - 2) (t - 2)
      + kap πA * gam πB * Phi q πA πB (i - 2) (j - 1) (t - 2)
      + gam πA * kap πB * Phi q πA πB (i - 1) (j - 2) (t - 2)
      + gam πA * gam πB * Phi q πA πB (i - 1) (j - 1) (t - 1))

end R

section Eval

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA πB : Fin 2 → F}
variable (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
variable {q : Config 2 2 → F} (hq : IsSolution θA θB ρ πA πB q)
variable {SA SB : Type u} [Fintype SA] [DecidableEq SA] [Fintype SB] [DecidableEq SB]
include hθA hθB hρ hq

theorem Q_kill_eval (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1)
    {M : Finset (SA × SB)} (hM : IsMatching M) {S : Finset SA} {T : Finset SB} {a b c : ℕ}
    (hS : S.card = a) (hT : T.card = b) (hlive : (liveM M S T).card = c) :
    Q q M (killAt (fvec πA) S) (killAt (fvec πB) T)
      = Phi q πA πB (Fintype.card SA - a) (Fintype.card SB - b) c := by
  rw [Q_killAt_eq_Phi hθA hθB hρ hq hπA hπB M S T hM, hS, hT, hlive]

theorem Q_killA_eval (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1)
    {M : Finset (SA × SB)} (hM : IsMatching M) {S : Finset SA} {a c : ℕ}
    (hS : S.card = a) (hlive : (liveM M S (∅ : Finset SB)).card = c) :
    Q q M (killAt (fvec πA) S) (fun _ => fvec πB)
      = Phi q πA πB (Fintype.card SA - a) (Fintype.card SB) c := by
  rw [← killAt_empty (ι := SB) (fvec πB),
    Q_kill_eval hθA hθB hρ hq hπA hπB hM hS Finset.card_empty hlive, Nat.sub_zero]

theorem Q_killB_eval (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1)
    {M : Finset (SA × SB)} (hM : IsMatching M) {T : Finset SB} {b c : ℕ}
    (hT : T.card = b) (hlive : (liveM M (∅ : Finset SA) T).card = c) :
    Q q M (fun _ => fvec πA) (killAt (fvec πB) T)
      = Phi q πA πB (Fintype.card SA) (Fintype.card SB - b) c := by
  rw [← killAt_empty (ι := SA) (fvec πA),
    Q_kill_eval hθA hθB hρ hq hπA hπB hM Finset.card_empty hT hlive, Nat.sub_zero]

end Eval

section DL1

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA πB : Fin 2 → F}
variable (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
variable {q : Config 2 2 → F} (hq : IsSolution θA θB ρ πA πB q)
variable {SA SB : Type u} [Fintype SA] [DecidableEq SA] [Fintype SB] [DecidableEq SB]
include hθA hθB hρ hq

theorem matchingRecursionSource_eq_phiRecursionSource (hπA : πA 0 + πA 1 = 1)
    (hπB : πB 0 + πB 1 = 1)
    (M : Finset (SA × SB)) (hM : IsMatching M) :
    matchingRecursionSource q πA πB M
      = phiRecursionSource q πA πB (Fintype.card SA) (Fintype.card SB) M.card := by
  have hfA : (freeA M).card = Fintype.card SA - M.card := by have := card_freeA hM; omega
  have hfB : (freeB M).card = Fintype.card SB - M.card := by have := card_freeB hM; omega
  have htA : M.card ≤ Fintype.card SA := by have := card_freeA hM; omega
  have htB : M.card ≤ Fintype.card SB := by have := card_freeB hM; omega
  have r1 : ∀ k ∈ freeA M, ∀ m ∈ (freeA M).erase k,
      kap πA * Q q M (killAt (fvec πA) (insert k {m})) (fun _ => fvec πB)
        + gam πA * Q q M (killAt (fvec πA) {m}) (fun _ => fvec πB)
      = kap πA * Phi q πA πB (Fintype.card SA - 2) (Fintype.card SB) M.card
        + gam πA * Phi q πA πB (Fintype.card SA - 1) (Fintype.card SB) M.card := by
    intro k hk m hm
    rcases Finset.mem_erase.mp hm with ⟨hmk, hmf⟩
    have hlive2 : liveM M (insert k {m}) (∅ : Finset SB) = M :=
      liveM_of_free (by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hk
        · rw [Finset.mem_singleton.mp hx]; exact hmf) (by simp)
    have hlive1 : liveM M ({m} : Finset SA) (∅ : Finset SB) = M :=
      liveM_of_free (by
        intro x hx
        rw [Finset.mem_singleton.mp hx]; exact hmf) (by simp)
    rw [Q_killA_eval hθA hθB hρ hq hπA hπB hM (card_pair_eq (Ne.symm hmk)) (by rw [hlive2]),
      Q_killA_eval hθA hθB hρ hq hπA hπB hM (Finset.card_singleton _) (by rw [hlive1])]
  have r2 : ∀ k ∈ freeA M, ∀ p ∈ M,
      kap πA * Q q M (killAt (fvec πA) (insert p.1 {k})) (fun _ => fvec πB)
        + gam πA * Q q M (killAt (fvec πA) {k}) (fun _ => fvec πB)
      = kap πA * Phi q πA πB (Fintype.card SA - 2) (Fintype.card SB) (M.card - 1)
        + gam πA * Phi q πA πB (Fintype.card SA - 1) (Fintype.card SB) M.card := by
    intro k hk p hp
    have hne : p.1 ≠ k := fst_ne_of_mem_freeA hk hp
    have hlive2 : liveM M (insert p.1 {k}) (∅ : Finset SB) = M.erase p := by
      rw [← liveM_erase (p := p) M _ _ (Or.inl (Finset.mem_insert_self _ _))]
      refine liveM_of_free (fun x hx => ?_) (by simp)
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact fst_freeA_erase hM hp
      · rw [Finset.mem_singleton.mp hx]; exact freeA_of_erase hk
    have hlive1 : liveM M ({k} : Finset SA) (∅ : Finset SB) = M :=
      liveM_of_free (by intro x hx; rw [Finset.mem_singleton.mp hx]; exact hk) (by simp)
    rw [Q_killA_eval hθA hθB hρ hq hπA hπB hM (card_pair_eq hne)
        (by rw [hlive2, Finset.card_erase_of_mem hp]),
      Q_killA_eval hθA hθB hρ hq hπA hπB hM (Finset.card_singleton _) (by rw [hlive1])]
  have r3 : ∀ l ∈ freeB M, ∀ n ∈ (freeB M).erase l,
      kap πB * Q q M (fun _ => fvec πA) (killAt (fvec πB) (insert l {n}))
        + gam πB * Q q M (fun _ => fvec πA) (killAt (fvec πB) {n})
      = kap πB * Phi q πA πB (Fintype.card SA) (Fintype.card SB - 2) M.card
        + gam πB * Phi q πA πB (Fintype.card SA) (Fintype.card SB - 1) M.card := by
    intro l hl n hn
    rcases Finset.mem_erase.mp hn with ⟨hnl, hnf⟩
    have hlive2 : liveM M (∅ : Finset SA) (insert l {n}) = M :=
      liveM_of_free (by simp) (by
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hl
        · rw [Finset.mem_singleton.mp hy]; exact hnf)
    have hlive1 : liveM M (∅ : Finset SA) ({n} : Finset SB) = M :=
      liveM_of_free (by simp) (by intro y hy; rw [Finset.mem_singleton.mp hy]; exact hnf)
    rw [Q_killB_eval hθA hθB hρ hq hπA hπB hM (card_pair_eq (Ne.symm hnl)) (by rw [hlive2]),
      Q_killB_eval hθA hθB hρ hq hπA hπB hM (Finset.card_singleton _) (by rw [hlive1])]
  have r4 : ∀ l ∈ freeB M, ∀ p ∈ M,
      kap πB * Q q M (fun _ => fvec πA) (killAt (fvec πB) (insert p.2 {l}))
        + gam πB * Q q M (fun _ => fvec πA) (killAt (fvec πB) {l})
      = kap πB * Phi q πA πB (Fintype.card SA) (Fintype.card SB - 2) (M.card - 1)
        + gam πB * Phi q πA πB (Fintype.card SA) (Fintype.card SB - 1) M.card := by
    intro l hl p hp
    have hne : p.2 ≠ l := snd_ne_of_mem_freeB hl hp
    have hlive2 : liveM M (∅ : Finset SA) (insert p.2 {l}) = M.erase p := by
      rw [← liveM_erase (p := p) M _ _ (Or.inr (Finset.mem_insert_self _ _))]
      refine liveM_of_free (by simp) (fun y hy => ?_)
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact snd_freeB_erase hM hp
      · rw [Finset.mem_singleton.mp hy]; exact freeB_of_erase hl
    have hlive1 : liveM M (∅ : Finset SA) ({l} : Finset SB) = M :=
      liveM_of_free (by simp) (by intro y hy; rw [Finset.mem_singleton.mp hy]; exact hl)
    rw [Q_killB_eval hθA hθB hρ hq hπA hπB hM (card_pair_eq hne)
        (by rw [hlive2, Finset.card_erase_of_mem hp]),
      Q_killB_eval hθA hθB hρ hq hπA hπB hM (Finset.card_singleton _) (by rw [hlive1])]
  have r5 : ∀ p ∈ M, ∀ r ∈ M.erase p,
      kap πA * kap πB * Q q M (killAt (fvec πA) (insert p.1 {r.1}))
            (killAt (fvec πB) (insert p.2 {r.2}))
        + kap πA * gam πB * Q q M (killAt (fvec πA) (insert p.1 {r.1}))
            (killAt (fvec πB) {r.2})
        + gam πA * kap πB * Q q M (killAt (fvec πA) {r.1})
            (killAt (fvec πB) (insert p.2 {r.2}))
        + gam πA * gam πB * Q q M (killAt (fvec πA) {r.1}) (killAt (fvec πB) {r.2})
      = kap πA * kap πB
            * Phi q πA πB (Fintype.card SA - 2) (Fintype.card SB - 2) (M.card - 2)
        + kap πA * gam πB
            * Phi q πA πB (Fintype.card SA - 2) (Fintype.card SB - 1) (M.card - 2)
        + gam πA * kap πB
            * Phi q πA πB (Fintype.card SA - 1) (Fintype.card SB - 2) (M.card - 2)
        + gam πA * gam πB
            * Phi q πA πB (Fintype.card SA - 1) (Fintype.card SB - 1) (M.card - 1) := by
    intro p hp r hr
    rcases Finset.mem_erase.mp hr with ⟨hrp, hrM⟩
    have hM' : IsMatching (M.erase p) := isMatching_erase hM p
    have hne1 : p.1 ≠ r.1 := fun hc => hrp (hM.fst _ hp _ hrM hc).symm
    have hne2 : p.2 ≠ r.2 := fun hc => hrp (hM.snd _ hp _ hrM hc).symm
    have hcard2 : ((M.erase p).erase r).card = M.card - 2 := by
      rw [Finset.card_erase_of_mem hr, Finset.card_erase_of_mem hp]
      omega
    have hpA : p.1 ∈ freeA ((M.erase p).erase r) := freeA_of_erase (fst_freeA_erase hM hp)
    have hpB : p.2 ∈ freeB ((M.erase p).erase r) := freeB_of_erase (snd_freeB_erase hM hp)
    have hrA : r.1 ∈ freeA ((M.erase p).erase r) := fst_freeA_erase hM' hr
    have hrB : r.2 ∈ freeB ((M.erase p).erase r) := snd_freeB_erase hM' hr
    have hlA : ∀ x ∈ (insert p.1 {r.1} : Finset SA), x ∈ freeA ((M.erase p).erase r) := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hpA
      · rw [Finset.mem_singleton.mp hx]; exact hrA
    have hlB : ∀ y ∈ (insert p.2 {r.2} : Finset SB), y ∈ freeB ((M.erase p).erase r) := by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hpB
      · rw [Finset.mem_singleton.mp hy]; exact hrB
    have hsA : ∀ x ∈ ({r.1} : Finset SA), x ∈ freeA ((M.erase p).erase r) := by
      intro x hx; rw [Finset.mem_singleton.mp hx]; exact hrA
    have hsB : ∀ y ∈ ({r.2} : Finset SB), y ∈ freeB ((M.erase p).erase r) := by
      intro y hy; rw [Finset.mem_singleton.mp hy]; exact hrB
    have hstep : ∀ (S : Finset SA) (T : Finset SB), p.1 ∈ S ∨ p.2 ∈ T → r.1 ∈ S ∨ r.2 ∈ T →
        (∀ x ∈ S, x ∈ freeA ((M.erase p).erase r)) →
        (∀ y ∈ T, y ∈ freeB ((M.erase p).erase r)) →
        liveM M S T = (M.erase p).erase r := by
      intro S T hpST hrST hfS hfT
      rw [← liveM_erase (p := p) M S T hpST, ← liveM_erase (p := r) (M.erase p) S T hrST]
      exact liveM_of_free hfS hfT
    have h4 : liveM M ({r.1} : Finset SA) ({r.2} : Finset SB) = M.erase r := by
      rw [← liveM_erase (p := r) M _ _ (Or.inl (Finset.mem_singleton_self _))]
      exact liveM_of_free (fun x hx => by
          rw [Finset.mem_singleton.mp hx]; exact fst_freeA_erase hM hrM)
        (fun y hy => by rw [Finset.mem_singleton.mp hy]; exact snd_freeB_erase hM hrM)
    rw [Q_kill_eval hθA hθB hρ hq hπA hπB hM (card_pair_eq hne1) (card_pair_eq hne2)
        (by rw [hstep _ _ (Or.inl (Finset.mem_insert_self _ _))
          (Or.inl (by simp)) hlA hlB, hcard2]),
      Q_kill_eval hθA hθB hρ hq hπA hπB hM (card_pair_eq hne1) (Finset.card_singleton _)
        (by rw [hstep _ _ (Or.inl (Finset.mem_insert_self _ _))
          (Or.inl (by simp)) hlA hsB, hcard2]),
      Q_kill_eval hθA hθB hρ hq hπA hπB hM (Finset.card_singleton _) (card_pair_eq hne2)
        (by rw [hstep _ _ (Or.inr (Finset.mem_insert_self _ _))
          (Or.inl (by simp)) hsA hlB, hcard2]),
      Q_kill_eval hθA hθB hρ hq hπA hπB hM (Finset.card_singleton _) (Finset.card_singleton _)
        (by rw [h4, Finset.card_erase_of_mem hrM])]
  rw [matchingRecursionSource, Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun m hm => r1
      k hk m hm,
    Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun p hp => r2 k hk p hp,
    Finset.sum_congr rfl fun l hl => Finset.sum_congr rfl fun n hn => r3 l hl n hn,
    Finset.sum_congr rfl fun l hl => Finset.sum_congr rfl fun p hp => r4 l hl p hp,
    Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun r hr => r5 p hp r hr,
    sum_erase_const, sum_prod_const, sum_erase_const, sum_prod_const, sum_erase_const,
    hfA, hfB, phiRecursionSource]
  have hgA : (((Fintype.card SA - M.card) * (Fintype.card SA + M.card - 1) : ℕ) : F)
      = (((Fintype.card SA - M.card) * (Fintype.card SA - M.card - 1) : ℕ) : F)
        + 2 * (((Fintype.card SA - M.card) * M.card : ℕ) : F) := by
    rw [← gamma_count (Fintype.card SA) M.card htA]
    push_cast
    ring
  have hgB : (((Fintype.card SB - M.card) * (Fintype.card SB + M.card - 1) : ℕ) : F)
      = (((Fintype.card SB - M.card) * (Fintype.card SB - M.card - 1) : ℕ) : F)
        + 2 * (((Fintype.card SB - M.card) * M.card : ℕ) : F) := by
    rw [← gamma_count (Fintype.card SB) M.card htB]
    push_cast
    ring
  rw [hgA, hgB]
  ring

theorem dgQ_mul_Phi_sub_eq_phiRecursionSource (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1)
    (i j t : ℕ) (hti : t ≤ i) (htj : t ≤ j) :
    dgQ θA θB ρ i j t * Phi q πA πB i j t
        - ρ * (t : F) * Phi q πA πB i j (t - 1)
        - 2 * (((i - t) * (j - t) : ℕ) : F) * Phi q πA πB i j (t + 1)
      = phiRecursionSource q πA πB i j t := by
  have hcA : Fintype.card (Fin i) = i := Fintype.card_fin i
  have hcB : Fintype.card (Fin j) = j := Fintype.card_fin j
  have hcM : (canM i j t).card = t := card_canM hti htj
  have h := dgQ_mul_Phi_eq_matchingRecursionSource hθA hθB hρ hq (canM i j t) hπA hπB
      (isMatching_canM i j t)
  rw [hcA, hcB, hcM] at h
  have hsrc := matchingRecursionSource_eq_phiRecursionSource hθA hθB hρ hq hπA hπB (canM i j t)
      (isMatching_canM i j t)
  rw [hcA, hcB, hcM] at hsrc
  rw [← hsrc, h]
  ring

end DL1

end Rhone.Probability.SlotDeletion
