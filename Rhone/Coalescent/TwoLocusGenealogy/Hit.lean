/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.TwoLocusGenealogy.Bounds

/-! # Finite-horizon hitting probabilities of the killed ancestral chain -/

@[expose] public section

namespace Rhone.Coalescent.TwoLocusGenealogy

open Finset LinearAlgebra.Recursion

variable {n KA KB : ℕ}
variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}

theorem rhs_nonneg (hθA : 0 ≤ θA) (hθB : 0 ≤ θB) (hρ : 0 ≤ ρ) (hπA : ∀ i, 0 ≤ πA i)
    (hπB : ∀ j, 0 ≤ πB j) {q : Config KA KB → F} (hq : ∀ η, 0 ≤ q η) (ξ : Config KA KB) :
    0 ≤ rhs θA θB ρ πA πB q ξ := by
  have hcast : ∀ m : ℕ, (0 : F) ≤ (m : F) := fun m => Nat.cast_nonneg m
  refine add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg ?_ ?_) ?_) ?_)
    ?_) ?_) ?_
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (hcast _) (hq _)
  · exact Finset.sum_nonneg fun j _ => mul_nonneg (hcast _) (hq _)
  · exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_nonneg (hcast _) (hq _)
  · exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_nonneg (hcast _) (hq _)
  · exact mul_nonneg hθA (Finset.sum_nonneg fun i _ => mul_nonneg (hπA i)
      (add_nonneg (mul_nonneg (hcast _) (hq _))
        (Finset.sum_nonneg fun j _ => mul_nonneg (hcast _) (hq _))))
  · exact mul_nonneg hθB (Finset.sum_nonneg fun j _ => mul_nonneg (hπB j)
      (add_nonneg (mul_nonneg (hcast _) (hq _))
        (Finset.sum_nonneg fun i _ => mul_nonneg (hcast _) (hq _))))
  · exact mul_nonneg hρ (Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => mul_nonneg (hcast _) (hq _))

theorem rhs_mono (hθA : 0 ≤ θA) (hθB : 0 ≤ θB) (hρ : 0 ≤ ρ) (hπA : ∀ i, 0 ≤ πA i)
    (hπB : ∀ j, 0 ≤ πB j) {q₁ q₂ : Config KA KB → F} (h : ∀ η, q₁ η ≤ q₂ η)
    (ξ : Config KA KB) :
    rhs θA θB ρ πA πB q₁ ξ ≤ rhs θA θB ρ πA πB q₂ ξ := by
  have hd : 0 ≤ rhs θA θB ρ πA πB (fun η => q₂ η - q₁ η) ξ :=
    rhs_nonneg hθA hθB hρ hπA hπB (fun η => sub_nonneg.2 (h η)) ξ
  rw [rhs_sub] at hd
  linarith

def fitN (θA θB ρ : F) (πA : Fin KA → F) (πB : Fin KB → F) : ℕ → Config KA KB → F
  | 0, ξ => if ξ.n = 0 then 1 else 0
  | N + 1, ξ =>
      if ξ.n = 0 then 1 else rhs θA θB ρ πA πB (fitN θA θB ρ πA πB N) ξ /
          LinearAlgebra.Recursion.diag θA θB ρ ξ

omit [LinearOrder F] [IsStrictOrderedRing F] in
@[simp] theorem fitN_of_n_eq_zero (N : ℕ) {ξ : Config KA KB} (h : ξ.n = 0) :
    fitN θA θB ρ πA πB N ξ = 1 := by
  cases N <;> simp [fitN, h]

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem fitN_succ_of_ne {ξ : Config KA KB} (N : ℕ) (h : ξ.n ≠ 0) :
    fitN θA θB ρ πA πB (N + 1) ξ
      = rhs θA θB ρ πA πB (fitN θA θB ρ πA πB N) ξ / LinearAlgebra.Recursion.diag θA θB ρ ξ := by
  rw [fitN, ite_eq_right h]

theorem fitN_nonneg (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (hπA : ∀ i, 0 ≤ πA i)
    (hπB : ∀ j, 0 ≤ πB j) (N : ℕ) (ξ : Config KA KB) : 0 ≤ fitN θA θB ρ πA πB N ξ := by
  induction N generalizing ξ with
  | zero => rw [fitN]; split_ifs <;> norm_num
  | succ N ih =>
    by_cases h : ξ.n = 0
    · rw [fitN_of_n_eq_zero _ h]; norm_num
    · rw [fitN_succ_of_ne N h]
      exact div_nonneg (rhs_nonneg hθA.le hθB.le hρ hπA hπB (fun η => ih η) ξ)
        (diag_pos hθA hθB hρ (by omega)).le

theorem fitN_le_one (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (hπA : ∀ i, 0 ≤ πA i)
    (hsA : ∑ i, πA i = 1) (hπB : ∀ j, 0 ≤ πB j) (hsB : ∑ j, πB j = 1) (N : ℕ)
    (ξ : Config KA KB) : fitN θA θB ρ πA πB N ξ ≤ 1 := by
  induction N generalizing ξ with
  | zero => rw [fitN]; split_ifs <;> norm_num
  | succ N ih =>
    by_cases h : ξ.n = 0
    · rw [fitN_of_n_eq_zero _ h]
    · have hd : 0 < LinearAlgebra.Recursion.diag θA θB ρ ξ := diag_pos hθA hθB hρ (by omega)
      rw [fitN_succ_of_ne N h, div_le_one hd]
      exact le_trans (rhs_mono hθA.le hθB.le hρ hπA hπB (fun η => ih η) ξ)
        (rhs_one_le_diag hθA.le hθB.le hπA hsA hπB hsB ξ)

theorem fitN_mono (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (hπA : ∀ i, 0 ≤ πA i)
    (hπB : ∀ j, 0 ≤ πB j) (N : ℕ) (ξ : Config KA KB) :
    fitN θA θB ρ πA πB N ξ ≤ fitN θA θB ρ πA πB (N + 1) ξ := by
  induction N generalizing ξ with
  | zero =>
    by_cases h : ξ.n = 0
    · rw [fitN_of_n_eq_zero _ h, fitN_of_n_eq_zero _ h]
    · rw [fitN, ite_eq_right h]
      exact fitN_nonneg hθA hθB hρ hπA hπB 1 ξ
  | succ N ih =>
    by_cases h : ξ.n = 0
    · rw [fitN_of_n_eq_zero _ h, fitN_of_n_eq_zero _ h]
    · have hd : 0 < LinearAlgebra.Recursion.diag θA θB ρ ξ := diag_pos hθA hθB hρ (by omega)
      rw [fitN_succ_of_ne N h, fitN_succ_of_ne (N + 1) h]
      exact div_le_div_of_nonneg_right (rhs_mono hθA.le hθB.le hρ hπA hπB (fun η => ih η) ξ) hd.le

theorem fitN_mono' (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (hπA : ∀ i, 0 ≤ πA i)
    (hπB : ∀ j, 0 ≤ πB j) (ξ : Config KA KB) :
    Monotone fun N => fitN θA θB ρ πA πB N ξ :=
  monotone_nat_of_le_succ fun N => fitN_mono hθA hθB hρ hπA hπB N ξ

variable {σA : Fin n → Fin KA} {σB : Fin n → Fin KB}

def hitN (σA : Fin n → Fin KA) (σB : Fin n → Fin KB) (θA θB ρ : F) (πA : Fin KA → F)
    (πB : Fin KB → F) : ℕ → Finset (Lin n) → F
  | 0, L => if L = ∅ then 1 else 0
  | N + 1, L =>
      if L = ∅ then 1
      else step σA σB θA θB ρ πA πB (hitN σA σB θA θB ρ πA πB N) L / dtot θA θB ρ L

omit [LinearOrder F] [IsStrictOrderedRing F] in
@[simp] theorem hitN_empty (N : ℕ) : hitN σA σB θA θB ρ πA πB N (∅ : Finset (Lin n)) = 1 := by
  cases N <;> simp [hitN]

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem hitN_succ_of_ne {L : Finset (Lin n)} (N : ℕ) (h : L ≠ ∅) :
    hitN σA σB θA θB ρ πA πB (N + 1) L
      = step σA σB θA θB ρ πA πB (hitN σA σB θA θB ρ πA πB N) L / dtot θA θB ρ L := by
  rw [hitN, ite_eq_right h]

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem matchB_eq_zero {T : Finset (Fin n)} (h : ¬ MonoB σB (T, T)) :
    matchB σB πB T = (0 : F) := by
  refine Finset.sum_eq_zero fun j _ => ite_eq_right fun hc => h ?_
  exact fun k hk l hl => by rw [hc k hk, hc l hl]

theorem MonoA.subset {p q : Lin n} (h : MonoA σA p) (hs : q.1 ⊆ p.1) : MonoA σA q :=
  fun k hk l hl => h k (hs hk) l (hs hl)

theorem MonoB.subset {p q : Lin n} (h : MonoB σB p) (hs : q.2 ⊆ p.2) : MonoB σB q :=
  fun k hk l hl => h k (hs hk) l (hs hl)

theorem notClean_of_mem {L : Finset (Lin n)} {r : Lin n} (hr : r ∈ L)
    (hbad : ¬ MonoA σA r ∨ ¬ MonoB σB r) : ¬ Clean σA σB L := by
  intro hcl
  rcases hbad with h | h
  · exact h (hcl.monoA hr)
  · exact h (hcl.monoB hr)

theorem exists_bad_of_notClean {L : Finset (Lin n)} (h : ¬ Clean σA σB L) :
    ∃ r ∈ L, ¬ MonoA σA r ∨ ¬ MonoB σB r := by
  by_contra hc
  refine h fun p hp => ?_
  by_cases h1 : MonoA σA p
  · by_cases h2 : MonoB σB p
    · exact ⟨h1, h2⟩
    · exact absurd ⟨p, hp, Or.inr h2⟩ hc
  · exact absurd ⟨p, hp, Or.inl h1⟩ hc

theorem notClean_coalL {L : Finset (Lin n)} {r : Lin n} (hr : r ∈ L)
    (hbad : ¬ MonoA σA r ∨ ¬ MonoB σB r) (p q : Lin n) : ¬ Clean σA σB (coalL L p q) := by
  intro hcl
  by_cases hrp : r = p
  · subst hrp
    have hm : (r.1 ∪ q.1, r.2 ∪ q.2) ∈ coalL L r q := Finset.mem_insert_self _ _
    rcases hbad with h | h
    · exact h ((hcl.monoA hm).subset Finset.subset_union_left)
    · exact h ((hcl.monoB hm).subset Finset.subset_union_left)
  · by_cases hrq : r = q
    · subst hrq
      have hm : (p.1 ∪ r.1, p.2 ∪ r.2) ∈ coalL L p r := Finset.mem_insert_self _ _
      rcases hbad with h | h
      · exact h ((hcl.monoA hm).subset Finset.subset_union_right)
      · exact h ((hcl.monoB hm).subset Finset.subset_union_right)
    · exact notClean_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_erase.2 ⟨hrq, Finset.mem_erase.2 ⟨hrp, hr⟩⟩)) hbad hcl

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem hitN_eq_zero (N : ℕ) {L : Finset (Lin n)} (hncl : ¬ Clean σA σB L) :
    hitN σA σB θA θB ρ πA πB N L = 0 := by
  induction N generalizing L with
  | zero =>
    obtain ⟨r, hrL, _⟩ := exists_bad_of_notClean hncl
    rw [hitN, ite_eq_right (Finset.ne_empty_of_mem hrL)]
  | succ N ih =>
    obtain ⟨r, hrL, hbad⟩ := exists_bad_of_notClean hncl
    rw [hitN_succ_of_ne N (Finset.ne_empty_of_mem hrL)]
    have hstep : step σA σB θA θB ρ πA πB (hitN σA σB θA θB ρ πA πB N) L = 0 := by
      have h1 : (∑ p ∈ L, ∑ q ∈ L.erase p,
          hitN σA σB θA θB ρ πA πB N (coalL L p q)) = 0 :=
        Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ =>
          ih (notClean_coalL hrL hbad p q)
      have h2 : (∑ p ∈ carA L, matchA σA πA p.1
          * hitN σA σB θA θB ρ πA πB N (mutAL L p)) = 0 := by
        refine Finset.sum_eq_zero fun p hp => ?_
        by_cases hrp : r = p
        · subst hrp
          rcases hbad with h | h
          · rw [matchA_eq_zero h, zero_mul]
          · have h2' : r.2.Nonempty := nonempty_of_not_monoB h
            have hL : mutAL L r = insert ((∅ : Finset (Fin n)), r.2) (L.erase r) := by
              rw [mutAL, ite_eq_right (Finset.nonempty_iff_ne_empty.1 h2')]
            rw [hL, ih (notClean_of_mem (r := ((∅ : Finset (Fin n)), r.2))
              (Finset.mem_insert_self _ _) (Or.inr h)), mul_zero]
        · have hrM : r ∈ mutAL L p := by
            rw [mutAL]
            split_ifs
            · exact Finset.mem_erase.2 ⟨hrp, hrL⟩
            · exact Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hrp, hrL⟩)
          rw [ih (notClean_of_mem hrM hbad), mul_zero]
      have h3 : (∑ p ∈ carB L, matchB σB πB p.2
          * hitN σA σB θA θB ρ πA πB N (mutBL L p)) = 0 := by
        refine Finset.sum_eq_zero fun p hp => ?_
        by_cases hrp : r = p
        · subst hrp
          rcases hbad with h | h
          · have h1' : r.1.Nonempty := nonempty_of_not_monoA h
            have hL : mutBL L r = insert (r.1, (∅ : Finset (Fin n))) (L.erase r) := by
              rw [mutBL, ite_eq_right (Finset.nonempty_iff_ne_empty.1 h1')]
            rw [hL, ih (notClean_of_mem (r := (r.1, (∅ : Finset (Fin n))))
              (Finset.mem_insert_self _ _) (Or.inl h)), mul_zero]
          · rw [matchB_eq_zero h, zero_mul]
        · have hrM : r ∈ mutBL L p := by
            rw [mutBL]
            split_ifs
            · exact Finset.mem_erase.2 ⟨hrp, hrL⟩
            · exact Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hrp, hrL⟩)
          rw [ih (notClean_of_mem hrM hbad), mul_zero]
      have h4 : (∑ p ∈ carC L, hitN σA σB θA θB ρ πA πB N (recL L p)) = 0 := by
        refine Finset.sum_eq_zero fun p hp => ?_
        refine ih ?_
        by_cases hrp : r = p
        · subst hrp
          rcases hbad with h | h
          · exact notClean_of_mem (L := recL L r) (r := (r.1, (∅ : Finset (Fin n))))
              (Finset.mem_insert_self _ _) (Or.inl h)
          · exact notClean_of_mem (L := recL L r) (r := ((∅ : Finset (Fin n)), r.2))
              (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) (Or.inr h)
        · exact notClean_of_mem (L := recL L p)
            (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
              (Finset.mem_erase.2 ⟨hrp, hrL⟩))) hbad
      rw [step, h1, h2, h3, h4]
      ring
    rw [hstep, zero_div]

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem hitN_eq_fitN (N : ℕ) {L : Finset (Lin n)}
    (hw : WF L) (hcl : Clean σA σB L) :
    hitN σA σB θA θB ρ πA πB N L = fitN θA θB ρ πA πB N (cfg σA σB L) := by
  induction N generalizing L with
  | zero =>
    have hz := n_cfg_eq_zero_iff (σA := σA) (σB := σB) hw hcl
    simp only [hitN, fitN]
    by_cases hL : L = ∅
    · rw [ite_eq_left hL, ite_eq_left (hz.2 hL)]
    · rw [ite_eq_right hL, ite_eq_right fun hc => hL (hz.1 hc)]
  | succ N ih =>
    by_cases hL : L = ∅
    · subst hL
      rw [hitN_empty, fitN_of_n_eq_zero _ (by rw [cfg_empty]; exact Config.n_zero)]
    · have hn : (cfg σA σB L).n ≠ 0 := fun h => hL ((n_cfg_eq_zero_iff hw hcl).1 h)
      rw [hitN_succ_of_ne N hL, fitN_succ_of_ne N hn,
        step_eq_rhs (fun M hwM hclM => ih hwM hclM) (fun M h => hitN_eq_zero N h) hw hcl,
        dtot_eq_diag hw hcl]

end Rhone.Coalescent.TwoLocusGenealogy
