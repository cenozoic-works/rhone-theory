/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.SlotDeletion.Rank
public import Rhone.Probability.GeneralAlphabet.RankOne

/-! # Centred two-slot identity for the sampling probability at general `K_A, K_B` -/

@[expose] public section

universe u v

namespace Rhone.Probability.GeneralAlphabet

open Finset LinearAlgebra.Recursion Denominator LinearAlgebra.Multilinear Multilinear
open LinearAlgebra.SlotDeletion SlotDeletion

variable {KA KB : ℕ}

section UA

variable {F : Type*} [Field F] {K : ℕ} {π : Fin K → F}

def UA (π : Fin K → F) (i j : Fin K) : F := π i * ((if i = j then (1 : F) else 0) - π j)

theorem mean_centre_single_mul (hπ : ∑ k, π k = 1) (i j : Fin K) :
    mean π (centre π (Pi.single i 1) * centre π (Pi.single j 1)) = UA π i j := by
  have hc : ∀ (l k : Fin K),
      centre π (Pi.single l (1 : F)) k = (if k = l then (1 : F) else 0) - π l := by
    intro l k
    rw [centre, mean_single]
    simp [Pi.single_apply]
  have hone : ∀ l : Fin K, (∑ k, π k * (if k = l then (1 : F) else 0)) = π l := by
    intro l
    rw [Finset.sum_eq_single l (fun b _ hb => by simp [hb])
      fun hb => absurd (Finset.mem_univ l) hb]
    simp
  have hpair : (∑ k, π k * ((if k = i then (1 : F) else 0) * (if k = j then (1 : F) else 0)))
      = if i = j then π i else 0 := by
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left rfl, ← hone i]
      exact Finset.sum_congr rfl fun k _ => by by_cases hk : k = i <;> simp [hk]
    · rw [ite_eq_right hij]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : k = i
      · subst hk; simp [hij]
      · simp [hk]
  have hterm : ∀ k : Fin K,
      π k * ((centre π (Pi.single i 1) * centre π (Pi.single j 1)) k)
        = π k * ((if k = i then (1 : F) else 0) * (if k = j then (1 : F) else 0))
          - π j * (π k * (if k = i then (1 : F) else 0))
          - π i * (π k * (if k = j then (1 : F) else 0))
          + π i * π j * π k := by
    intro k
    rw [Pi.mul_apply, hc, hc]
    ring
  have e1 : (∑ k, π j * (π k * (if k = i then (1 : F) else 0))) = π j * π i := by
    rw [← Finset.mul_sum, hone]
  have e2 : (∑ k, π i * (π k * (if k = j then (1 : F) else 0))) = π i * π j := by
    rw [← Finset.mul_sum, hone]
  have e3 : (∑ k : Fin K, π i * π j * π k) = π i * π j := by
    rw [← Finset.mul_sum, hπ, mul_one]
  rw [mean, Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_sub_distrib, hpair, e1, e2, e3, UA]
  by_cases hij : i = j
  · rw [ite_eq_left hij, ite_eq_left hij]; ring
  · rw [ite_eq_right hij, ite_eq_right hij]; ring

end UA

section Expand

variable {SA : Type u} {SB : Type v}
variable [Fintype SA] [DecidableEq SA] [Fintype SB] [DecidableEq SB]
variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}
variable (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
variable {q : Config KA KB → F} (hq : IsSolution θA θB ρ πA πB q)
include hθA hθB hρ hq

theorem centred_two_slots (hπA : ∑ i, πA i = 1) (hcard : Fintype.card SA = 2)
    {u₁ u₂ : SA} (hne : u₁ ≠ u₂) {M : Finset (SA × SB)} (hM : IsMatching M)
    (α : SA → Fin KA) (w : SB → Fin KB → F) :
    Q q M (fun u => Pi.single (α u) 1) w
      = πA (α u₁) * πA (α u₂) * Q q M (fun _ => (1 : Fin KA → F)) w
        + Q q M (sPair u₁ (centre πA (Pi.single (α u₁) 1))
            (centre πA (Pi.single (α u₂) 1))) w := by
  have hcpair : ({u₁, u₂} : Finset SA).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
  have huniv : (univ : Finset SA) = {u₁, u₂} :=
    (Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      (le_of_eq (by rw [Finset.card_univ, hcard, hcpair]))).symm
  have hone : ∀ S : Finset SA, S.card = 1 →
      (∏ u ∈ Sᶜ, mean πA ((fun u => (Pi.single (α u) 1 : Fin KA → F)) u))
        * Q q M (fun u => if u ∈ S then centre πA (Pi.single (α u) 1) else 1) w = 0 := by
    intro S hS
    have hcompl : Sᶜ.card = 1 := by rw [Finset.card_compl, hcard, hS]
    obtain ⟨u₀, hu₀⟩ := Finset.card_eq_one.mp hcompl
    have hnot : u₀ ∉ S := by
      have h : u₀ ∈ Sᶜ := by rw [hu₀]; exact Finset.mem_singleton_self u₀
      simpa using h
    have hzero : Q q M (fun u => if u ∈ S then centre πA (Pi.single (α u) 1) else 1) w = 0 := by
      refine Q_eq_zero_of_two_slots hθA hθB hρ hq hπA hcard hM (v := u₀) _ ?_ ?_ w
      · show (if u₀ ∈ S then centre πA (Pi.single (α u₀) 1) else (1 : Fin KA → F)) = 1
        rw [ite_eq_right hnot]
      · intro z hz
        have hzS : z ∈ S := by
          by_contra hc
          have h : z ∈ Sᶜ := by simpa using hc
          rw [hu₀, Finset.mem_singleton] at h
          exact hz h
        change mean πA (if z ∈ S then centre πA (Pi.single (α z) 1) else (1 : Fin KA → F)) = 0
        rw [ite_eq_left hzS]
        exact mean_centre πA _ hπA
    rw [hzero, mul_zero]
  have hdrop : ∀ S ∈ (univ : Finset (Finset SA)),
      S ∉ ({∅, univ} : Finset (Finset SA)) →
      (∏ u ∈ Sᶜ, mean πA ((fun u => (Pi.single (α u) 1 : Fin KA → F)) u))
        * Q q M (fun u => if u ∈ S then centre πA (Pi.single (α u) 1) else 1) w = 0 := by
    intro S _ hS
    rw [Finset.mem_insert, Finset.mem_singleton] at hS
    refine hone S ?_
    have hle : S.card ≤ Fintype.card SA := by
      simpa using Finset.card_le_card (Finset.subset_univ S)
    have h0 : S.card ≠ 0 := fun hc => hS (Or.inl (Finset.card_eq_zero.mp hc))
    have h2 : S.card ≠ 2 := fun hc => hS (Or.inr (Finset.eq_univ_of_card S (by rw [hc, hcard])))
    omega
  have hemp : (∅ : Finset SA) ≠ univ := by
    intro hc
    have h : (univ : Finset SA).card = 0 := by rw [← hc, Finset.card_empty]
    rw [Finset.card_univ, hcard] at h
    omega
  have hz : (fun u => if u ∈ (∅ : Finset SA) then centre πA (Pi.single (α u) 1)
      else (1 : Fin KA → F)) = fun _ => 1 := by
    funext u; simp
  have hfull : (fun u => if u ∈ (univ : Finset SA) then centre πA (Pi.single (α u) 1)
      else (1 : Fin KA → F))
      = sPair u₁ (centre πA (Pi.single (α u₁) 1)) (centre πA (Pi.single (α u₂) 1)) := by
    funext u
    rw [ite_eq_left (Finset.mem_univ u)]
    rcases eq_or_eq_of_card_two hcard hne u with h | h
    · rw [h, sPair_self]
    · rw [h, sPair_of_ne (Ne.symm hne)]
  rw [(Q_isMultiA q M w).centred_expansion πA (fun u => Pi.single (α u) 1),
    ← Finset.sum_subset (Finset.subset_univ ({∅, univ} : Finset (Finset SA))) hdrop,
    Finset.sum_pair hemp, hz, hfull, Finset.compl_empty, Finset.compl_univ,
    Finset.prod_empty, one_mul,
    Finset.prod_congr rfl fun u (_ : u ∈ (univ : Finset SA)) => mean_single πA (α u),
    huniv, Finset.prod_pair hne]

end Expand

section AOnly

variable {SA : Type u}

theorem isMatching_empty : IsMatching (∅ : Finset (SA × Fin 0)) := ⟨by simp, by simp⟩

variable [Fintype SA] [DecidableEq SA]
variable {F : Type*} [Field F]

def QA (q : Config KA KB → F) (u₁ : SA) (x y : Fin KA → F) : F :=
  Q q (∅ : Finset (SA × Fin 0)) (sPair u₁ x y) fun _ => (1 : Fin KB → F)

end AOnly

section Theorem3

variable {SA : Type u} {SB : Type v}
variable [Fintype SA] [DecidableEq SA] [Fintype SB] [DecidableEq SB]
variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}
variable (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
variable {q : Config KA KB → F} (hq : IsSolution θA θB ρ πA πB q)
include hθA hθB hρ hq

theorem qOne_two_slots (hπA : ∑ i, πA i = 1) (hcard : Fintype.card SA = 2)
    {u₁ u₂ : SA} (hne : u₁ ≠ u₂) (α : SA → Fin KA) :
    qOne θA πA (mAof α)
      = πA (α u₁) * πA (α u₂)
        + QA (KB := KB) q u₁ (centre πA (Pi.single (α u₁) 1))
            (centre πA (Pi.single (α u₂) 1)) := by
  have hM0 : IsMatching (∅ : Finset (SA × Fin 0)) := isMatching_empty
  have hw : (fun _ : Fin 0 => (1 : Fin KB → F))
      = fun v : Fin 0 => Pi.single ((fun v : Fin 0 => v.elim0 : Fin 0 → Fin KB) v) 1 := by
    funext v; exact v.elim0
  have hmB : mBof (fun v : Fin 0 => v.elim0 : Fin 0 → Fin KB) = fun _ => 0 := by
    funext j; rw [mBof]; simp
  have h1 : Q q (∅ : Finset (SA × Fin 0)) (fun u => Pi.single (α u) 1)
      (fun _ : Fin 0 => (1 : Fin KB → F)) = qOne θA πA (mAof α) := by
    rw [hw, Q_basis, eq_qHat_of_min_le_one hθA hθB hρ hq _
      (Or.inr (by rw [nB_xi _ _ _ hM0]; simp)), qHat, mA_xi _ _ _ hM0, mB_xi _ _ _ hM0, hmB,
      qOne_zero, mul_one]
  have h2 : Q q (∅ : Finset (SA × Fin 0)) (fun _ => (1 : Fin KA → F))
      (fun _ : Fin 0 => (1 : Fin KB → F)) = 1 := by
    rw [hw, Q_const_one_basis hθA hθB hρ hq hπA _ hM0, hmB, qOne_zero]
  rw [← h1, centred_two_slots hθA hθB hρ hq hπA hcard hne hM0 α _, h2, mul_one, QA]

theorem q_sub_qHat_two_slots_centred (hπA : ∑ i, πA i = 1) (hcard : Fintype.card SA = 2)
    {u₁ u₂ : SA} (hne : u₁ ≠ u₂) (M : Finset (SA × SB)) (hM : IsMatching M)
    (α : SA → Fin KA) (β : SB → Fin KB) :
    q (xi M α β) - qHat θA θB πA πB (xi M α β)
      = Q q M (sPair u₁ (centre πA (Pi.single (α u₁) 1))
            (centre πA (Pi.single (α u₂) 1))) (fun v => Pi.single (β v) 1)
        - QA (KB := KB) q u₁ (centre πA (Pi.single (α u₁) 1))
            (centre πA (Pi.single (α u₂) 1)) * qOne θB πB (mBof β) := by
  have hq1 : q (xi M α β)
      = πA (α u₁) * πA (α u₂) * qOne θB πB (mBof β)
        + Q q M (sPair u₁ (centre πA (Pi.single (α u₁) 1))
            (centre πA (Pi.single (α u₂) 1))) (fun v => Pi.single (β v) 1) := by
    rw [← Q_basis q M α β, centred_two_slots hθA hθB hρ hq hπA hcard hne hM α _,
      Q_const_one_basis hθA hθB hρ hq hπA M hM β]
  rw [hq1, qHat, mA_xi M α β hM, mB_xi M α β hM,
    qOne_two_slots hθA hθB hρ hq hπA hcard hne α]
  ring

theorem UA_mul_q_sub_qHat_comm (hπA : ∑ i, πA i = 1) (hπB : ∑ j, πB j = 1)
    (hcard : Fintype.card SA = 2) {u₁ u₂ : SA} (hne : u₁ ≠ u₂)
    (M : Finset (SA × SB)) (hM : IsMatching M) (α α' : SA → Fin KA) (β : SB → Fin KB) :
    UA πA (α' u₁) (α' u₂) * (q (xi M α β) - qHat θA θB πA πB (xi M α β))
      = UA πA (α u₁) (α u₂) * (q (xi M α' β) - qHat θA θB πA πB (xi M α' β)) := by
  have hcen : ∀ i : Fin KA, mean πA (centre πA (Pi.single i 1)) = 0 :=
    fun i => mean_centre πA _ hπA
  have hrk1 := Q_sPair_rank_one (u₁ := u₁) (x := centre πA (Pi.single (α u₁) 1))
    (y := centre πA (Pi.single (α u₂) 1)) (x' := centre πA (Pi.single (α' u₁) 1))
    (y' := centre πA (Pi.single (α' u₂) 1)) hθA hθB hρ hq hπA hπB hcard hne
    (hcen _) (hcen _) (hcen _) (hcen _) M hM (fun v => Pi.single (β v) 1)
  have hrk2 := Q_sPair_rank_one (u₁ := u₁) (x := centre πA (Pi.single (α u₁) 1))
    (y := centre πA (Pi.single (α u₂) 1)) (x' := centre πA (Pi.single (α' u₁) 1))
    (y' := centre πA (Pi.single (α' u₂) 1)) hθA hθB hρ hq hπA hπB hcard hne
    (hcen _) (hcen _) (hcen _) (hcen _) (∅ : Finset (SA × Fin 0)) isMatching_empty
    (fun _ => (1 : Fin KB → F))
  rw [mean_centre_single_mul hπA, mean_centre_single_mul hπA] at hrk1 hrk2
  rw [q_sub_qHat_two_slots_centred hθA hθB hρ hq hπA hcard hne M hM α β,
    q_sub_qHat_two_slots_centred hθA hθB hρ hq hπA hcard hne M hM α' β]
  simp only [QA]
  linear_combination hrk1 - qOne θB πB (mBof β) * hrk2

theorem exists_q_sub_qHat_eq_UA_mul (hπA : ∑ i, πA i = 1) (hπB : ∑ j, πB j = 1)
    (hcard : Fintype.card SA = 2) {u₁ u₂ : SA} (hne : u₁ ≠ u₂)
    {i₀ : Fin KA} (hκ : UA πA i₀ i₀ ≠ 0)
    (M : Finset (SA × SB)) (hM : IsMatching M) (β : SB → Fin KB) :
    ∃ G : F, ∀ α : SA → Fin KA,
      q (xi M α β) - qHat θA θB πA πB (xi M α β) = UA πA (α u₁) (α u₂) * G := by
  refine ⟨(q (xi M (fun _ => i₀) β) - qHat θA θB πA πB (xi M (fun _ => i₀) β)) / UA πA i₀ i₀,
    fun α => ?_⟩
  have h := UA_mul_q_sub_qHat_comm hθA hθB hρ hq hπA hπB hcard hne M hM α (fun _ => i₀) β
  field_simp
  linear_combination h

end Theorem3

section Biallelic

variable {SA : Type u} {SB : Type v}
variable [Fintype SA] [DecidableEq SA] [Fintype SB] [DecidableEq SB]
variable {F : Type*} [Field F]
variable {q : Config KA KB → F}

theorem Q_sPair_smul (hcard : Fintype.card SA = 2) {u₁ u₂ : SA} (hne : u₁ ≠ u₂)
    (M : Finset (SA × SB)) (a b : F) (x y : Fin KA → F) (w : SB → Fin KB → F) :
    Q q M (sPair u₁ (a • x) (b • y)) w = a * b * Q q M (sPair u₁ x y) w := by
  have h1 : ∀ z : Fin KA → F, Function.update (sPair u₁ x y) u₁ z = sPair u₁ z y := by
    intro z
    funext t
    by_cases ht : t = u₁
    · rw [ht, Function.update_self, sPair_self]
    · rw [Function.update_of_ne ht, sPair_of_ne ht, sPair_of_ne ht]
  have h2 : ∀ (z : Fin KA → F) (z' : Fin KA → F),
      Function.update (sPair u₁ z y) u₂ z' = sPair u₁ z z' := by
    intro z z'
    funext t
    rcases eq_or_eq_of_card_two hcard hne t with h | h
    · rw [h, Function.update_of_ne hne, sPair_self, sPair_self]
    · rw [h, Function.update_self, sPair_of_ne (Ne.symm hne)]
  have hy : Function.update (sPair u₁ (a • x) y) u₂ y = sPair u₁ (a • x) y := by
    rw [h2]
  calc Q q M (sPair u₁ (a • x) (b • y)) w
      = Q q M (Function.update (sPair u₁ (a • x) y) u₂ (b • y)) w := by rw [h2]
    _ = b * Q q M (Function.update (sPair u₁ (a • x) y) u₂ y) w :=
        (Q_isMultiA q M w).smul _ _ _ _
    _ = b * Q q M (Function.update (sPair u₁ x y) u₁ (a • x)) w := by rw [hy, h1]
    _ = b * (a * Q q M (Function.update (sPair u₁ x y) u₁ x) w) := by
        rw [(Q_isMultiA q M w).smul]
    _ = a * b * Q q M (sPair u₁ x y) w := by rw [h1]; ring

end Biallelic

section BiallelicA

variable {SA : Type u} {SB : Type v}
variable [Fintype SA] [DecidableEq SA] [Fintype SB] [DecidableEq SB]
variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA : Fin 2 → F} {πB : Fin KB → F}
variable (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
variable {q : Config 2 KB → F} (hq : IsSolution θA θB ρ πA πB q)
include hθA hθB hρ hq

theorem q_sub_qHat_two_slots_biallelicA (hπA : πA 0 + πA 1 = 1) (hcard : Fintype.card SA = 2)
    {u₁ u₂ : SA} (hne : u₁ ≠ u₂)
    (M : Finset (SA × SB)) (hM : IsMatching M) (α : SA → Fin 2) (β : SB → Fin KB) :
    q (xi M α β) - qHat θA θB πA πB (xi M α β)
      = eps F (α u₁) * eps F (α u₂)
        * (Q q M (sPair u₁ (fvec πA) (fvec πA)) (fun v => Pi.single (β v) 1)
            - QA (KB := KB) q u₁ (fvec πA) (fvec πA) * qOne θB πB (mBof β)) := by
  have hπA' : ∑ i, πA i = 1 := by rw [Fin.sum_univ_two]; exact hπA
  have hce : ∀ i : Fin 2, centre πA (Pi.single i 1) = eps F i • fvec πA :=
    fun i => centre_single hπA i
  have hQ : Q q M (sPair u₁ (centre πA (Pi.single (α u₁) 1))
        (centre πA (Pi.single (α u₂) 1))) (fun v => Pi.single (β v) 1)
      = eps F (α u₁) * eps F (α u₂)
        * Q q M (sPair u₁ (fvec πA) (fvec πA)) (fun v => Pi.single (β v) 1) := by
    rw [hce, hce, Q_sPair_smul hcard hne M _ _ _ _ _]
  have hQA : QA (KB := KB) q u₁ (centre πA (Pi.single (α u₁) 1))
        (centre πA (Pi.single (α u₂) 1))
      = eps F (α u₁) * eps F (α u₂) * QA (KB := KB) q u₁ (fvec πA) (fvec πA) := by
    rw [QA, QA, hce, hce, Q_sPair_smul hcard hne _ _ _ _ _ _]
  rw [q_sub_qHat_two_slots_centred hθA hθB hρ hq hπA' hcard hne M hM α β, hQ, hQA]
  ring

theorem exists_q_sub_qHat_eq_UA_mul_biallelicA (hπA : πA 0 + πA 1 = 1) (hπB : ∑ j, πB j = 1)
    (hκ : kap πA ≠ 0) (hcard : Fintype.card SA = 2) {u₁ u₂ : SA} (hne : u₁ ≠ u₂)
    (M : Finset (SA × SB)) (hM : IsMatching M) (β : SB → Fin KB) :
    ∃ G : F, ∀ α : SA → Fin 2,
      q (xi M α β) - qHat θA θB πA πB (xi M α β)
        = πA (α u₁) * ((if α u₁ = α u₂ then (1 : F) else 0) - πA (α u₂)) * G := by
  have hπA' : ∑ i, πA i = 1 := by rw [Fin.sum_univ_two]; exact hπA
  have hU0 : UA πA 0 0 = kap πA := by
    rw [UA, UA_eq hπA, eps_zero]; ring
  obtain ⟨G, hG⟩ := exists_q_sub_qHat_eq_UA_mul hθA hθB hρ hq hπA' hπB hcard hne
    (i₀ := 0) (by rw [hU0]; exact hκ) M hM β
  exact ⟨G, fun α => hG α⟩

end BiallelicA

section PhiBridge

variable {SA : Type u} [Fintype SA] [DecidableEq SA]
variable {F : Type*} [Field F]

theorem QA_eq_Phi (q : Config 2 2 → F) (πA πB : Fin 2 → F) (u₁ : SA)
    (hcard : Fintype.card SA = 2) :
    QA (KB := 2) q u₁ (fvec πA) (fvec πA) = Phi q πA πB 2 0 0 := by
  have hs : sPair u₁ (fvec πA) (fvec πA) = fun _ => fvec πA := by
    funext t; simp [sPair]
  have hw : (fun _ : Fin 0 => (1 : Fin 2 → F)) = fun _ : Fin 0 => fvec πB := by
    funext v; exact v.elim0
  rw [QA, hs, hw]
  exact Phi_eq q πA πB (isMatching_empty (SA := SA)) hcard (by simp) (by simp)
    (by omega) (by omega)

end PhiBridge

end Rhone.Probability.GeneralAlphabet
