/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.SlotDeletion.Surj

/-! # The Beta variance and the two-slot closed form at `K = 2` -/

@[expose] public section

universe u v

namespace Rhone.Probability.SlotDeletion

open Finset LinearAlgebra.Recursion Denominator LinearAlgebra.Multilinear Multilinear

section Beta

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA πB : Fin 2 → F}
variable (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
variable {q : Config 2 2 → F} (hq : IsSolution θA θB ρ πA πB q)
include hθA hθB hρ hq

theorem Phi_two_zero (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1) :
    (1 + θA) * Phi q πA πB 2 0 0 = kap πA := by
  have h := phi_A_rec hθA hθB hρ hq hπA hπB (show 2 ≤ 2 by omega)
  have e1 : (2 : ℕ) - 1 = 1 := rfl
  have e2 : (2 : ℕ) - 2 = 0 := rfl
  rw [e1, e2, Phi_zero_zero hq, Phi_i_one hθA hθB hρ hq hπA 0 0, Nat.cast_one] at h
  linear_combination h

theorem Phi_two_zero_eq (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1) :
    Phi q πA πB 2 0 0 = kap πA / (1 + θA) := by
  have hne : (1 : F) + θA ≠ 0 := by positivity
  field_simp
  linear_combination Phi_two_zero hθA hθB hρ hq hπA hπB

end Beta

section ConstOne

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA πB : Fin 2 → F}
variable (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
variable {q : Config 2 2 → F} (hq : IsSolution θA θB ρ πA πB q)
variable {SB : Type v} [Fintype SB] [DecidableEq SB]
include hθA hθB hρ hq

theorem Q_const_one_empty {SA : Type u} [Fintype SA] [DecidableEq SA]
    (hcard : Fintype.card SA = 0) (M : Finset (SA × SB)) (hM : IsMatching M)
    (w : SB → Fin 2 → F) :
    Q q M (fun _ => (1 : Fin 2 → F)) w
      = ∑ β : SB → Fin 2, (∏ v, w v (β v)) * qOne θB πB (mBof β) := by
  have hu : (univ : Finset SA) = ∅ := Finset.card_eq_zero.mp (by rw [Finset.card_univ, hcard])
  have hterm : ∀ α : SA → Fin 2,
      (∏ u : SA, (1 : Fin 2 → F) (α u)) * qOne θA πA (mAof α) = 1 := by
    intro α
    have hm : mAof α = fun _ => 0 := by
      funext i
      rw [mAof, hu, Finset.filter_empty, Finset.card_empty]
    rw [hm, qOne_zero, mul_one]
    simp
  have hcardfun : Fintype.card (SA → Fin 2) = 1 := by
    rw [Fintype.card_fun, hcard]
    simp
  rw [Q_factor hθA hθB hρ hq M hM (Or.inl (by omega)) _ w,
    Finset.sum_congr rfl fun α (_ : α ∈ univ) => hterm α, Finset.sum_const, Finset.card_univ,
    hcardfun, one_smul, one_mul]

theorem Q_const_one_aux (hπA : ∑ i, πA i = 1) :
    ∀ (n : ℕ) {SA : Type u} [Fintype SA] [DecidableEq SA] (M : Finset (SA × SB))
      (w : SB → Fin 2 → F), IsMatching M → Fintype.card SA + M.card ≤ n →
      Q q M (fun _ => (1 : Fin 2 → F)) w
        = ∑ β : SB → Fin 2, (∏ v, w v (β v)) * qOne θB πB (mBof β) := by
  intro n
  induction n with
  | zero =>
      intro SA _ _ M w hM hle
      exact Q_const_one_empty hθA hθB hρ hq (by omega) M hM w
  | succ n ih =>
      intro SA _ _ M w hM hle
      rcases isEmpty_or_nonempty SA with hE | ⟨⟨u₀⟩⟩
      · exact Q_const_one_empty hθA hθB hρ hq Fintype.card_eq_zero M hM w
      · by_cases hfree : u₀ ∈ freeA M
        · rw [Q_restrA hθA hθB hρ hq hπA hfree _ rfl w]
          have hcard : Fintype.card {x : SA // x ≠ u₀} + 1 = Fintype.card SA := card_sub_ne u₀
          exact ih (restrA u₀ M) w (isMatching_restrA hM)
            (by rw [card_restrA hfree]; omega)
        · obtain ⟨v, hv⟩ := mem_domA.mp (by simpa [freeA, Finset.mem_sdiff] using hfree)
          rw [Q_eraseA hθA hθB hρ hq hπA hM hv _ rfl w]
          have hMp : 1 ≤ M.card := Finset.card_pos.mpr ⟨(u₀, v), hv⟩
          exact ih (M.erase (u₀, v)) w (isMatching_erase hM _)
            (by rw [Finset.card_erase_of_mem hv]; omega)

variable {SA : Type u} [Fintype SA] [DecidableEq SA]

theorem Q_const_one (hπA : ∑ i, πA i = 1) (M : Finset (SA × SB)) (hM : IsMatching M)
    (w : SB → Fin 2 → F) :
    Q q M (fun _ => (1 : Fin 2 → F)) w
      = ∑ β : SB → Fin 2, (∏ v, w v (β v)) * qOne θB πB (mBof β) :=
  Q_const_one_aux hθA hθB hρ hq hπA _ M w hM le_rfl

theorem Q_const_one_basis (hπA : ∑ i, πA i = 1) (M : Finset (SA × SB)) (hM : IsMatching M)
    (β : SB → Fin 2) :
    Q q M (fun _ => (1 : Fin 2 → F)) (fun v => Pi.single (β v) 1) = qOne θB πB (mBof β) := by
  rw [Q_const_one hθA hθB hρ hq hπA M hM]
  simp only [prod_single_apply]
  rw [Finset.sum_eq_single β (fun b _ hb => by simp [hb]) fun hb => absurd (Finset.mem_univ β) hb]
  simp

end ConstOne

section TwoSlots

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA πB : Fin 2 → F}
variable (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
variable {q : Config 2 2 → F} (hq : IsSolution θA θB ρ πA πB q)
variable {SA SB : Type*} [Fintype SA] [DecidableEq SA] [Fintype SB] [DecidableEq SB]
include hθA hθB hρ hq

theorem Q_kill_one_A (hπA : πA 0 + πA 1 = 1) (hcard : Fintype.card SA = 2)
    {M : Finset (SA × SB)} (hM : IsMatching M) (u₀ : SA) (w : SB → Fin 2 → F) :
    Q q M (killAt (fvec πA) {u₀}) w = 0 := by
  have hπA' : ∑ i, πA i = 1 := by rw [Fin.sum_univ_two]; exact hπA
  have hkill : killAt (fvec πA) ({u₀} : Finset SA) u₀ = 1 :=
    killAt_of_mem _ (Finset.mem_singleton_self u₀)
  have hres : (fun (x : {x : SA // x ≠ u₀}) => killAt (fvec πA) ({u₀} : Finset SA) (x : SA))
      = fun _ => fvec πA := by
    funext x
    simp only [killAt, Finset.mem_singleton, x.2, ite_false]
  have hcard' : Fintype.card {x : SA // x ≠ u₀} = 1 := by
    have := card_sub_ne (SA := SA) u₀
    omega
  by_cases hfree : u₀ ∈ freeA M
  · rw [Q_restrA hθA hθB hρ hq hπA' hfree _ hkill w, hres]
    exact Q_eq_zero_of_one_A_slot hθA hθB hρ hq _ (isMatching_restrA hM) hcard' _ _
      fun _ => mean_fvec hπA
  · obtain ⟨v, hv⟩ := mem_domA.mp (by simpa [freeA, Finset.mem_sdiff] using hfree)
    have hfree' : u₀ ∈ freeA (M.erase (u₀, v)) := fst_freeA_erase hM hv
    rw [Q_eraseA hθA hθB hρ hq hπA' hM hv _ hkill w,
      Q_restrA hθA hθB hρ hq hπA' hfree' _ hkill w, hres]
    exact Q_eq_zero_of_one_A_slot hθA hθB hρ hq _ (isMatching_restrA (isMatching_erase hM _))
      hcard' _ _ fun _ => mean_fvec hπA

theorem centred_two_slots (hπA : πA 0 + πA 1 = 1) (hcard : Fintype.card SA = 2)
    {u₁ u₂ : SA} (hne : u₁ ≠ u₂) {M : Finset (SA × SB)} (hM : IsMatching M)
    (α : SA → Fin 2) (w : SB → Fin 2 → F) :
    Q q M (fun u => Pi.single (α u) 1) w
      = πA (α u₁) * πA (α u₂) * Q q M (fun _ => (1 : Fin 2 → F)) w
        + eps F (α u₁) * eps F (α u₂) * Q q M (fun _ => fvec πA) w := by
  have hcpair : ({u₁, u₂} : Finset SA).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
  have huniv : (univ : Finset SA) = {u₁, u₂} :=
    (Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      (le_of_eq (by rw [Finset.card_univ, hcard, hcpair]))).symm
  have hA : ∀ S : Finset SA,
      (fun u => if u ∈ S then centre πA (Pi.single (α u) 1) else (1 : Fin 2 → F))
        = fun u => if u ∈ S then eps F (α u) • fvec πA else 1 := by
    intro S
    funext u
    by_cases h : u ∈ S
    · rw [ite_eq_left h, ite_eq_left h, centre_single hπA]
    · rw [ite_eq_right h, ite_eq_right h]
  have hone : ∀ S : Finset SA, S.card = 1 →
      (∏ u ∈ Sᶜ, mean πA ((fun u => (Pi.single (α u) 1 : Fin 2 → F)) u))
        * Q q M (fun u => if u ∈ S then centre πA (Pi.single (α u) 1) else 1) w = 0 := by
    intro S hS
    have hcompl : Sᶜ.card = 1 := by rw [Finset.card_compl, hcard, hS]
    obtain ⟨u₀, hu₀⟩ := Finset.card_eq_one.mp hcompl
    rw [hA S, Q_pull_scalars_A q M πA w S (fun u => eps F (α u)), hu₀,
      Q_kill_one_A hθA hθB hρ hq hπA hcard hM u₀ w]
    ring
  have hdrop : ∀ S ∈ (univ : Finset (Finset SA)),
      S ∉ ({∅, univ} : Finset (Finset SA)) →
      (∏ u ∈ Sᶜ, mean πA ((fun u => (Pi.single (α u) 1 : Fin 2 → F)) u))
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
    have : (univ : Finset SA).card = 0 := by rw [← hc, Finset.card_empty]
    rw [Finset.card_univ, hcard] at this
    omega
  rw [(Q_isMultiA q M w).centred_expansion πA (fun u => Pi.single (α u) 1),
    ← Finset.sum_subset (Finset.subset_univ ({∅, univ} : Finset (Finset SA))) hdrop,
    Finset.sum_pair hemp]
  have hz : (fun u => if u ∈ (∅ : Finset SA) then centre πA (Pi.single (α u) 1)
      else (1 : Fin 2 → F)) = fun _ => 1 := by
    funext u; simp
  have hfull : Q q M (fun u => if u ∈ (univ : Finset SA) then centre πA (Pi.single (α u) 1)
        else (1 : Fin 2 → F)) w
      = (∏ u ∈ (univ : Finset SA), eps F (α u)) * Q q M (fun _ => fvec πA) w := by
    rw [hA univ, Q_pull_scalars_A q M πA w univ (fun u => eps F (α u)), Finset.compl_univ,
      killAt_empty]
  rw [hz, hfull, Finset.compl_empty, Finset.compl_univ, Finset.prod_empty,
    Finset.prod_congr rfl fun u (_ : u ∈ (univ : Finset SA)) => mean_single πA (α u),
    huniv, Finset.prod_pair hne, Finset.prod_pair hne]
  ring

end TwoSlots

section Theorem3

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA πB : Fin 2 → F}

theorem UA_eq (hπA : πA 0 + πA 1 = 1) (i₁ i₂ : Fin 2) :
    πA i₁ * ((if i₁ = i₂ then (1 : F) else 0) - πA i₂) = eps F i₁ * eps F i₂ * kap πA := by
  have h00 : πA 0 * ((if (0 : Fin 2) = 0 then (1 : F) else 0) - πA 0)
      = eps F 0 * eps F 0 * kap πA := by
    rw [ite_eq_left rfl, eps_zero, kap]
    linear_combination (-(πA 0)) * hπA
  have h01 : πA 0 * ((if (0 : Fin 2) = 1 then (1 : F) else 0) - πA 1)
      = eps F 0 * eps F 1 * kap πA := by
    rw [ite_eq_right (by decide), eps_zero, eps_one, kap]
    ring
  have h10 : πA 1 * ((if (1 : Fin 2) = 0 then (1 : F) else 0) - πA 0)
      = eps F 1 * eps F 0 * kap πA := by
    rw [ite_eq_right (by decide), eps_zero, eps_one, kap]
    ring
  have h11 : πA 1 * ((if (1 : Fin 2) = 1 then (1 : F) else 0) - πA 1)
      = eps F 1 * eps F 1 * kap πA := by
    rw [ite_eq_left rfl, eps_one, kap]
    linear_combination (-(πA 1)) * hπA
  fin_cases i₁ <;> fin_cases i₂
  · simpa using h00
  · simpa using h01
  · simpa using h10
  · simpa using h11

variable (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
variable {q : Config 2 2 → F} (hq : IsSolution θA θB ρ πA πB q)
variable {SA : Type u} [Fintype SA] [DecidableEq SA]
include hθA hθB hρ hq

omit [DecidableEq SA] in
theorem qOne_two_slots (hπA : πA 0 + πA 1 = 1)
    (hcard : Fintype.card SA = 2) {u₁ u₂ : SA} (hne : u₁ ≠ u₂) (α : SA → Fin 2) :
    qOne θA πA (mAof α)
      = πA (α u₁) * πA (α u₂) + eps F (α u₁) * eps F (α u₂) * Phi q πA πB 2 0 0 := by
  classical
  have hπA' : ∑ i, πA i = 1 := by rw [Fin.sum_univ_two]; exact hπA
  have hM0 : IsMatching (∅ : Finset (SA × Fin 0)) := ⟨by simp, by simp⟩
  have hmB : mBof (fun _ : Fin 0 => (0 : Fin 2)) = fun _ => 0 := by
    funext j
    rw [mBof, Finset.eq_empty_of_isEmpty ((univ : Finset (Fin 0)).filter _), Finset.card_empty]
  have h1 : Q q (∅ : Finset (SA × Fin 0)) (fun u => Pi.single (α u) 1)
      (fun _ : Fin 0 => (Pi.single (0 : Fin 2) 1 : Fin 2 → F)) = qOne θA πA (mAof α) := by
    rw [Q_basis (β := fun _ : Fin 0 => (0 : Fin 2)), eq_qHat_of_min_le_one hθA hθB hρ hq _
      (Or.inr (by rw [nB_xi _ _ _ hM0]; simp)), qHat, mA_xi _ _ _ hM0, mB_xi _ _ _ hM0, hmB,
      qOne_zero, mul_one]
  have h2 : Q q (∅ : Finset (SA × Fin 0)) (fun _ => (1 : Fin 2 → F))
      (fun _ : Fin 0 => (Pi.single (0 : Fin 2) 1 : Fin 2 → F)) = 1 := by
    rw [Q_const_one_basis hθA hθB hρ hq hπA' _ hM0 (fun _ : Fin 0 => (0 : Fin 2)), hmB,
      qOne_zero]
  have hsub : (fun _ : Fin 0 => (Pi.single (0 : Fin 2) 1 : Fin 2 → F))
      = fun _ => fvec πB := funext fun v => v.elim0
  have h3 : Q q (∅ : Finset (SA × Fin 0)) (fun _ => fvec πA)
      (fun _ : Fin 0 => (Pi.single (0 : Fin 2) 1 : Fin 2 → F)) = Phi q πA πB 2 0 0 := by
    rw [hsub]
    exact Phi_eq q πA πB hM0 hcard (by simp) (by simp) (by omega) (by omega)
  rw [← h1, centred_two_slots hθA hθB hρ hq hπA hcard hne hM0 α _, h2, mul_one, h3]

variable {SB : Type v} [Fintype SB] [DecidableEq SB]

theorem q_sub_qHat_two_slots (hπA : πA 0 + πA 1 = 1) (hcard : Fintype.card SA = 2) {u₁ u₂ : SA}
    (hne : u₁ ≠ u₂)
    (M : Finset (SA × SB)) (hM : IsMatching M) (α : SA → Fin 2) (β : SB → Fin 2) :
    q (xi M α β) - qHat θA θB πA πB (xi M α β)
      = eps F (α u₁) * eps F (α u₂)
        * (Q q M (fun _ => fvec πA) (fun v => Pi.single (β v) 1)
            - Phi q πA πB 2 0 0 * qOne θB πB (mBof β)) := by
  have hπA' : ∑ i, πA i = 1 := by rw [Fin.sum_univ_two]; exact hπA
  have hq1 : q (xi M α β)
      = πA (α u₁) * πA (α u₂) * qOne θB πB (mBof β)
        + eps F (α u₁) * eps F (α u₂)
          * Q q M (fun _ => fvec πA) (fun v => Pi.single (β v) 1) := by
    rw [← Q_basis q M α β, centred_two_slots hθA hθB hρ hq hπA hcard hne hM α _,
      Q_const_one_basis hθA hθB hρ hq hπA' M hM β]
  rw [hq1, qHat, mA_xi M α β hM, mB_xi M α β hM,
    qOne_two_slots hθA hθB hρ hq hπA hcard hne α]
  ring

theorem q_sub_qHat_two_slots_UA (hπA : πA 0 + πA 1 = 1) (hκ : kap πA ≠ 0)
    (hcard : Fintype.card SA = 2) {u₁ u₂ : SA} (hne : u₁ ≠ u₂) (M : Finset (SA × SB))
    (hM : IsMatching M) (α : SA → Fin 2) (β : SB → Fin 2) :
    q (xi M α β) - qHat θA θB πA πB (xi M α β)
      = (πA (α u₁) * ((if α u₁ = α u₂ then (1 : F) else 0) - πA (α u₂)))
        * ((Q q M (fun _ => fvec πA) (fun v => Pi.single (β v) 1)
              - Phi q πA πB 2 0 0 * qOne θB πB (mBof β)) / kap πA) := by
  rw [q_sub_qHat_two_slots hθA hθB hρ hq hπA hcard hne M hM α β, UA_eq hπA]
  field_simp

end Theorem3

end Rhone.Probability.SlotDeletion
