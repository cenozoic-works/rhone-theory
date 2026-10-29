/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.Multilinear.Factor

/-! # DL‑1 — the centred hierarchy, before lumping -/

@[expose] public section

namespace Rhone.Probability.Multilinear

open Finset LinearAlgebra.Recursion Denominator

variable {SA SB : Type*}
variable [Fintype SA] [DecidableEq SA] [Fintype SB] [DecidableEq SB]
variable {F : Type*} [Field F]

def killAt {ι : Type*} [DecidableEq ι] {K : ℕ} (f : Fin K → F) (S : Finset ι) : ι → Fin K → F :=
  fun u => if u ∈ S then 1 else f

section KillAt

variable {ι : Type*} [DecidableEq ι] {K : ℕ} (f : Fin K → F)

theorem killAt_apply_of_notMem {S : Finset ι} {u : ι} (h : u ∉ S) : killAt f S u = f := by
  simp [killAt, h]

theorem killAt_singleton (m : ι) : Function.update (fun _ => f) m 1 = killAt f {m} := by
  funext u
  by_cases h : u = m <;> simp [killAt, h]

theorem killAt_insert (S : Finset ι) (k : ι) :
    Function.update (killAt f S) k 1 = killAt f (insert k S) := by
  funext u
  by_cases h : u = k <;> simp [killAt, h, Function.update_of_ne]

end KillAt

section Merge

variable (q : Config 2 2 → F) (M : Finset (SA × SB)) {πA πB : Fin 2 → F}

omit [Fintype SA] in
theorem hadA_const {k m : SA} (hkm : k ≠ m) (f : Fin 2 → F) :
    hadA k m (fun _ => f) = Function.update (killAt f {m}) k (f * f) := by
  rw [← killAt_singleton f m]
  exact Function.update_comm hkm (f * f) 1 fun _ => f

omit [Fintype SB] in
theorem hadB_const {l n : SB} (hln : l ≠ n) (g : Fin 2 → F) :
    hadB l n (fun _ => g) = Function.update (killAt g {n}) l (g * g) := by
  rw [← killAt_singleton g n]
  exact Function.update_comm hln (g * g) 1 fun _ => g

theorem Q_hadA_const (hπA : πA 0 + πA 1 = 1) {k m : SA} (hkm : k ≠ m)
    (w : SB → Fin 2 → F) :
    Q q M (hadA k m fun _ => fvec πA) w
      = kap πA * Q q M (killAt (fvec πA) (insert k {m})) w
        + gam πA * Q q M (killAt (fvec πA) {m}) w := by
  have hupd : Function.update (killAt (fvec πA) ({m} : Finset SA)) k (fvec πA)
      = killAt (fvec πA) {m} := by
    funext u
    by_cases h : u = k
    · subst h; rw [Function.update_self, killAt_apply_of_notMem _ (by simp [hkm])]
    · rw [Function.update_of_ne h]
  rw [hadA_const hkm, fvec_mul_fvec hπA,
    (Q_isMultiA q M w).add (killAt (fvec πA) {m}) k (kap πA • 1) (gam πA • fvec πA),
    (Q_isMultiA q M w).smul (killAt (fvec πA) {m}) k (kap πA) 1,
    (Q_isMultiA q M w).smul (killAt (fvec πA) {m}) k (gam πA) (fvec πA),
    killAt_insert (fvec πA) {m} k, hupd]

theorem Q_hadB_const (hπB : πB 0 + πB 1 = 1) {l n : SB} (hln : l ≠ n)
    (s : SA → Fin 2 → F) :
    Q q M s (hadB l n fun _ => fvec πB)
      = kap πB * Q q M s (killAt (fvec πB) (insert l {n}))
        + gam πB * Q q M s (killAt (fvec πB) {n}) := by
  have hupd : Function.update (killAt (fvec πB) ({n} : Finset SB)) l (fvec πB)
      = killAt (fvec πB) {n} := by
    funext v
    by_cases h : v = l
    · subst h; rw [Function.update_self, killAt_apply_of_notMem _ (by simp [hln])]
    · rw [Function.update_of_ne h]
  rw [hadB_const hln, fvec_mul_fvec hπB,
    (Q_isMultiB q M s).add (killAt (fvec πB) {n}) l (kap πB • 1) (gam πB • fvec πB),
    (Q_isMultiB q M s).smul (killAt (fvec πB) {n}) l (kap πB) 1,
    (Q_isMultiB q M s).smul (killAt (fvec πB) {n}) l (gam πB) (fvec πB),
    killAt_insert (fvec πB) {n} l, hupd]

theorem Q_hadAB_const (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1)
    {k m : SA} (hkm : k ≠ m) {l n : SB} (hln : l ≠ n) :
    Q q M (hadA k m fun _ => fvec πA) (hadB l n fun _ => fvec πB)
      = kap πA * kap πB * Q q M (killAt (fvec πA) (insert k {m}))
            (killAt (fvec πB) (insert l {n}))
        + kap πA * gam πB * Q q M (killAt (fvec πA) (insert k {m})) (killAt (fvec πB) {n})
        + gam πA * kap πB * Q q M (killAt (fvec πA) {m}) (killAt (fvec πB) (insert l {n}))
        + gam πA * gam πB * Q q M (killAt (fvec πA) {m}) (killAt (fvec πB) {n}) := by
  rw [Q_hadA_const q M hπA hkm, Q_hadB_const q M hπB hln, Q_hadB_const q M hπB hln]
  ring

end Merge

section DL1

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA πB : Fin 2 → F}
variable (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
variable {q : Config 2 2 → F} (hq : IsSolution θA θB ρ πA πB q)
variable (M : Finset (SA × SB))
include hθA hθB hρ hq

theorem dgQ_mul_Q_fvec (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1) (hM : IsMatching M) :
    dgQ θA θB ρ (Fintype.card SA) (Fintype.card SB) M.card
        * Q q M (fun _ => fvec πA) (fun _ => fvec πB)
      = (∑ k ∈ freeA M, ∑ m ∈ (freeA M).erase k,
          (kap πA * Q q M (killAt (fvec πA) (insert k {m})) (fun _ => fvec πB)
            + gam πA * Q q M (killAt (fvec πA) {m}) (fun _ => fvec πB)))
        + 2 * (∑ k ∈ freeA M, ∑ p ∈ M,
          (kap πA * Q q M (killAt (fvec πA) (insert p.1 {k})) (fun _ => fvec πB)
            + gam πA * Q q M (killAt (fvec πA) {k}) (fun _ => fvec πB)))
        + (∑ l ∈ freeB M, ∑ n ∈ (freeB M).erase l,
          (kap πB * Q q M (fun _ => fvec πA) (killAt (fvec πB) (insert l {n}))
            + gam πB * Q q M (fun _ => fvec πA) (killAt (fvec πB) {n})))
        + 2 * (∑ l ∈ freeB M, ∑ p ∈ M,
          (kap πB * Q q M (fun _ => fvec πA) (killAt (fvec πB) (insert p.2 {l}))
            + gam πB * Q q M (fun _ => fvec πA) (killAt (fvec πB) {l})))
        + (∑ p ∈ M, ∑ r ∈ M.erase p,
          (kap πA * kap πB * Q q M (killAt (fvec πA) (insert p.1 {r.1}))
                (killAt (fvec πB) (insert p.2 {r.2}))
            + kap πA * gam πB * Q q M (killAt (fvec πA) (insert p.1 {r.1}))
                (killAt (fvec πB) {r.2})
            + gam πA * kap πB * Q q M (killAt (fvec πA) {r.1})
                (killAt (fvec πB) (insert p.2 {r.2}))
            + gam πA * gam πB * Q q M (killAt (fvec πA) {r.1}) (killAt (fvec πB) {r.2})))
        + 2 * (∑ k ∈ freeA M, ∑ l ∈ freeB M,
          Q q (insert (k, l) M) (fun _ => fvec πA) (fun _ => fvec πB))
        + ρ * (∑ p ∈ M, Q q (M.erase p) (fun _ => fvec πA) (fun _ => fvec πB)) := by
  have hπA' : ∑ i, πA i = 1 := by rw [Fin.sum_univ_two]; exact hπA
  have hπB' : ∑ j, πB j = 1 := by rw [Fin.sum_univ_two]; exact hπB
  have hmutA : (∑ u : SA, mean πA ((fun _ => fvec πA) u)
      * Q q M (Function.update (fun _ => fvec πA) u 1) (fun _ => fvec πB)) = 0 := by
    refine Finset.sum_eq_zero fun u _ => ?_
    rw [mean_fvec hπA, zero_mul]
  have hmutB : (∑ v : SB, mean πB ((fun _ => fvec πB) v)
      * Q q M (fun _ => fvec πA) (Function.update (fun _ => fvec πB) v 1)) = 0 := by
    refine Finset.sum_eq_zero fun v _ => ?_
    rw [mean_fvec hπB, zero_mul]
  rw [dgQ_mul_Q_eq_rhsQ hθA hθB hρ hq M hπA' hπB' hM, rhsQ, hmutA, hmutB]
  rw [Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m hm =>
      Q_hadA_const q M hπA (Ne.symm (Finset.mem_erase.mp hm).1) _,
    Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun p hp =>
      Q_hadA_const q M hπA (fst_ne_of_mem_freeA hk hp) _,
    Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun n hn =>
      Q_hadB_const q M hπB (Ne.symm (Finset.mem_erase.mp hn).1) _,
    Finset.sum_congr rfl fun l hl => Finset.sum_congr rfl fun p hp =>
      Q_hadB_const q M hπB (snd_ne_of_mem_freeB hl hp) _,
    Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun r hr =>
      Q_hadAB_const q M hπA hπB
        (fun hc => (Finset.mem_erase.mp hr).1 (hM.fst p hp r (Finset.mem_erase.mp hr).2 hc).symm)
        (fun hc => (Finset.mem_erase.mp hr).1
          (hM.snd p hp r (Finset.mem_erase.mp hr).2 hc).symm)]
  ring

end DL1

end Rhone.Probability.Multilinear
