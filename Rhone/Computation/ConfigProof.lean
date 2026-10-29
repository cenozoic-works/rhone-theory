/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.ConfigKeyProof

/-! # Canonical-key acceptance -/

@[expose] public section

namespace Rhone.Computation

theorem key_eq_of_parseConfig_eq_ok {input : String} {ka kb : Nat} {c : Config}
    (h : parseConfig input ka kb = .ok c) : c.key = input := by
  unfold parseConfig at h
  cases hr : parseConfigRaw input ka kb with
  | error e => simp [hr] at h
  | ok parsed =>
    by_cases hk : parsed.key = input
    · simp only [hr, hk, ↓reduceIte, Except.ok.injEq] at h
      cases h
      exact hk
    · simp [hr, hk] at h

theorem parseConfig_key (c : Config) (ka kb : Nat)
    (hka : 1 ≤ ka) (hkb : 1 ≤ kb) (hka255 : ka ≤ 255) (hkb255 : kb ≤ 255)
    (ha : c.a.size = ka) (hb : c.b.size = kb) (hc : c.c.size = ka * kb)
    (hu : ∀ n ∈ c.a.toList ++ c.b.toList ++ c.c.toList, n ≤ 65535) :
    parseConfig c.key ka kb = .ok c := by
  have hs : (ka == 0 || kb == 0 || ka > 255 || kb > 255) = false := by
    simp; omega
  have hv : (c.a.toList ++ c.b.toList ++ c.c.toList).any (· > 65535) = false := by
    simp only [List.any_eq_false]
    intro n hn
    simpa using (Nat.not_lt.mpr (hu n hn))
  have hlen : (c.a.toList ++ c.b.toList ++ c.c.toList).length = ka + kb + ka * kb := by
    simp [ha, hb, hc, Nat.add_assoc]
  have htake : (c.a.toList ++ c.b.toList ++ c.c.toList).take ka = c.a.toList := by
    rw [← ha]
    simp [List.append_assoc]
  have hdrop : ((c.a.toList ++ c.b.toList ++ c.c.toList).drop ka).take kb =
      c.b.toList := by
    rw [← ha, ← hb]
    simp [List.append_assoc]
  have hmatrix : (c.a.toList ++ c.b.toList ++ c.c.toList).drop (ka + kb) =
      c.c.toList := by
    rw [← List.drop_drop, ← ha, ← hb]
    simp [List.append_assoc]
  have hp : parseConfigRaw c.key ka kb = .ok c := by
    simp only [parseConfigRaw, hs, keyCounts_key c ka kb ha hb hc hu, hv, hlen,
      htake, hdrop, hmatrix]
    simp only [Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
    cases c
    rfl
  simp [parseConfig, hp]

end Rhone.Computation
