/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.ResidueSupport.Support
public import Rhone.Probability.Propagation.Propagate

/-! # Residue propagation for cleared hierarchies without support or separation hypotheses -/

@[expose] public section

namespace Rhone.Probability.ResidueSupport
open Polynomial Matrix Analysis.GenericCoordinates LinearAlgebra.Propagation Propagation

theorem block_eval {L : Type*} [Field L] (φ : CanonicalField →+* L) (r : L) (i j : ℕ) :
    (block i j).eval₂ φ r =
      LinearAlgebra.Tridiag.E L i j (φ canonicalThetaA) (φ canonicalThetaB) r := by
  unfold block
  have h := LinearAlgebra.Tridiag.E_map (Polynomial.eval₂RingHom φ r) i j
    (C canonicalThetaA) (C canonicalThetaB) X
  simpa using h

theorem other_block_ne_zero {L : Type*} [Field L] (φ : CanonicalField →+* L) (r : L)
    {p q i j : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hi : 1 ≤ i) (hj : 1 ≤ j)
    (hne : (i, j) ≠ (p, q)) (hroot : (block p q).eval₂ φ r = 0) :
    LinearAlgebra.Tridiag.E L i j (φ canonicalThetaA) (φ canonicalThetaB) r ≠ 0 := by
  have hc := (E_coprime p q i j (by omega) (by omega) hi hj (Ne.symm hne)).map
    (Polynomial.eval₂RingHom φ r)
  have hz : (block i j).eval₂ φ r ≠ 0 :=
    hc.ne_zero_or_ne_zero.resolve_left (by simpa [block] using hroot)
  rwa [block_eval] at hz

theorem residueFamily_eq_smul_w {L : Type*} [Field L]
    (φ : CanonicalField →+* L) (r : L)
    (N : ℕ → ℕ → ℕ → Polynomial CanonicalField) (κA γA κB γB c : L) (v : ℕ → L)
    {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (hroot : (block p q).eval₂ φ r = 0)
    (hbase : ∀ t, t ≤ min p q → residueFamily φ r N p q t = c * v t)
    (hrec : ∀ i j, p ≤ i → q ≤ j → (i, j) ≠ (p, q) →
      LinearAlgebra.Tridiag.T L i j (φ canonicalThetaA) (φ canonicalThetaB) r *ᵥ
        (fun s : Fin (min i j + 1) => residueFamily φ r N i j (s : ℕ)) =
      fun s : Fin (min i j + 1) => src κA γA κB γB (residueFamily φ r N) i j (s : ℕ)) :
    ∀ i j t, t ≤ min i j → residueFamily φ r N i j t =
      c * w (φ canonicalThetaA) (φ canonicalThetaB) r κA γA κB γB p q v i j t := by
  apply res_eq_smul_w hp hq _ (residueFamily_off φ r N hp hq hroot) hbase hrec
  intro i j hi hj hne
  exact other_block_ne_zero φ r hp hq (by omega) (by omega) hne hroot

end Rhone.Probability.ResidueSupport
