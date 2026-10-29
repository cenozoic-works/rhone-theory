/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.Expr

/-! # Closure of bounded denominators under the expression operations -/

@[expose] public section

namespace Rhone.Algebra

open Polynomial

variable {F : Type*} [Field F]

def BoundedDen (D : ℕ) (f : RatFunc F) : Prop :=
  ∃ N M : Polynomial F, M ≠ 0 ∧
    f * algebraMap (Polynomial F) (RatFunc F) M = algebraMap (Polynomial F) (RatFunc F) N ∧
    ∀ p : Polynomial F, Irreducible p → p ∣ M → p.natDegree ≤ D

theorem algebraMap_ne_zero {p : Polynomial F} (hp : p ≠ 0) :
    algebraMap (Polynomial F) (RatFunc F) p ≠ 0 :=
  RatFunc.algebraMap_ne_zero hp

theorem boundedDen_of_poly (D : ℕ) (p : Polynomial F) :
    BoundedDen D (algebraMap (Polynomial F) (RatFunc F) p) :=
  ⟨p, 1, one_ne_zero, by simp, fun _ hq hdvd => absurd (isUnit_of_dvd_one hdvd) hq.not_isUnit⟩

theorem ratCast_eq_algebraMap (q : ℚ) :
    ((q : RatFunc F)) = algebraMap (Polynomial F) (RatFunc F) (C (q : F)) := by
  rw [RatFunc.algebraMap_C]
  exact (map_ratCast (RatFunc.C : F →+* RatFunc F) q).symm

theorem boundedDen_ratCast (D : ℕ) (q : ℚ) : BoundedDen D ((q : RatFunc F)) := by
  rw [ratCast_eq_algebraMap]; exact boundedDen_of_poly D _

theorem boundedDen_coeff (D : ℕ) (x : F) :
    BoundedDen D (algebraMap F (RatFunc F) x) := by
  have : algebraMap F (RatFunc F) x = algebraMap (Polynomial F) (RatFunc F) (C x) := by
    rw [RatFunc.algebraMap_C]; rfl
  rw [this]; exact boundedDen_of_poly D _

theorem BoundedDen.add {D : ℕ} {f g : RatFunc F}
    (hf : BoundedDen D f) (hg : BoundedDen D g) : BoundedDen D (f + g) := by
  obtain ⟨N₁, M₁, hM₁, h₁, hd₁⟩ := hf
  obtain ⟨N₂, M₂, hM₂, h₂, hd₂⟩ := hg
  refine ⟨N₁ * M₂ + N₂ * M₁, M₁ * M₂, mul_ne_zero hM₁ hM₂, ?_, ?_⟩
  · rw [map_mul, map_add, map_mul, map_mul]
    calc (f + g) * (algebraMap (Polynomial F) (RatFunc F) M₁
              * algebraMap (Polynomial F) (RatFunc F) M₂)
        = (f * algebraMap (Polynomial F) (RatFunc F) M₁)
              * algebraMap (Polynomial F) (RatFunc F) M₂
          + (g * algebraMap (Polynomial F) (RatFunc F) M₂)
              * algebraMap (Polynomial F) (RatFunc F) M₁ := by ring
      _ = _ := by rw [h₁, h₂]
  · intro p hp hdvd
    rcases hp.prime.dvd_mul.mp hdvd with h | h
    · exact hd₁ p hp h
    · exact hd₂ p hp h

theorem BoundedDen.mul {D : ℕ} {f g : RatFunc F}
    (hf : BoundedDen D f) (hg : BoundedDen D g) : BoundedDen D (f * g) := by
  obtain ⟨N₁, M₁, hM₁, h₁, hd₁⟩ := hf
  obtain ⟨N₂, M₂, hM₂, h₂, hd₂⟩ := hg
  refine ⟨N₁ * N₂, M₁ * M₂, mul_ne_zero hM₁ hM₂, ?_, ?_⟩
  · rw [map_mul, map_mul]
    calc f * g * (algebraMap (Polynomial F) (RatFunc F) M₁
              * algebraMap (Polynomial F) (RatFunc F) M₂)
        = (f * algebraMap (Polynomial F) (RatFunc F) M₁)
              * (g * algebraMap (Polynomial F) (RatFunc F) M₂) := by ring
      _ = _ := by rw [h₁, h₂]
  · intro p hp hdvd
    rcases hp.prime.dvd_mul.mp hdvd with h | h
    · exact hd₁ p hp h
    · exact hd₂ p hp h

theorem BoundedDen.div_poly {D : ℕ} {f : RatFunc F} (hf : BoundedDen D f)
    {g : Polynomial F} (hg : g ≠ 0) (hdeg : g.natDegree ≤ D) :
    BoundedDen D (f / algebraMap (Polynomial F) (RatFunc F) g) := by
  obtain ⟨N, M, hM, h, hd⟩ := hf
  have hg' : algebraMap (Polynomial F) (RatFunc F) g ≠ 0 := algebraMap_ne_zero hg
  refine ⟨N, M * g, mul_ne_zero hM hg, ?_, ?_⟩
  · rw [map_mul]
    calc f / algebraMap (Polynomial F) (RatFunc F) g
            * (algebraMap (Polynomial F) (RatFunc F) M
              * algebraMap (Polynomial F) (RatFunc F) g)
        = f * algebraMap (Polynomial F) (RatFunc F) M := by field_simp
      _ = _ := h
  · intro p hp hdvd
    rcases hp.prime.dvd_mul.mp hdvd with hpm | hpg
    · exact hd p hp hpm
    · exact le_trans (Polynomial.natDegree_le_of_dvd hpg hg) hdeg

theorem boundedDen_eval {D : ℕ} {tA tB tR : RatFunc F}
    (hA : BoundedDen D tA) (hB : BoundedDen D tB) (hR : BoundedDen D tR)
    {e : Expr F} (h : DAdm tA tB tR D e) : BoundedDen D (Expr.eval tA tB tR e) := by
  induction h with
  | const q => exact boundedDen_ratCast D q
  | coeff x => exact boundedDen_coeff D x
  | thA => exact hA
  | thB => exact hB
  | rho => exact hR
  | add _ _ ihx ihy => exact ihx.add ihy
  | mul _ _ ihx ihy => exact ihx.mul ihy
  | div _ _ p hp hdeg hval ihx _ =>
      rw [Expr.eval_div, hval]
      exact ihx.div_poly hp hdeg

theorem natDegree_le_of_dvd_denom_eval {D : ℕ} {tA tB tR : RatFunc F}
    (hA : BoundedDen D tA) (hB : BoundedDen D tB) (hR : BoundedDen D tR)
    {e : Expr F} (h : DAdm tA tB tR D e)
    {p : Polynomial F} (hp : Irreducible p) (hdvd : p ∣ (Expr.eval tA tB tR e).denom) :
    p.natDegree ≤ D := by
  obtain ⟨N, M, hM, hNM, hd⟩ := boundedDen_eval hA hB hR h
  set f := Expr.eval tA tB tR e with hf
  have hden : algebraMap (Polynomial F) (RatFunc F) f.denom ≠ 0 :=
    algebraMap_ne_zero f.denom_ne_zero
  have hnum : algebraMap (Polynomial F) (RatFunc F) f.num
      = f * algebraMap (Polynomial F) (RatFunc F) f.denom :=
    (div_eq_iff hden).mp (RatFunc.num_div_denom f)
  have key : f.num * M = N * f.denom := by
    apply IsFractionRing.injective (Polynomial F) (RatFunc F)
    rw [map_mul, map_mul, hnum, ← hNM]
    ring
  have hpnum : ¬ p ∣ f.num := fun hpn =>
    hp.not_isUnit ((f.isCoprime_num_denom).isUnit_of_dvd' hpn hdvd)
  have : p ∣ f.num * M := key ▸ Dvd.dvd.mul_left hdvd N
  exact hd p hp ((hp.prime.dvd_mul.mp this).resolve_left hpnum)

theorem prime_dvd_denom {f : RatFunc F} {Nq Dq p : Polynomial F} (hDq : Dq ≠ 0)
    (hf : f = algebraMap (Polynomial F) (RatFunc F) Nq
            / algebraMap (Polynomial F) (RatFunc F) Dq)
    (hp : Prime p) (hpD : p ∣ Dq) (hpN : ¬ p ∣ Nq) : p ∣ f.denom := by
  have hDq' : algebraMap (Polynomial F) (RatFunc F) Dq ≠ 0 := algebraMap_ne_zero hDq
  have hden : algebraMap (Polynomial F) (RatFunc F) f.denom ≠ 0 :=
    algebraMap_ne_zero f.denom_ne_zero
  have hnum : algebraMap (Polynomial F) (RatFunc F) f.num
      = f * algebraMap (Polynomial F) (RatFunc F) f.denom :=
    (div_eq_iff hden).mp (RatFunc.num_div_denom f)
  have key : f.num * Dq = Nq * f.denom := by
    apply IsFractionRing.injective (Polynomial F) (RatFunc F)
    rw [map_mul, map_mul, hnum, hf]
    field_simp
  have : p ∣ Nq * f.denom := key ▸ Dvd.dvd.mul_left hpD f.num
  exact (hp.dvd_mul.mp this).resolve_left hpN

theorem not_boundedDen {D : ℕ} {f : RatFunc F} {Nq Dq p : Polynomial F}
    (hDq : Dq ≠ 0)
    (hf : f = algebraMap (Polynomial F) (RatFunc F) Nq
            / algebraMap (Polynomial F) (RatFunc F) Dq)
    (hp : Prime p) (hpD : p ∣ Dq) (hpN : ¬ p ∣ Nq) (hdeg : D < p.natDegree) :
    ¬ BoundedDen D f := by
  rintro ⟨N, M, hM, hNM, hd⟩
  have hDq' : algebraMap (Polynomial F) (RatFunc F) Dq ≠ 0 := algebraMap_ne_zero hDq
  have key : Nq * M = N * Dq := by
    apply IsFractionRing.injective (Polynomial F) (RatFunc F)
    rw [map_mul, map_mul, ← hNM, hf]
    field_simp
  have : p ∣ Nq * M := key ▸ Dvd.dvd.mul_left hpD N
  exact absurd (hd p hp.irreducible ((hp.dvd_mul.mp this).resolve_left hpN)) (by omega)

end Rhone.Algebra
