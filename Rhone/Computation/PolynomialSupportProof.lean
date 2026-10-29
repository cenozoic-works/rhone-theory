/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.PolynomialEncodingProof
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-! # Natural degree support of the configuration polynomial -/

@[expose] public section
namespace Rhone.Computation.PolynomialEncoding

open scoped Pointwise

def Supported (g : MvPolynomial (Fin 3) Rat) (na nb linked : Nat) : Prop :=
  ∀ d ∈ g.support, d 0 ≤ na ∧ d 1 ≤ nb ∧ d 2 ≤ linked ∧ d 2 ≤ d 0 ∧ d 2 ≤ d 1

theorem Supported.mono {g : MvPolynomial (Fin 3) Rat} {na nb linked ma mb ml : Nat}
    (h : Supported g na nb linked) (ha : na ≤ ma) (hb : nb ≤ mb) (hl : linked ≤ ml) :
    Supported g ma mb ml := by
  intro d hd
  obtain ⟨hna, hnb, hnl, hca, hcb⟩ := h d hd
  exact ⟨hna.trans ha, hnb.trans hb, hnl.trans hl, hca, hcb⟩

theorem supported_one : Supported (1 : MvPolynomial (Fin 3) Rat) 0 0 0 := by
  simp [Supported]

theorem supported_monomial (key : Key) (v : Rat) (na nb linked : Nat)
    (h : key.1 ≤ na ∧ key.2.1 ≤ nb ∧ key.2.2 ≤ linked ∧
      key.2.2 ≤ key.1 ∧ key.2.2 ≤ key.2.1) :
    Supported (MvPolynomial.monomial (exponent key) v) na nb linked := by
  intro d hd
  by_cases hv : v = 0
  · simp [hv] at hd
  · have he : d = exponent key := by simpa [MvPolynomial.support_monomial, hv] using hd
    subst d
    simpa [exponent] using h

theorem Supported.add {a b : MvPolynomial (Fin 3) Rat} {na nb linked : Nat}
    (ha : Supported a na nb linked) (hb : Supported b na nb linked) :
    Supported (a + b) na nb linked := by
  intro d hd
  rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with hd | hd
  · exact ha d hd
  · exact hb d hd

theorem Supported.mul {a b : MvPolynomial (Fin 3) Rat} {na nb nl ma mb ml : Nat}
    (ha : Supported a na nb nl) (hb : Supported b ma mb ml) :
    Supported (a * b) (na + ma) (nb + mb) (nl + ml) := by
  intro d hd
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul a b hd)
  obtain ⟨hxa, hxb, hxl, hx0, hx1⟩ := ha x hx
  obtain ⟨hya, hyb, hyl, hy0, hy1⟩ := hb y hy
  simp only [Finsupp.add_apply]
  omega

theorem Supported.pow {g : MvPolynomial (Fin 3) Rat} {na nb linked : Nat}
    (h : Supported g na nb linked) (n : Nat) :
    Supported (g ^ n) (n * na) (n * nb) (n * linked) := by
  induction n with
  | zero => simpa using supported_one
  | succ n ih => simpa only [pow_succ, Nat.succ_mul] using ih.mul h

end Rhone.Computation.PolynomialEncoding
