/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.PanRiccatiUniqueness

/-! # The scalar reconstruction is equivalent to the full pre-merger ODE -/

@[expose] public section

namespace Rhone.Statistics.Identifiability

set_option backward.isDefEq.respectTransparency false

def PanPreEquations (rate recomb D R U : ℝ → ℝ) : Prop :=
  ∀ t, 0 ≤ t →
    HasDerivAt D (-(rate t+2*recomb t)*D t+rate t*R t) t ∧
    HasDerivAt R (2*recomb t*D t-(3*rate t+recomb t)*R t+4*rate t*U t) t ∧
    HasDerivAt U (recomb t*R t-6*rate t*U t) t

def PanScalarEquations (rate D Ddot N R : ℝ → ℝ) : Prop :=
  ∀ t, 0 ≤ t →
    HasDerivAt D (Ddot t) t ∧
    HasDerivAt N (-rate t*(D t+2*N t)-Ddot t) t ∧
    HasDerivAt R (panRiccatiDrift (rate t) (D t) (Ddot t) (N t) (R t)) t

theorem scalar_equations_give_pan_forward (rate D Ddot N R : ℝ → ℝ)
    (hD : ∀ t, 0 ≤ t → D t ≠ 0) (h : PanScalarEquations rate D Ddot N R) :
    PanPreEquations rate (fun t => reconstructedRecomb (rate t) (D t) (Ddot t) (R t))
      D R (fun t => N t - R t) := by
  intro t ht
  rcases h t ht with ⟨hd,hn,hr⟩
  have he := (pan_forward_scalar_reconstruction (rate t)
    (reconstructedRecomb (rate t) (D t) (Ddot t) (R t)) (D t) (R t) (N t) (Ddot t)
    (panRiccatiDrift (rate t) (D t) (Ddot t) (N t) (R t))
    (-rate t*(D t+2*N t)-Ddot t) (hD t ht)).mpr ⟨rfl,by ring,rfl⟩
  refine ⟨?_,?_,?_⟩
  · convert! hd using 1
    exact he.1.symm
  · convert! hr using 1
    exact he.2.1.symm
  · convert! hn.sub hr using 1
    exact he.2.2.symm

theorem pan_forward_gives_scalar_equations (rate recomb D Ddot N R : ℝ → ℝ)
    (hD : ∀ t, 0 ≤ t → D t ≠ 0)
    (hderiv : ∀ t, 0 ≤ t → HasDerivAt D (Ddot t) t)
    (h : PanPreEquations rate recomb D R (fun t => N t - R t)) :
    PanScalarEquations rate D Ddot N R ∧
      ∀ t, 0 ≤ t → recomb t = reconstructedRecomb (rate t) (D t) (Ddot t) (R t) := by
  have he : ∀ t, 0 ≤ t → recomb t = reconstructedRecomb (rate t) (D t) (Ddot t) (R t) ∧
      Ddot t + ((2*recomb t*D t-(3*rate t+recomb t)*R t+4*rate t*(N t - R t))+
        (recomb t*R t-6*rate t*(N t - R t))) = -rate t*(D t+2*N t) ∧
      2*recomb t*D t-(3*rate t+recomb t)*R t+4*rate t*(N t - R t) =
        panRiccatiDrift (rate t) (D t) (Ddot t) (N t) (R t) := by
    intro t ht
    apply (pan_forward_scalar_reconstruction _ _ _ _ _ _ _ _ (hD t ht)).mp
    exact ⟨(hderiv t ht).unique (h t ht).1,rfl,by ring⟩
  refine ⟨?_,fun t ht => (he t ht).1⟩
  intro t ht
  refine ⟨hderiv t ht,?_,?_⟩
  · have hn := (h t ht).2.1.add (h t ht).2.2
    convert! hn using 1
    · funext x
      simp only [Pi.add_apply]
      ring
    · linarith [(he t ht).2.1]
  · rw [← (he t ht).2.2]
    exact (h t ht).2.1

theorem pan_forward_reconstruction_iff (rate D Ddot N R : ℝ → ℝ)
    (hD : ∀ t, 0 ≤ t → D t ≠ 0)
    (hderiv : ∀ t, 0 ≤ t → HasDerivAt D (Ddot t) t) :
    PanScalarEquations rate D Ddot N R ↔
      ∃ recomb : ℝ → ℝ, PanPreEquations rate recomb D R (fun t => N t - R t) := by
  constructor
  · intro h
    exact ⟨_,scalar_equations_give_pan_forward rate D Ddot N R hD h⟩
  · rintro ⟨recomb,h⟩
    exact (pan_forward_gives_scalar_equations rate recomb D Ddot N R hD hderiv h).1

theorem nonnegative_pan_forward_reconstruction_iff (rate D Ddot N R : ℝ → ℝ)
    (hD : ∀ t, 0 ≤ t → 0 < D t)
    (hderiv : ∀ t, 0 ≤ t → HasDerivAt D (Ddot t) t) :
    (PanScalarEquations rate D Ddot N R ∧
      ∀ t, 0 ≤ t → Ddot t ≤ rate t*(R t-D t)) ↔
    ∃ recomb : ℝ → ℝ, (∀ t, 0 ≤ t → 0 ≤ recomb t) ∧
      PanPreEquations rate recomb D R (fun t => N t - R t) := by
  constructor
  · rintro ⟨he,hn⟩
    refine ⟨fun t => reconstructedRecomb (rate t) (D t) (Ddot t) (R t),?_,
      scalar_equations_give_pan_forward rate D Ddot N R
        (fun t ht => (hD t ht).ne') he⟩
    intro t ht
    exact (reconstructedRecomb_nonneg_iff (hD t ht)).mpr (hn t ht)
  · rintro ⟨recomb,hn,he⟩
    have h := pan_forward_gives_scalar_equations rate recomb D Ddot N R
      (fun t ht => (hD t ht).ne') hderiv he
    refine ⟨h.1,?_⟩
    intro t ht
    apply (reconstructedRecomb_nonneg_iff (hD t ht)).mp
    rw [← h.2 t ht]
    exact hn t ht

end Rhone.Statistics.Identifiability
