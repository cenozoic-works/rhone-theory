/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.Q22

/-! # No Ewens-shaped formula of degree `1` for `q22` -/

@[expose] public section

namespace Rhone.Algebra

open Polynomial

theorem not_boundedDen_q22 : ¬ BoundedDen 1 q22 :=
  not_boundedDen Dq_ne_zero rfl E22_prime E22_dvd_Dq E22_not_dvd_Nq
    (by rw [E22_natDegree]; norm_num)

theorem no_degree_one_formula :
    ¬ ∃ e : Expr Fuv, DAdm thA thB rhoL 1 e ∧ Expr.eval thA thB rhoL e = q22 := by
  rintro ⟨e, he, hval⟩
  exact not_boundedDen_q22
    (hval ▸ boundedDen_eval (boundedDen_thA 1) (boundedDen_thB 1) (boundedDen_rhoL 1) he)

theorem two_le_degree_of_formula {D : ℕ} {e : Expr Fuv} (he : DAdm thA thB rhoL D e)
    (hval : Expr.eval thA thB rhoL e = q22) : 2 ≤ D := by
  have h := natDegree_le_of_dvd_denom_eval (boundedDen_thA D) (boundedDen_thB D) (boundedDen_rhoL D)
      he
    E22_irreducible (by rw [hval]; exact E22_dvd_q22_denom)
  rwa [E22_natDegree] at h

end Rhone.Algebra
