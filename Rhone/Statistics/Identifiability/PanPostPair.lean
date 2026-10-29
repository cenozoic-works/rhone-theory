/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.LawSeparation

/-! # Surviving pair under arbitrary time-varying panmictic rates -/

@[expose] public section

open scoped Matrix
open Set Finset
namespace Rhone.Statistics.Identifiability

set_option backward.isDefEq.respectTransparency false

def panPostShape : Fin 2 → MarkovChain.Identifiability.Shape := ![[[2,3]], [[1,2,2]]]

def panPostRateCount
    (events : MarkovChain.Identifiability.Shape → List MarkovChain.Identifiability.Shape)
    (kill : MarkovChain.Identifiability.Shape → Nat)
    (i j : Fin 2) : Int :=
  ((events (panPostShape i)).countP (fun s => s == panPostShape j) : Int) -
    if i = j then ((events (panPostShape i)).length + kill (panPostShape i) : Nat) else 0

theorem panPost_events_checked :
    (∀ i j, panPostRateCount MarkovChain.Identifiability.coalescenceEvents
        MarkovChain.Identifiability.killedCount i j =
      (![![-1,0], ![2,-3]] : Matrix (Fin 2) (Fin 2) Int) i j) ∧
    (∀ i j, panPostRateCount MarkovChain.Identifiability.recombinationEvents (fun _ => 0) i j =
      (![![-1,1], ![0,0]] : Matrix (Fin 2) (Fin 2) Int) i j) ∧
    (∀ i, MarkovChain.Identifiability.killedCount (panPostShape i) = 1) := by
  decide

noncomputable def panPostGenerator (rate recomb : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![-rate-recomb,recomb], ![2*rate,-3*rate]]

theorem panPost_row_sum (rate recomb : ℝ) (i : Fin 2) :
    (∑ j, panPostGenerator rate recomb i j) = -rate := by
  fin_cases i <;> simp [panPostGenerator, Fin.sum_univ_succ]
  ring

theorem panPost_total_derivative (rate recomb : ℝ → ℝ) (p : ℝ → Fin 2 → ℝ) (t : ℝ)
    (hp : ∀ i, HasDerivAt (fun x => p x i)
      (∑ j, p t j * panPostGenerator (rate t) (recomb t) j i) t) :
    HasDerivAt (fun x => ∑ i, p x i) (-(rate t) * ∑ i, p t i) t := by
  have h := HasDerivAt.sum (u := Finset.univ) (fun i _ => hp i)
  convert! h using 1
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, panPost_row_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem constant_on_ray_of_derivative_zero (g : ℝ → ℝ) (s : ℝ)
    (hg : ∀ x, s ≤ x → HasDerivAt g 0 x) {t : ℝ} (ht : s ≤ t) : g t = g s := by
  have hcont : ContinuousOn g (Ici s) := fun x hx => (hg x hx).continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ interior (Ici s), HasDerivWithinAt g 0 (interior (Ici s)) x :=
    fun x hx => (hg x (interior_subset hx)).hasDerivWithinAt
  have hm := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici s) hcont hderiv
    (fun _ _ => le_refl 0)
  have ha := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici s) hcont hderiv
    (fun _ _ => le_refl 0)
  exact le_antisymm (ha self_mem_Ici ht ht) (hm self_mem_Ici ht ht)

set_option backward.isDefEq.respectTransparency false in
theorem survival_clock_of_forward_equation (S rate H : ℝ → ℝ) (s : ℝ)
    (hS : ∀ x, s ≤ x → HasDerivAt S (-rate x * S x) x)
    (hH : ∀ x, s ≤ x → HasDerivAt H (rate x) x) {t : ℝ} (ht : s ≤ t) :
    S t = S s * Real.exp (H s - H t) := by
  have hg : ∀ x, s ≤ x → HasDerivAt (fun y => S y * Real.exp (H y)) 0 x := by
    intro x hx
    convert! (hS x hx).mul (hH x hx).exp using 1
    ring
  have h := constant_on_ray_of_derivative_zero _ s hg ht
  apply mul_right_cancel₀ (Real.exp_pos (H t)).ne'
  rw [mul_assoc, ← Real.exp_add, sub_add_cancel]
  exact h

theorem panPost_survival_clock (rate recomb H : ℝ → ℝ) (p : ℝ → Fin 2 → ℝ) (s : ℝ)
    (hp : ∀ x, s ≤ x → ∀ i, HasDerivAt (fun y => p y i)
      (∑ j, p x j * panPostGenerator (rate x) (recomb x) j i) x)
    (hH : ∀ x, s ≤ x → HasDerivAt H (rate x) x) {t : ℝ} (ht : s ≤ t) :
    (∑ i, p t i) = (∑ i, p s i) * Real.exp (H s - H t) :=
  survival_clock_of_forward_equation _ rate H s
    (fun x hx => panPost_total_derivative rate recomb p x (hp x hx)) hH ht

end Rhone.Statistics.Identifiability
