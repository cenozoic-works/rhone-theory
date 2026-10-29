module

public import Rhone.MarkovChain.FluctuatingSizeHeterozygosity

@[expose] public section

namespace Rhone.Palomar.FluctuatingSize

open Finset MarkovChain MarkovChain.EffectiveSize

theorem wfResize_nonneg (M N : ℕ) (i : Fin (M + 1)) (j : Fin (N + 1)) :
    0 ≤ wfResize M N i j :=
  Rhone.MarkovChain.wfResize_nonneg M N i j

theorem wfResize_row_sum (M N : ℕ) (i : Fin (M + 1)) : ∑ j, wfResize M N i j = 1 :=
  Rhone.MarkovChain.wfResize_row_sum M N i

theorem wfResize_self (N : ℕ) : wfResize N N = wf N :=
  Rhone.MarkovChain.wfResize_self N

theorem wfVarExpect_const (N t : ℕ) (f : Fin (N + 1) → ℝ) :
    wfVarExpect (fun _ => N) t f = (wf N).expectIter t f :=
  Rhone.MarkovChain.wfVarExpect_const N t f

theorem wfResize_expect_het (M : ℕ) {N : ℕ} (hN : 0 < N) (i : Fin (M + 1)) :
    ∑ j, wfResize M N i j * het N j = (1 - 1 / (N : ℝ)) * het M i :=
  Rhone.MarkovChain.wfResize_expect_het M hN i

theorem wfVarExpect_het (n : ℕ → ℕ) (t : ℕ) (hpos : ∀ s, s < t → 0 < n (s + 1))
    (i : Fin (n 0 + 1)) :
    wfVarExpect n t (fun j => het (n t) j) i =
      (∏ s ∈ range t, (1 - 1 / (n (s + 1) : ℝ))) * het (n 0) i :=
  Rhone.MarkovChain.wfVarExpect_het n t hpos i

theorem sum_inv_eq_div_harmonicSize {T : ℕ} (a : Fin T → ℝ) :
    ∑ t, 1 / a t = T / harmonicSize a :=
  Rhone.MarkovChain.sum_inv_eq_div_harmonicSize a

theorem prod_deficit_le_harmonic {T : ℕ} (a : Fin T → ℝ) (ha : ∀ t, 1 ≤ a t) :
    ∏ t, (1 - 1 / a t) ≤ (1 - 1 / harmonicSize a) ^ T :=
  Rhone.MarkovChain.prod_deficit_le_harmonic a ha

theorem prod_deficit_eq_harmonic_iff {T : ℕ} (a : Fin T → ℝ) (ha : ∀ t, 1 ≤ a t) :
    ∏ t, (1 - 1 / a t) = (1 - 1 / harmonicSize a) ^ T ↔ ∀ s t, a s = a t :=
  Rhone.MarkovChain.prod_deficit_eq_harmonic_iff a ha

theorem harmonic_sub_prod_deficit_le {T : ℕ} (a : Fin T → ℝ) (ha : ∀ t, 1 ≤ a t) :
    (1 - 1 / harmonicSize a) ^ T - ∏ t, (1 - 1 / a t) ≤
      ((T : ℝ) - 1) / (2 * T) * (∑ t, 1 / a t) ^ 2 :=
  Rhone.MarkovChain.harmonic_sub_prod_deficit_le a ha

theorem abs_prod_deficit_sub_harmonic_le {T : ℕ} (a : Fin T → ℝ) (ha : ∀ t, 1 ≤ a t) :
    |∏ t, (1 - 1 / a t) - (1 - 1 / harmonicSize a) ^ T| ≤ (∑ t, 1 / a t) ^ 2 / 2 :=
  Rhone.MarkovChain.abs_prod_deficit_sub_harmonic_le a ha

theorem wfVarExpect_het_le_harmonic (n : ℕ → ℕ) (t : ℕ) (hpos : ∀ s, s < t → 0 < n (s + 1))
    (i : Fin (n 0 + 1)) :
    wfVarExpect n t (fun j => het (n t) j) i ≤
      (1 - 1 / harmonicSize (fun s : Fin t => (n (s + 1) : ℝ))) ^ t * het (n 0) i :=
  Rhone.MarkovChain.wfVarExpect_het_le_harmonic n t hpos i

theorem prod_deficit_two_four :
    ∏ t : Fin 2, (1 - 1 / ((![2, 4] : Fin 2 → ℝ) t)) = 3 / 8 :=
  Rhone.MarkovChain.prod_deficit_two_four

theorem harmonicSize_two_four : harmonicSize (![2, 4] : Fin 2 → ℝ) = 8 / 3 :=
  Rhone.MarkovChain.harmonicSize_two_four

theorem harmonic_power_two_four :
    (1 - 1 / harmonicSize (![2, 4] : Fin 2 → ℝ)) ^ 2 = 25 / 64 :=
  Rhone.MarkovChain.harmonic_power_two_four

theorem prod_deficit_two_four_ne_harmonic :
    ∏ t : Fin 2, (1 - 1 / ((![2, 4] : Fin 2 → ℝ) t)) ≠
      (1 - 1 / harmonicSize (![2, 4] : Fin 2 → ℝ)) ^ 2 :=
  Rhone.MarkovChain.prod_deficit_two_four_ne_harmonic

end Rhone.Palomar.FluctuatingSize
