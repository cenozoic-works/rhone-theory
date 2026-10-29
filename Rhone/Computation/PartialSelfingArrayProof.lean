/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.PartialSelfingFiniteProof

/-! # Canonical array storage of diploid laws and the stored-row update -/

@[expose] public section
namespace Rhone.Computation.PartialSelfing
open Dynamics.MendelianIBD

theorem decode_equiv {d : Nat} (i : Fin (d * d)) :
    decode i = (finProdFinEquiv : Fin d × Fin d ≃ Fin (d * d)).symm i := by
  rfl

theorem lawArray_size (d : Nat) (p : Diploid d → Rat) :
    (lawArray d p).size = d * d := by
  simp [lawArray]

theorem dipLaw_lawArray (d : Nat) (p : Diploid d → Rat) (z : Diploid d) :
    dipLaw d (lawArray d p) z = p z := by
  let i : Fin (d * d) := finProdFinEquiv (z 0, z 1)
  have hi : dipIndex z = i.val := by
    simp [dipIndex, i, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
  have hs : i.val < (lawArray d p).size := by
    rw [lawArray_size]
    exact i.isLt
  unfold dipLaw
  rw [hi, ← Array.getElem_eq_getD (h := hs) 0]
  simp only [lawArray, Array.getElem_ofFn]
  change p (pair (decode i).1 (decode i).2) = p z
  have hd : decode i = (z 0, z 1) := by
    rw [decode_equiv]
    exact (finProdFinEquiv : Fin d × Fin d ≃ Fin (d * d)).symm_apply_apply (z 0, z 1)
  rw [hd, pair_eta]

theorem rowStep_embedding (d : Nat) (s : Rat) (environment previous : Array Rat)
    (z : Diploid d) :
    dipLaw d (rowStep d s environment previous) z =
      s * selfed (dipLaw d previous) z + (1 - s) * dipLaw d environment z := by
  rw [rowStep, dipLaw_lawArray]

theorem rowStep_cast (d : Nat) (s : Rat) (q environment previous : Array Rat)
    (he : ∀ z : Diploid d, dipLaw d environment z = outcross (parentLaw d q) z)
    (z : Diploid d) :
    (dipLaw d (rowStep d s environment previous) z : Real) =
      partialSelfingLaw (s : Real) (fun xy => (parentLaw d q xy : Real))
        (fun x => (dipLaw d previous x : Real)) z := by
  rw [rowStep_embedding, he z]
  exact step_cast s (parentLaw d q) (dipLaw d previous) z

end Rhone.Computation.PartialSelfing
