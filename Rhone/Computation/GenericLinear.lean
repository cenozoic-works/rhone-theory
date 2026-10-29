/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.GenericRows
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Computable general-allele finite-system reference values -/

@[expose] public section
open Rhone.Computation Rhone.LinearAlgebra.Recursion Matrix
namespace Rhone.Computation.GenericLinear
abbrev Index (KA KB N : Nat) := Fin (GenericRows.keys KA KB N).length
def key {KA KB N : Nat} (i : Index KA KB N) : Config KA KB := (GenericRows.keys KA KB N).get i
def extend {KA KB N : Nat} (v : Index KA KB N → Rat) (ξ : Config KA KB) : Rat :=
  ∑ i, if ξ = key i then v i else 0

lemma keys_nodup (KA KB N : Nat) : (GenericRows.keys KA KB N).Nodup := List.nodup_dedup _
lemma key_injective {KA KB N : Nat} : Function.Injective (@key KA KB N) :=
  List.nodup_iff_injective_get.mp (keys_nodup KA KB N)
lemma key_closure {KA KB N : Nat} (i : Index KA KB N) : CheckerSpec.InClosure N (key i) :=
  (GenericRows.mem_keys_iff _).mp (List.get_mem _ _)
lemma key_surjective {KA KB N : Nat} (ξ : Config KA KB) (h : CheckerSpec.InClosure N ξ) :
    ∃ i : Index KA KB N, key i = ξ := by
  exact List.mem_iff_get.mp ((GenericRows.mem_keys_iff ξ).mpr h)
lemma extend_key {KA KB N : Nat} (v : Index KA KB N → Rat) (i : Index KA KB N) :
    extend v (key i) = v i := by
  simp only [extend, key_injective.eq_iff]
  simp
lemma extend_add {KA KB N : Nat} (v w : Index KA KB N → Rat) :
    extend (v + w) = fun ξ => extend v ξ + extend w ξ := by
  funext ξ
  simp only [extend, Pi.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp
lemma extend_smul {KA KB N : Nat} (c : Rat) (v : Index KA KB N → Rat) :
    extend (c • v) = fun ξ => c * extend v ξ := by
  funext ξ
  simp only [extend, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

def operator {KA KB N : Nat} (θA θB ρ : Rat) (πA : Fin KA → Rat) (πB : Fin KB → Rat) :
    (Index KA KB N → Rat) →ₗ[Rat] (Index KA KB N → Rat) where
  toFun v := fun i => if (key i).n ≤ 1 then v i else
    diag θA θB ρ (key i) * v i - rhs θA θB ρ πA πB (extend v) (key i)
  map_add' v w := by
    funext i
    simp only [Pi.add_apply, extend_add, rhs_add]
    split_ifs <;> ring
  map_smul' c v := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, extend_smul, rhs_smul]
    split_ifs <;> ring

def matrix {KA KB N : Nat} (θA θB ρ : Rat) (πA : Fin KA → Rat) (πB : Fin KB → Rat) :
    Matrix (Index KA KB N) (Index KA KB N) Rat :=
  LinearMap.toMatrix' (operator θA θB ρ πA πB)

def explicitInverse {d : Nat} (A : Matrix (Fin d) (Fin d) Rat) : Matrix (Fin d) (Fin d) Rat :=
  A.det⁻¹ • A.adjugate

lemma operator_zero {KA KB N : Nat} {θA θB ρ : Rat} {πA : Fin KA → Rat} {πB : Fin KB → Rat}
    (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) {v : Index KA KB N → Rat}
    (hz : operator θA θB ρ πA πB v = 0) :
    ∀ ξ : Config KA KB, CheckerSpec.InClosure N ξ → extend v ξ = 0 := by
  apply CheckerSpec.closure_unique hθA hθB hρ (g := fun _ => 0)
  · intro ξ hc hn
    obtain ⟨i, rfl⟩ := key_surjective ξ hc
    have hi := congrFun hz i
    simpa [operator, hn, extend_key] using hi
  · intro ξ hc hn
    obtain ⟨i, rfl⟩ := key_surjective ξ hc
    have hi := congrFun hz i
    have hnot : ¬ (key i).n ≤ 1 := by omega
    have hi' : diag θA θB ρ (key i) * v i -
        rhs θA θB ρ πA πB (extend v) (key i) = 0 := by
      simpa only [operator, LinearMap.coe_mk, AddHom.coe_mk,
        ite_eq_right hnot, Pi.zero_apply] using hi
    rw [extend_key]
    exact sub_eq_zero.mp hi'
  · intro ξ _ _
    simp [rhs_zero]

lemma operator_injective {KA KB N : Nat} {θA θB ρ : Rat} {πA : Fin KA → Rat} {πB : Fin KB → Rat}
    (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) :
    Function.Injective (operator (N := N) θA θB ρ πA πB) := by
  intro v w heq
  have hz : operator θA θB ρ πA πB (v - w) = 0 := by rw [map_sub, heq, sub_self]
  have hzero := operator_zero hθA hθB hρ hz
  funext i
  have hi := hzero (key i) (key_closure i)
  rw [extend_key] at hi
  exact sub_eq_zero.mp hi

lemma matrix_det_unit {KA KB N : Nat} {θA θB ρ : Rat} {πA : Fin KA → Rat} {πB : Fin KB → Rat}
    (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) :
    IsUnit (matrix (N := N) θA θB ρ πA πB).det := by
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro v w heq
  simp only [matrix, LinearMap.toMatrix'_mulVec] at heq
  exact operator_injective hθA hθB hρ heq

lemma explicitInverse_eq {d : Nat} (A : Matrix (Fin d) (Fin d) Rat) : explicitInverse A = A⁻¹ := by
  simp only [explicitInverse, Matrix.inv_def, Ring.inverse_eq_inv]

def boundaryVector {KA KB N : Nat} (πA : Fin KA → Rat) (πB : Fin KB → Rat) :
    Index KA KB N → Rat := fun i =>
  if (key i).n ≤ 1 then GenericClosure.boundary πA πB (key i) else 0

def solve {KA KB N : Nat} (θA θB ρ : Rat) (πA : Fin KA → Rat) (πB : Fin KB → Rat) :
    Index KA KB N → Rat :=
  explicitInverse (matrix θA θB ρ πA πB) *ᵥ boundaryVector πA πB

def value {KA KB : Nat} (θA θB ρ : Rat) (πA : Fin KA → Rat) (πB : Fin KB → Rat)
    (N : Nat) : Config KA KB → Rat := extend (solve (N := N) θA θB ρ πA πB)

lemma operator_solve {KA KB N : Nat} {θA θB ρ : Rat} {πA : Fin KA → Rat} {πB : Fin KB → Rat}
    (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) :
    operator θA θB ρ πA πB (solve (N := N) θA θB ρ πA πB) = boundaryVector πA πB := by
  rw [← LinearMap.toMatrix'_mulVec]
  change matrix θA θB ρ πA πB *ᵥ solve θA θB ρ πA πB = _
  rw [solve, explicitInverse_eq, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (matrix_det_unit hθA hθB hρ), Matrix.one_mulVec]

lemma value_boundary {KA KB N : Nat} {θA θB ρ : Rat} {πA : Fin KA → Rat} {πB : Fin KB → Rat}
    (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (ξ : Config KA KB) (hc : CheckerSpec.InClosure N ξ) (hn : ξ.n ≤ 1) :
    value θA θB ρ πA πB N ξ = GenericClosure.boundary πA πB ξ := by
  obtain ⟨i, rfl⟩ := key_surjective ξ hc
  have hi := congrFun (operator_solve (N := N) (πA := πA) (πB := πB) hθA hθB hρ) i
  simpa only [operator, LinearMap.coe_mk, AddHom.coe_mk, boundaryVector,
    ite_eq_left hn, value, extend_key] using hi

lemma value_recursion {KA KB N : Nat} {θA θB ρ : Rat} {πA : Fin KA → Rat} {πB : Fin KB → Rat}
    (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (ξ : Config KA KB) (hc : CheckerSpec.InClosure N ξ) (hn : 2 ≤ ξ.n) :
    diag θA θB ρ ξ * value θA θB ρ πA πB N ξ =
      rhs θA θB ρ πA πB (value θA θB ρ πA πB N) ξ := by
  obtain ⟨i, rfl⟩ := key_surjective ξ hc
  have hi := congrFun (operator_solve (N := N) (πA := πA) (πB := πB) hθA hθB hρ) i
  have hnot : ¬ (key i).n ≤ 1 := by omega
  simp only [operator, LinearMap.coe_mk, AddHom.coe_mk, boundaryVector, ite_eq_right hnot] at hi
  simpa only [value, extend_key] using sub_eq_zero.mp hi

lemma value_eq_q {KA KB N : Nat} {θA θB ρ : Rat} {πA : Fin KA → Rat} {πB : Fin KB → Rat}
    (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) :
    ∀ ξ : Config KA KB, CheckerSpec.InClosure N ξ →
      value θA θB ρ πA πB N ξ = q (πA := πA) (πB := πB) hθA hθB hρ ξ := by
  apply CheckerSpec.closure_eq_q hθA hθB hρ
  · intro ξ hc hn
    rw [value_boundary hθA hθB hρ ξ hc hn]
    exact GenericClosure.boundary_solution θA θB ρ πA πB _ (q_isSolution hθA hθB hρ) ξ hn
  · intro ξ hc hn
    exact value_recursion hθA hθB hρ ξ hc hn

def qValue {KA KB : Nat} (θA θB ρ : Rat) (πA : Fin KA → Rat) (πB : Fin KB → Rat)
    (ξ : Config KA KB) : Rat := value θA θB ρ πA πB (max ξ.nA ξ.nB) ξ

lemma qValue_eq_q {KA KB : Nat} {θA θB ρ : Rat} {πA : Fin KA → Rat} {πB : Fin KB → Rat}
    (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (ξ : Config KA KB) :
    qValue θA θB ρ πA πB ξ = q (πA := πA) (πB := πB) hθA hθB hρ ξ :=
  value_eq_q hθA hθB hρ ξ ⟨Nat.le_max_left _ _, Nat.le_max_right _ _⟩

def table {KA KB : Nat} (θA θB ρ : Rat) (πA : Fin KA → Rat) (πB : Fin KB → Rat)
    (N : Nat) : List (Config KA KB × Rat) :=
  let v := solve (N := N) θA θB ρ πA πB
  (GenericRows.keys KA KB N).map (fun ξ => (ξ, extend v ξ))

lemma table_eq_spec {KA KB N : Nat} {θA θB ρ : Rat} {πA : Fin KA → Rat} {πB : Fin KB → Rat}
    (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) :
    table θA θB ρ πA πB N = (GenericRows.keys KA KB N).map
      (fun ξ => (ξ, q (πA := πA) (πB := πB) hθA hθB hρ ξ)) := by
  change (GenericRows.keys KA KB N).map (fun ξ => (ξ, value θA θB ρ πA πB N ξ)) = _
  apply List.map_congr_left
  intro ξ hξ
  congr 1
  exact value_eq_q hθA hθB hρ ξ ((GenericRows.mem_keys_iff ξ).mp hξ)

lemma table_checked {KA KB N : Nat} {θA θB ρ : Rat} {πA : Fin KA → Rat} {πB : Fin KB → Rat}
    (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) :
    GenericRows.check θA θB ρ πA πB N (table θA θB ρ πA πB N) = true := by
  rw [table_eq_spec hθA hθB hρ]
  exact GenericRows.check_complete θA θB ρ πA πB hθA hθB hρ _ (q_isSolution hθA hθB hρ)

end Rhone.Computation.GenericLinear
