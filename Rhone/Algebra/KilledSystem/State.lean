/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.Tower

/-! # The two-locus sample configurations, `K_A = K_B = 2` -/

@[expose] public section

namespace Rhone.Algebra.KilledSystem

structure St where
  a0 : ℕ
  a1 : ℕ
  b0 : ℕ
  b1 : ℕ
  c00 : ℕ
  c01 : ℕ
  c10 : ℕ
  c11 : ℕ
deriving DecidableEq, Repr

namespace St

def t (s : St) : ℕ := s.c00 + s.c01 + s.c10 + s.c11

def nA (s : St) : ℕ := s.a0 + s.a1 + s.t

def nB (s : St) : ℕ := s.b0 + s.b1 + s.t

def n (s : St) : ℕ := s.a0 + s.a1 + s.b0 + s.b1 + s.t

def cr0 (s : St) : ℕ := s.c00 + s.c01

def cr1 (s : St) : ℕ := s.c10 + s.c11

def cc0 (s : St) : ℕ := s.c00 + s.c10

def cc1 (s : St) : ℕ := s.c01 + s.c11

def InClosure (s : St) : Prop := s.nA ≤ 2 ∧ s.nB ≤ 2 ∧ 1 ≤ s.nA + s.nB

instance (s : St) : Decidable s.InClosure := by
  unfold InClosure; infer_instance

end St

end Rhone.Algebra.KilledSystem
