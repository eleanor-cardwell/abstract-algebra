-- Algebra.Monoid.Basic

import Algebra.Set.Function

variable {X: Type u₁} {Y: Type u₂}

/-

A monoid is a set with
- an associative binary operation, and
- an identity element "0"

-/

class Monoid (X: Type u) where
  op: X → X → X
  unit: X
  identity: Identity op unit
  assoc: Associative op
  
class CommMonoid (X: Type u) extends Monoid X where
  comm: Commutative op

namespace Monoid
scoped instance [Monoid X]: Add X := ⟨op⟩
scoped instance [Monoid X]: Zero X := ⟨unit⟩

end Monoid
open Monoid



-- Unpack axioms.

theorem op_unit_left [Monoid X] (a: X): 0 + a = a := by
  exact Monoid.identity.left a

theorem op_unit_right [Monoid X] (a: X): a + 0 = a := by
  exact Monoid.identity.right a

theorem op_assoc [Monoid X] (a b c: X): a + b + c = a + (b + c) := by
  exact Monoid.assoc a b c

def inverses [Monoid X] (a b: X): Prop :=
  Inverses op a b unit

def inverses_iff [Monoid X] (a b: X): inverses a b ↔ a + b = 0 ∧ b + a = 0 := by
  rfl

theorem inverses_unique [Monoid X] {a b b': X}
  (h: inverses a b) (h': inverses a b'): b = b' := by
  simp_all [inverses_iff]
  calc
    b = b + 0        := by rw [op_unit_right]
    _ = b + (a + b') := by rw [h'.left]
    _ = (b + a) + b' := by rw [op_assoc]
    _ = 0 + b'       := by rw [h.right]
    _ = b'           := by rw [op_unit_left]


theorem left_right_inverse_eq [Monoid X] {a b c: X}
  (h₁: a + b = 0) (h₂: b + c = 0): a = c := by
  calc
    a = a + 0        := by rw [op_unit_right]
    _ = a + (b + c) := by rw [h₂]
    _ = (a + b) + c := by rw [op_assoc]
    _ = 0 + c       := by rw [h₁]
    _ = c           := by rw [op_unit_left]
