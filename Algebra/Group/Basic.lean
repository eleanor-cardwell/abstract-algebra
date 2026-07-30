-- Algebra.Group.Basic

import Algebra.Monoid.Basic

variable {X: Type u₁} {Y: Type u₂} {Z: Type u₃}

/-

A group is a monoid with inverses.

-/

class Group (X: Type u) extends Monoid X where
  inv: X → X
  inverse: Inverse op inv unit

class CommGroup (X: Type u) extends Group X, CommMonoid X

namespace Group
scoped instance [Monoid X]: Add X := ⟨Monoid.op⟩
scoped instance [Monoid X]: Zero X := ⟨Monoid.unit⟩
scoped instance [Group X]: Neg X := ⟨inv⟩

def opinv [Group X] (a b: X): X := a + -b
scoped instance [Group X]: Sub X := ⟨opinv⟩

end Group
open Group



-- Unpack axioms

theorem op_inv_left [Group X] (a: X): -a + a = 0 := by
  exact Group.inverse.left a

theorem op_inv_right [Group X] (a: X): a + -a = 0 := by
  exact Group.inverse.right a

theorem inverses_inv [Group X] (a: X): inverses a (-a) := by
  constructor
  exact op_inv_right a
  exact op_inv_left a

theorem op_cancel_left [Group X] {a b c: X} (h: a + b = a + c): b = c := by
  calc
    b
    _ = 0 + b        := by rw [op_unit_left]
    _ = -a + a + b   := by rw [op_inv_left]
    _ = -a + (a + b) := by rw [op_assoc]
    _ = -a + (a + c) := by rw [h]
    _ = -a + a + c   := by rw [op_assoc]
    _ = 0 + c        := by rw [op_inv_left]
    _ = c            := by rw [op_unit_left]

theorem op_cancel_right [Group X] {a b c: X} (h: a + c = b + c): a = b := by
  calc
    a
    _ = a + 0        := by rw [op_unit_right]
    _ = a + (c + -c) := by rw [op_inv_right]
    _ = a + c + -c   := by rw [op_assoc]
    _ = b + c + -c   := by rw [h]
    _ = b + (c + -c) := by rw [op_assoc]
    _ = b + 0        := by rw [op_inv_right]
    _ = b            := by rw [op_unit_right]

theorem op_unit_inverses [Group X] {a b: X} (h: a + b = 0): -a = b := by
  have: -a + a + b = -a := by rw [op_assoc, h, op_unit_right]
  rw [←this, op_inv_left, op_unit_left]

theorem inv_unit [Group X]: -(0: X) = 0 := by
  apply op_unit_inverses
  apply op_unit_left

theorem inv_inv [Group X] (a: X): -(-a) = a := by
  apply op_cancel_right (c := -a)
  rw [op_inv_left, op_inv_right]

theorem opinv_self [Group X] (a: X): a - a = 0 := by
  apply op_inv_right

theorem inv_invop [Group X] (a b: X): -(a - b) = b - a := by
  apply op_unit_inverses
  calc
    a - b + (b - a)
    _ = a + -b + (b + -a)   := by rfl
    _ = a + (-b + (b + -a)) := by rw [op_assoc]
    _ = a + (-b + b + -a)   := by rw [op_assoc]
    _ = a + (0 + -a)        := by rw [op_inv_left]
    _ = a + -a              := by rw [op_unit_left]
    _ = 0                   := by rw [op_inv_right]

theorem inv_op [Group X] (a b: X): -(a + b) = -b + -a := by
  repeat rw [←neg_eq]
  apply op_cancel_right (c := (a + b))
  rw [op_inv_left]
  apply Eq.symm
  calc
    -b + -a + (a + b)
    _ = -b + (-a + (a + b)) := by rw [op_assoc]
    _ = -b + (-a + a + b)   := by rw [op_assoc]
    _ = -b + (0 + b)        := by rw [op_inv_left]
    _ = -b + b              := by rw [op_unit_left]
    _ = 0                   := by rw [op_inv_left]
