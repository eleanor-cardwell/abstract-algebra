import Algebra.Group.Basic

namespace Group

variable {X: Type u₁} {Y: Type u₂} {Z: Type u₃}

-- Group homomorphism

structure Hom (G₁: Group X) (G₂: Group Y) where
  map: X → Y
  preserves_op: ∀ x₁ x₂, map (x₁ + x₂) = (map x₁) + (map x₂)

instance [G₁: Group X] [G₂: Group Y]: CoeFun (Hom G₁ G₂) (λ _ ↦ X → Y) := ⟨λ f ↦ f.map⟩

-- Homomorphism preserves identity and inverse operation

theorem hom_preserves_id [G₁: Group X] [G₂: Group Y] (f: Hom G₁ G₂): (0: Y) = f (0: X) := by
  have h := calc 
        0 + f 0
    _ = f 0 := by rw [op_unit_left]
    _ = f (0 + 0) := by rw [op_unit_left 0]
    _ = f 0 + f 0 := by rw [f.preserves_op]
  exact op_cancel_right h

theorem hom_preserves_inverse [G₁: Group X] [G₂: Group Y] (f: Hom G₁ G₂) (x: X): f (-x) = -(f x) := by
  have h := calc
        f (-x) + f x
    _ = f (-x + x) := by rw [f.preserves_op]
    _ = f 0 := by rw [op_inv_left]
    _ = 0 := by rw [←hom_preserves_id]
    _ = -(f x) + f x := by rw [op_inv_left]
  exact op_cancel_right h

-- There is an identity homomorphism

def IdentityHom [G: Group X]: Hom G G := {
  map := Function.Identity
  preserves_op := by
    intro _ _
    unfold Function.Identity
    rfl
}

-- Composing homomorphisms results in another homomorphism

def ComposeHom [G₁: Group X] [G₂: Group Y] [G₃: Group Z] (g: Hom G₂ G₃) (f: Hom G₁ G₂): Hom G₁ G₃ := {
  map := g ∘ f
  preserves_op := by
    intro x₁ x₂
    simp_all
    rw [←g.preserves_op]
    rw [←f.preserves_op]
}
