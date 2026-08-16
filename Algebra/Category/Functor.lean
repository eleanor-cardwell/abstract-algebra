-- Algebra.Category.Functor

import Algebra.Category.Basic
namespace Category

structure Functor (C: Type u) (D: Type v)
    [Category C] [Category D] where
  objMap: C → D
  homMap {X Y: C}: Hom X Y → Hom (objMap X) (objMap Y)
  id {X: C}: homMap (Category.id X) = Category.id (objMap X)
  comp {X Y Z: C} (f: Hom X Y) (g: Hom Y Z): homMap (g ≪ f) = homMap g ≪ homMap f

def IdentityFunctor (C: Type u) [Category C]: Functor C C := {
  objMap := λ X ↦ X
  homMap := λ f ↦ f
  id := by
    intro _
    rfl
  comp := by
    intro _ _ _ _ _
    rfl
}

def ComposeFunctors {C₁: Type u} {C₂: Type v} {C₃: Type w}
    [Category C₁] [Category C₂] [Category C₃]
    (F₂: Functor C₂ C₃) (F₁: Functor C₁ C₂): Functor C₁ C₃ := {
  objMap := F₂.objMap ∘ F₁.objMap
  homMap := F₂.homMap ∘ F₁.homMap
  id := by
    intro X
    simp
    rw [F₁.id, F₂.id]
  comp := by
    intro X Y Z f g
    simp
    rw [F₁.comp, F₂.comp]
}
