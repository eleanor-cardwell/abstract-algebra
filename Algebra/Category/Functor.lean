-- Algebra.Category.Functor

import Algebra.Category.Basic
namespace Category

structure Functor {X: Type u₁} {Y: Type u₂} (C: Category X) (D: Category Y) where
  objMap: X → Y
  homMap {A B: X}: C.Hom A B → D.Hom (objMap A) (objMap B)
  id {A: X}: homMap (C.id A) = D.id (objMap A)
  comp {A₁ A₂ A₃: X} (f: C.Hom A₁ A₂) (g: C.Hom A₂ A₃): homMap (C.comp g f) = D.comp (homMap g) (homMap f)

def IdentityFunctor {X: Type u} (C: Category X): Functor C C := {
  objMap := λ A ↦ A
  homMap := λ f ↦ f
  id := by
    intro _
    rfl
  comp := by
    intro _ _ _ _ _
    rfl
}

def ComposeFunctors {X₁: Type u₁} {X₂: Type u₂} {X₃: Type u₃} {C₁: Category X₁} {C₂: Category X₂} {C₃: Category X₃} (F₂: Functor C₂ C₃) (F₁: Functor C₁ C₂): Functor C₁ C₃ := {
  objMap := F₂.objMap ∘ F₁.objMap
  homMap := F₂.homMap ∘ F₁.homMap
  id := by
    intro _
    simp
    rw [F₁.id, F₂.id]
  comp := by
    intro _ _ _ _ _
    simp
    rw [F₁.comp, F₂.comp]
}
