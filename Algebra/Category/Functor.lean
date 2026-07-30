-- Algebra.Category.Functor

import Algebra.Category.Basic
namespace Category

structure Functor (C D: Category) where
  objMap: C → D
  homMap {A B: C}: C.Hom A B → D.Hom (objMap A) (objMap B)
  id {A: C}: homMap (C.id A) = D.id (objMap A)
  comp {A₁ A₂ A₃: C} (f: C.Hom A₁ A₂) (g: C.Hom A₂ A₃): homMap (g ≪ f) = homMap g ≪ homMap f

def IdentityFunctor (C: Category): Functor C C := {
  objMap := λ A ↦ A
  homMap := λ f ↦ f
  id := by
    intro _
    rfl
  comp := by
    intro _ _ _ _ _
    rfl
}

def ComposeFunctors {C₁ C₂ C₃: Category} (F₂: Functor C₂ C₃) (F₁: Functor C₁ C₂): Functor C₁ C₃ := {
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
