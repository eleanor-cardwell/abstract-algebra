-- Algebra.Category.HomFunctor

import Algebra.Category.Functor
import Algebra.Set.CatSet
import Algebra.Category.Constructions
namespace Category

def CovariantHomFunctor (C: Category) (A: C): Functor C CatSet := {
  objMap := λ Z: C ↦ C.Hom A Z
  homMap := λ f ↦ (λ g ↦ f ≪ g)
  id := by
    intro Z
    funext h
    calc
      C.id Z ≪ h
      _ = h := by rw [compLeft, C.comp_id_left]
      _ = CatSet.id (C.Hom A Z) h := by rfl
  comp := by
    intro _ _ _ f g
    funext h
    calc
      (g ≪ f) ≪ h
      _ = g ≪ (f ≪ h) := by simp only [compLeft, C.comp_assoc]
}

def ContravariantHomFunctor (C: Category) (B: C): Functor (Op C) CatSet := {
  objMap := λ Z: C ↦ C.Hom Z B
  homMap := λ f ↦ (λ g ↦ g ≪ f)
  id := by
    intro Z
    funext h
    calc
      h ≪ C.id Z
      _ = h := by rw [compLeft, C.comp_id_right]
      _ = CatSet.id (C.Hom Z B) h := by rfl
  comp := by
    intro _ _ _ f g
    funext h
    calc
      h ≪ (f ≪ g)
      _ = (h ≪ f) ≪ g := by simp only [compLeft, C.comp_assoc]
}

def ContravariantHomFunctor.v2 (C: Category) (B: C): Functor (Op C) CatSet :=
  CovariantHomFunctor C.Op B

def HomFunctor (C: Category): Functor (Prod C.Op C) CatSet := {
  objMap := λ (A₁, A₂) ↦ C.Hom A₁ A₂
  homMap := by
    intro (A₁, A₂) (B₁, B₂) (f₁, f₂)
    intro g
    exact f₂ ≪ (g ≪ f₁)
  id := by
    unfold Prod
    unfold Op
    simp_all
    intro A₁ A₂
    simp [C.comp_id_left, C.comp_id_right]
    rfl
  comp := by
    unfold Prod
    unfold Op
    simp_all
    intro A₁ A₂ B₁ B₂ C₁ C₂
    intro f₁ f₂ g₁ g₂
    funext h
    calc (g₂ ≪ f₂) ≪ (h ≪ (f₁ ≪ g₁))
    _ = g₂ ≪ ((f₂ ≪ (h ≪ f₁)) ≪ g₁) := by simp [compLeft, C.comp_assoc]
}
