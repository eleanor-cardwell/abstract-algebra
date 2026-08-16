-- Algebra.Category.HomFunctor

import Algebra.Category.Functor
import Algebra.Set.CatSet
import Algebra.Category.Constructions
namespace Category

def CovariantHomFunctor (C: Type u) [Category C] (X: C): Functor C CatSet := {
  objMap := λ Z: C ↦ Hom X Z
  homMap := λ f ↦ (λ g ↦ f ≪ g)
  id := by
    intro Z
    funext h
    calc
      Category.id Z ≪ h
      _ = h := by rw [comp_id_left]
      _ = Category.id (Hom X Z) h := by rfl
  comp := by
    intro _ _ _ f g
    funext h
    calc
      (g ≪ f) ≪ h
      _ = g ≪ (f ≪ h) := by simp only [comp_assoc]
}

def ContravariantHomFunctor (C: Type u) [Category C] (Y: C): Functor (Op C) CatSet := {
  objMap := λ Z: C ↦ @Hom C _ Z Y
  homMap := λ f ↦ (λ g ↦ g ≪ f)
  id := by
    intro Z
    funext h
    exact @comp_id_right C _ Z Y h
  comp := by
    intro _ _ _ f g
    funext h
    calc
      h ≪ (f ≪ g)
      _ = (h ≪ f) ≪ g := by simp only [comp_assoc]
}

def ContravariantHomFunctor.v2 (C: Type u) [Category C] (Y: C): Functor (Op C) CatSet :=
  CovariantHomFunctor (Op C) Y

def HomFunctor (C: Type u) [Category C]: Functor (Prod (Op C) C) CatSet := {
  objMap := λ (X, Y) ↦ @Hom C _ X Y
  homMap := by
    intro (X₁, X₂) (Y₁, Y₂) (f₁, f₂)
    intro g
    exact f₂ ≪ (g ≪ f₁)
  id := by
    simp_all
    intro X Y
    funext h
    change Category.id Y ≪ (h ≪ Category.id X) = h
    calc
      Category.id Y ≪ (h ≪ Category.id X)
      _ = (Category.id Y ≪ h) ≪ Category.id X := by simp only [comp_assoc]
      _ = h ≪ Category.id X := by
        rw [@comp_id_left C _ X Y h]
      _ = h := by
        exact @comp_id_right C _ X Y h
  comp := by
    simp_all
    intro X₁ X₂ Y₁ Y₂ Z₁ Z₂
    intro f g
    rcases f with ⟨f₁, f₂⟩
    rcases g with ⟨g₁, g₂⟩
    funext h
    calc
      (g₂ ≪ f₂) ≪ (h ≪ (f₁ ≪ g₁))
      _ = g₂ ≪ ((f₂ ≪ (h ≪ f₁)) ≪ g₁) := by simp [comp_assoc]
}
