-- Algebra.Category.HomFunctor

import Algebra.Category.Functor
import Algebra.Set.CatSet
import Algebra.Category.Constructions
namespace Category

def CovariantHomFunctor {X: Type u} (C: Category X) (A: X): Functor C CatSet := {
  objMap := λ Z: X ↦ C.Hom A Z
  homMap := λ f ↦ (λ g ↦ C.comp f g)
  id := by
    intro Z
    funext h
    calc
      C.comp (C.id Z) h
      _ = h := by rw [C.comp_id_left]
      _ = CatSet.id (C.Hom A Z) h := by rfl
  comp := by
    intro _ _ _ f g
    funext h
    calc
      C.comp (C.comp g f) h
      _ = C.comp g (C.comp f h) := by rw [C.comp_assoc]
      _ = (fun p => C.comp g p) (C.comp f h) := by rfl
      _ = (fun p => C.comp g p) ((fun q => C.comp f q) h) := by rfl
      _ = ((fun p => C.comp g p) ∘ (fun q => C.comp f q)) h := by rfl
      _ = (CatSet.comp (fun p => C.comp g p) (fun q => C.comp f q)) h := by rfl
}

def ContravariantHomFunctor {X: Type u} (C: Category X) (B: X): Functor (Op C) CatSet := {
  objMap := λ Z: X ↦ C.Hom Z B
  homMap := λ f ↦ (λ g ↦ C.comp g f)
  id := by
    intro Z
    funext h
    calc
      C.comp h (C.id Z)
      _ = h := by rw [C.comp_id_right]
      _ = CatSet.id (C.Hom Z B) h := by rfl
  comp := by
    intro _ _ _ f g
    funext h
    calc
      C.comp h (C.Op.comp g f)
      _ = C.comp h (C.comp f g) := by rfl
      _ = C.comp (C.comp h f) g := by rw [C.comp_assoc]
      _ = CatSet.comp (fun g_1 => C.comp g_1 g) (fun g => C.comp g f) h := by rfl
}

def ContravariantHomFunctor.v2 {X: Type u} (C: Category X) (B: X): Functor (Op C) CatSet :=
  CovariantHomFunctor C.Op B

def HomFunctor {X: Type u} (C: Category X): Functor (Prod C.Op C) CatSet := {
  objMap := λ (A₁, A₂) ↦ C.Hom A₁ A₂
  homMap := by
    intro (A₁, A₂) (B₁, B₂) (f₁, f₂)
    intro g
    exact C.comp f₂ (C.comp g f₁)
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
    calc C.comp (C.comp g₂ f₂) (C.comp h (C.comp f₁ g₁))
    _ = C.comp g₂ (C.comp (C.comp f₂ (C.comp h f₁)) g₁) := by simp [C.comp_assoc]
    _ = (fun g => C.comp g₂ (C.comp g g₁)) (C.comp f₂ (C.comp h f₁)) := by rfl
    _ = (fun g => C.comp g₂ (C.comp g g₁)) ((fun g => C.comp f₂ (C.comp g f₁)) h) := by rfl
    _ = ((fun g => C.comp g₂ (C.comp g g₁)) ∘ (fun g => C.comp f₂ (C.comp g f₁))) h := by rfl
    _ = CatSet.comp (fun g => C.comp g₂ (C.comp g g₁)) (fun g => C.comp f₂ (C.comp g f₁)) h := by rfl
}
