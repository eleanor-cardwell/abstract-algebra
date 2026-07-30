-- Algebra.Category.Constructions

import Algebra.Category.Basic
namespace Category
variable {X: Type u₁} {Y: Type u₂}

/-
Given a category C, we can form its opposite category C^op.
-/
def Op (C: Category X): Category X := {
  Hom := λ A B ↦ C.Hom B A
  id := λ A ↦ C.id A
  comp := λ g f ↦ C.comp f g
  comp_assoc := by
    intro _ _ _ _ f g h
    exact Eq.symm (C.comp_assoc h g f)
  comp_id_left := by
    intro A B f
    exact C.comp_id_right f
  comp_id_right := by
    intro A B F
    exact C.comp_id_left F
}

def Prod (C₁: Category X) (C₂: Category Y): Category (Prod X Y) := {
  Hom := λ (A₁, A₂) (B₁, B₂) ↦ _root_.Prod (C₁.Hom A₁ B₁) (C₂.Hom A₂ B₂)
  id := λ (A₁, A₂) ↦ (C₁.id A₁, C₂.id A₂)
  comp := λ ⟨g₁, g₂⟩ ⟨f₁, f₂⟩ ↦ ⟨C₁.comp g₁ f₁, C₂.comp g₂ f₂⟩
  comp_assoc := sorry
  comp_id_left := sorry
  comp_id_right := sorry
}

/-
Let C be a category and A ∈ Obj(C). Define a new category C_A where
- the objects are morphisms with target A
- for objects f₁: Z₁ → A and f₂: Z₂ → A, a morphism f₁ → f₂ is a map σ ∈ Hom(Z₁, Z₂) such that
    f₁ = f₂ ∘ σ
and the rest is defined as you would expect
-/
def Slice (C: Category X) (A: X): Category (Sigma (λ Z ↦ C.Hom Z A)) := {
  Hom := λ ⟨Z₁, f₁⟩ ⟨Z₂, f₂⟩ ↦ Subtype (λ σ: C.Hom Z₁ Z₂ ↦ f₁ = C.comp f₂ σ)
  id := λ ⟨Z, f⟩ ↦ ⟨C.id Z, by rw [C.comp_id_right f]⟩
  comp := by
    simp_all
    intro ⟨Z₁, f₁⟩ ⟨Z₂, f₂⟩ ⟨Z₃, f₃⟩ ⟨σ₂, hσ₂⟩ ⟨σ₁, hσ₁⟩
    exists C.comp σ₂ σ₁
    calc f₁
    _ = C.comp f₂ σ₁             := by rw [←hσ₁]
    _ = C.comp (C.comp f₃ σ₂) σ₁ := by rw [←hσ₂]
    _ = C.comp f₃ (C.comp σ₂ σ₁) := by rw [C.comp_assoc]
  comp_assoc := by
    intro ⟨Z₁, f₁⟩ ⟨Z₂, f₂⟩ ⟨Z₃, f₃⟩ ⟨Z₄, f₄⟩ ⟨σ₁, hσ₁⟩ ⟨σ₂, hσ₂⟩ ⟨σ₃, hσ₃⟩
    simp_all
    exact C.comp_assoc σ₁ σ₂ σ₃
  comp_id_left := by
    intro ⟨Z₁, f₁⟩ ⟨Z₂, f₂⟩ ⟨σ, hσ⟩
    simp_all
    exact C.comp_id_left σ
  comp_id_right := by
    intro ⟨Z₁, f₁⟩ ⟨Z₂, f₂⟩ ⟨σ, hσ⟩
    simp_all
    exact C.comp_id_right σ
}
