-- Algebra.Category.Constructions

import Algebra.Category.Basic
namespace Category

/-
Given a category C, we can form its opposite category C^op.
-/
def Op (C: Category): Category := {
  Obj := C
  Hom := λ A B ↦ C.Hom B A
  id := λ A ↦ C.id A
  comp := λ g f ↦ f ≪ g
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

def Prod (C₁ C₂: Category): Category := {
  Obj := _root_.Prod C₁ C₂
  Hom := λ (A₁, A₂) (B₁, B₂) ↦ _root_.Prod (C₁.Hom A₁ B₁) (C₂.Hom A₂ B₂)
  id := λ (A₁, A₂) ↦ (C₁.id A₁, C₂.id A₂)
  comp := λ ⟨g₁, g₂⟩ ⟨f₁, f₂⟩ ↦ ⟨g₁ ≪ f₁, g₂ ≪ f₂⟩
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
def Slice (C: Category) (A: C): Category := {
  Obj := Sigma (λ Z ↦ C.Hom Z A)
  Hom := λ ⟨Z₁, f₁⟩ ⟨Z₂, f₂⟩ ↦ Subtype (λ σ: C.Hom Z₁ Z₂ ↦ f₁ = f₂ ≪ σ)
  id := λ ⟨Z, f⟩ ↦ ⟨C.id Z, by rw [compLeft, C.comp_id_right f]⟩
  comp := by
    simp_all
    intro ⟨Z₁, f₁⟩ ⟨Z₂, f₂⟩ ⟨Z₃, f₃⟩ ⟨σ₂, hσ₂⟩ ⟨σ₁, hσ₁⟩
    exists σ₂ ≪ σ₁
    calc f₁
    _ = f₂ ≪ σ₁        := by rw [←hσ₁]
    _ = (f₃ ≪ σ₂) ≪ σ₁ := by rw [←hσ₂]
    _ = f₃ ≪ (σ₂ ≪ σ₁) := by simp only [compLeft, C.comp_assoc]
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
