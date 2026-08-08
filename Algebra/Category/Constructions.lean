-- Algebra.Category.Constructions

import Algebra.Category.Basic
namespace Category

/-
Given a category C, we can form its opposite category C^op.
-/
def Op (C: Type u) := C

instance opCategory {C: Type u} [Category C]: Category (Op C) where
  Hom := λ X Y ↦ @Hom C _ Y X
  id := λ X ↦ @id C _ X
  comp := λ g f ↦ @comp C _ _ _ _ f g
  comp_assoc := by
    intro _ _ _ _ f g h
    exact Eq.symm (comp_assoc h g f)
  comp_id_left := by
    intro X Y f
    exact comp_id_right f
  comp_id_right := by
    intro X Y f
    exact comp_id_left f

abbrev Prod (C₁: Type u) (C₂: Type v) := _root_.Prod C₁ C₂

instance prodCategory {C₁: Type u} {C₂: Type v}
    [Category C₁] [Category C₂]: Category (Prod C₁ C₂) where
  Hom := λ (X₁, X₂) (Y₁, Y₂) ↦ _root_.Prod (@Hom C₁ _ X₁ Y₁) (@Hom C₂ _ X₂ Y₂)
  id := λ (X₁, X₂) ↦ (@id C₁ _ X₁, @id C₂ _ X₂)
  comp := λ ⟨g₁, g₂⟩ ⟨f₁, f₂⟩ ↦
    ⟨@comp C₁ _ _ _ _ g₁ f₁, @comp C₂ _ _ _ _ g₂ f₂⟩
  comp_assoc := sorry
  comp_id_left := sorry
  comp_id_right := sorry

/-
Let C be a category and A ∈ Obj(C). Define a new category C_A where
- the objects are morphisms with target A
- for objects f₁: Z₁ → A and f₂: Z₂ → A, a morphism f₁ → f₂ is a map σ ∈ Hom(Z₁, Z₂) such that
    f₁ = f₂ ∘ σ
and the rest is defined as you would expect
-/
abbrev Slice {C: Type u} [Category C] (X: C) :=
  Sigma (λ Y ↦ Hom Y X)

instance sliceCategory {C: Type u} [Category C] {X: C}: Category (Slice X) where
  Hom := λ ⟨Y₁, f₁⟩ ⟨Y₂, f₂⟩ ↦ Subtype (λ σ: @Hom C _ Y₁ Y₂ ↦ f₁ = f₂ ≪ σ)
  id := λ ⟨Y, f⟩ ↦ ⟨Category.id Y, by rw [comp_id_right f]⟩
  comp := by
    simp_all
    intro ⟨Y₁, f₁⟩ ⟨Y₂, f₂⟩ ⟨Y₃, f₃⟩ ⟨σ₂, hσ₂⟩ ⟨σ₁, hσ₁⟩
    exists σ₂ ≪ σ₁
    calc f₁
    _ = f₂ ≪ σ₁        := by rw [←hσ₁]
    _ = (f₃ ≪ σ₂) ≪ σ₁ := by rw [←hσ₂]
    _ = f₃ ≪ (σ₂ ≪ σ₁) := by simp only [comp_assoc]
  comp_assoc := by
    intro ⟨Y₁, f₁⟩ ⟨Y₂, f₂⟩ ⟨Y₃, f₃⟩ ⟨Y₄, f₄⟩ ⟨σ₁, hσ₁⟩ ⟨σ₂, hσ₂⟩ ⟨σ₃, hσ₃⟩
    simp_all
    exact comp_assoc σ₁ σ₂ σ₃
  comp_id_left := by
    intro ⟨Y₁, f₁⟩ ⟨Y₂, f₂⟩ ⟨σ, hσ⟩
    simp_all
    exact comp_id_left σ
  comp_id_right := by
    intro ⟨Y₁, f₁⟩ ⟨Y₂, f₂⟩ ⟨σ, hσ⟩
    simp_all
    exact comp_id_right σ
