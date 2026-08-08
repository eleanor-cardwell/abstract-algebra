-- Algebra.Set.CatSet

import Algebra.Category.Basic
import Algebra.Set.Basic

universe u

abbrev CatSet := Type u

/-
The category of sets
-/
instance typeCategory: Category (Type u) where
  Hom := λ X Y ↦ X → Y
  id := λ X ↦ (λ x ↦ x)
  comp := λ g f ↦ g ∘ f
  comp_assoc := by
    intros
    rfl
  comp_id_left := by
    intros
    rfl
  comp_id_right := by
    intros
    rfl

open Category

/-
The empty set is the initial object in the category of sets
-/
theorem set_initial_empty: Initial (C := CatSet) Empty := by
  intro X
  exists λ x ↦ by contradiction
  intro f
  funext x
  contradiction

/-
Any singleton set is a final object in the category of sets
-/
theorem set_final_singleton {S: Type} (h₁: Subsingleton S) (h₂: Nonempty S): Final (C := CatSet) S := by
  intro X
  exists λ x ↦ Classical.choice h₂
  intro f
  funext x
  exact Subsingleton.elim _ _

/-
Thus all singletons are isomorphic (of course...)
-/
example {S T: Type} (h₁: Subsingleton S) (h₂: Nonempty S) (h₃: Subsingleton T) (h₄: Nonempty T): Isomorphic S T := by
  have hS := set_final_singleton h₁ h₂
  have hT := set_final_singleton h₃ h₄
  exact final_objects_isomorphic hS hT

/-
The category of sets has a product, the Cartesian product
-/
theorem set_has_product: HasProduct CatSet := by
  intro X Y
  exists Prod X Y
  exists λ ⟨x, y⟩ ↦ x
  exists λ ⟨x, y⟩ ↦ y
  intro Z fX fY
  simp_all
  constructor
  · exists λ z ↦ ⟨fX z, fY z⟩
  · sorry
