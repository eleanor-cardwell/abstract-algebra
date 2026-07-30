-- Algebra/Set/CatSet
import Algebra.Category.Basic
import Algebra.Set.Basic

/-
The category of sets
-/
def CatSet: Category (Type u) := {
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
}

open Category

/-
The empty set is the initial object in the category of sets
-/
theorem set_initial_empty: Initial CatSet Empty := by
  intro X
  exists λ x ↦ by contradiction
  intro f
  funext x
  contradiction

/-
Any singleton set is a final object in the category of sets
-/
theorem set_final_singleton {S: Type} (h₁: Subsingleton S) (h₂: Nonempty S): Final CatSet S := by
  intro X
  exists λ x ↦ Classical.choice h₂
  intro f
  funext x
  exact Subsingleton.elim _ _

/-
Thus all singletons are isomorphic (of course...)
-/
example {S T: Type} (h₁: Subsingleton S) (h₂: Nonempty S) (h₃: Subsingleton T) (h₄: Nonempty T): Isomorphic CatSet S T := by
  have hS := set_final_singleton h₁ h₂
  have hT := set_final_singleton h₃ h₄
  exact final_objects_isomorphic hS hT

/-
The category of sets has a product, the Cartesian product
-/
theorem set_has_product: HasProduct CatSet := by
  intro A B
  exists Prod A B
  exists λ ⟨a, b⟩ ↦ a
  exists λ ⟨a, b⟩ ↦ b
  intro Z fA fB
  simp_all
  constructor
  · exists λ z ↦ ⟨fA z, fB z⟩
  · intro σ₁ σ₂ ⟨⟨hσ₁a, hσ₁b⟩ , ⟨hσ₂a, hσ₂b⟩⟩
    sorry
