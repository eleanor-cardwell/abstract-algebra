import Algebra.CategoryTheory.Category
import Algebra.SetTheory.Relation

/-
The category of sets
-/
def Category.Set: Category (Type u₁) := {
  /-
    Morphisms from type X to Y are simply functions X → Y.
  -/
  Hom := λ X Y ↦ X → Y

  /-
    The identity morphism on any type is simply the identity function.
  -/
  id := λ X ↦ (λ x ↦ x)

  /-
    Composition of morphisms is simply composition of functions.
  -/
  comp := λ g f ↦ g ∘ f

  /-
    Composition of functions is, of course, associative.
  -/
  comp_assoc := by
    intros
    rfl

  /-
    The identity function is a left and right identity under composition.
  -/
  comp_id_left := by
    intros
    rfl
  comp_id_right := by
    intros
    rfl
}

/-
The empty set is the initial object in the category of sets
-/
example: Category.Initial Category.Set Empty := by
  intro Ss
  sorry


/-
Preorder category
-/
def Category.Preorder {X: Type u₁} (R: Relation.Preorder X): Category X := {
  /-
    There is exactly one morphism from x → y if x ≤ y, otherwise there are no morphisms.
    What the morphism is doesn't really matter. Here it is just a proof of x ≤ y.
  -/
  Hom := λ x y ↦ PLift (R.R x y)

  /-
    The identity morphism for any object x is just the proof of reflexivity which comes with every
    preorder, that is, that x ≤ x.
  -/
  id := λ x ↦ PLift.up (R.reflexive x)

  /-
    If we have a proof that x ≤ y and a proof that y ≤ z, we can use the transitivity of the given
    preorder to produce a proof that x ≤ z.
  -/
  comp := λ g f ↦ PLift.up (R.transitive _ _ _ (PLift.down f) (PLift.down g))

  /-
    Associativity of composition follows simply because both homs are of the same type and our
    homs here only have 1 possible inhabitant (?)
  -/
  comp_assoc := by
    intros
    rfl

  /-
    Identity follows for the same reason
  -/
  comp_id_left := by
    intros
    rfl
  comp_id_right := by
    intros
    rfl
}

/-
Subset relation is a preorder, so we get a category from that
-/
def Set.SubsetPreorder (X: Type u₁): Relation.Preorder (Set X) := {
  R := λ S T ↦ S ⊆ T
  reflexive := Set.subset_self
  transitive := by
    intro S T U h₁ h₂
    intro s hs
    have h₃ := h₁ s hs
    have h₄ := h₂ s h₃
    exact h₄
}

def Category.SubsetPreorder (X: Type u₁): Category (_root_.Set X) :=
  Category.Preorder (Set.SubsetPreorder X)
