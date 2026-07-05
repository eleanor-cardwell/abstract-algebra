import Algebra.SetTheory.Relation

variable {X: Type u₁} {Y: Type u₂} {Z: Type u₃}

-- Injective, surjective, and bijective functions

/-
A function f: X → Y is injective if
∀ x₁, x₂ ∈ X, f(x₁) = f(x₂) → x₁ = x₂
-/
def Injective (f: X → Y): Prop :=
  ∀ x₁ x₂, f x₁ = f x₂ → x₁ = x₂

/-
A function f: X → Y is surjective if
∀ y ∈ Y, ∃ x ∈ X, f(x) = y
-/
def Surjective (f: X → Y): Prop :=
  ∀ y, ∃ x, f x = y

/-
A function is bijective if it is injective and surjective.
-/
def Bijective (f: X → Y): Prop :=
  Injective f ∧ Surjective f



-- Injective, surjective, and bijective functions defined by inverses

namespace Function

def Identity: X → X :=
  λ x ↦ x

/--
Let X and Y be sets. Assume X is nonempty.
A function f: X → Y is injective if and only if it has a left inverse, that is,
there exists function g: Y → X such that g ∘ f = id_X.

Proof:
(=>)

(<=)
-/
theorem injective_iff_left_inverse (hX: Nonempty X) (f: X → Y): Injective f ↔ ∃ g, g ∘ f = Identity := by
  constructor
  · intro h
    have x₀: X := Classical.choice hX
    sorry
  · intro ⟨g, hg⟩ x₁ x₂ h
    have h₁ := congrArg g h
    have h₂: (g ∘ f) x₁ = (g ∘ f) x₂ := h₁
    rw [hg] at h₂
    exact h₂

/--
Let X and Y be sets.
A function g: Y → X is surjective if and only if it has a right inverse, that is,
there exists a function f: X → Y such that g ∘ f = id_X.

Proof:
(=>)

(<=)
-/
theorem surjective_iff_right_inverse (g: Y → X): Surjective g ↔ ∃ f, g ∘ f = Identity := by
  constructor
  · intro h
    sorry
  · intro h
    sorry

/--
A function f: X → Y is bijective if and only if it has an inverse, that is,
there exists a function g: Y → X such that g ∘ f = id_X and f ∘ g = id_Y.
-/
theorem bijective_iff_inverse (f: X → Y): Bijective f ↔ ∃ g, g ∘ f = Identity ∧ f ∘ g = Identity := by
  sorry



-- Monomorphisms and epimorphisms

/--
A function f: X → Y is a monomorphism if it is left cancellable, that is,
for all functions g, h: W → X, f ∘ g = f ∘ h → g = h.
-/
def Monic (f: X → Y): Prop :=
  ∀ W: Type u₃, ∀ g h: W → X, f ∘ g = f ∘ h → g = h

/--
A function f: X → Y is injective if and only if it is monic.

Proof:
(=>)

(<=)
-/
theorem injective_iff_monic (f: X → Y): Injective f ↔ Monic f := by
  sorry

/--
A function f: X → Y is an epimorphism if it is right cancellable, that is,
for all functions g, h: Y → Z, g ∘ f = h ∘ f → g = h.
-/
def Epic (f: X → Y): Prop :=
  ∀ Z: Type u₃, ∀ g h: Y → Z, g ∘ f = h ∘ f → g = h

/--
A function f: X → Y is surjective if and only if it is epic.

Proof:
(=>)

(<=)
-/
theorem surjective_iff_epic (f: X → Y): Surjective f ↔ Epic f := by
  sorry



-- Canonical decomposition

/--
Given a function f: X → Y, you can define an equivalence relation on X by x₁ ~ x₂ ↔ f(x₁) = f(x₂).
-/
def Function.toEquivalenceRelation (f: X → Y): EquivalenceRelation X := {
  R := λ x₁ x₂ ↦ f x₁ = f x₂
  reflexive := by
    intro _
    rfl
  symmetric := by
    intro x₁ x₂ h
    exact Eq.symm h
  transitive := by
    intro x₁ x₂ x₃ h₁ h₂
    rw [h₁, h₂]
}
