-- Algebra/Set/Function

import Algebra.Set.Relation

variable {X: Type u₁} {Y: Type u₂} {Z: Type u₃}



-- Injective, surjective, and bijective functions defined by inverses <-- LIE

namespace Function

def Bijective (f: X → Y): Prop :=
  Injective f ∧ Surjective f

def Identity: X → X :=
  λ x ↦ x

/-
Let X and Y be sets. Assume X is nonempty.
A function f: X → Y is injective if and only if it has a left inverse, that is, there exists
function g: Y → X such that g ∘ f = id_X.

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

/-
Let X and Y be sets.
A function g: Y → X is surjective if and only if it has a right inverse, that is, there exists a
function f: X → Y such that g ∘ f = id_X.

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

/-
A function f: X → Y is bijective if and only if it has an inverse, that is, there exists a function
g: Y → X such that g ∘ f = id_X and f ∘ g = id_Y.
-/
theorem bijective_iff_inverse (f: X → Y): Bijective f ↔ ∃ g, g ∘ f = Identity ∧ f ∘ g = Identity := by
  sorry



-- Left and right cancellable

/-
A function f: X → Y is left cancellable if for all functions g, h: W → X, f ∘ g = f ∘ h → g = h.
-/
def LeftCancellable (f: X → Y): Prop :=
  ∀ W: Type u₃, ∀ g h: W → X, f ∘ g = f ∘ h → g = h

/-
A function f: X → Y is injective if and only if it left cancellable.

Proof:
(=>)

(<=)
-/
theorem injective_iff_left_cancellable (f: X → Y): Injective f ↔ LeftCancellable f := by
  sorry

/-
A function f: X → Y is right cancellable if for all functions g, h: Y → Z, g ∘ f = h ∘ f → g = h.
-/
def RightCancellable (f: X → Y): Prop :=
  ∀ Z: Type u₃, ∀ g h: Y → Z, g ∘ f = h ∘ f → g = h

/-
A function f: X → Y is surjective if and only if it right cancellable.

Proof:
(=>)

(<=)
-/
theorem surjective_iff_right_cancellable (f: X → Y): Surjective f ↔ RightCancellable f := by
  sorry



-- Inclusion map

def Inclusion {B: Type u₁} (A: Set B): A → B :=
  λ a ↦ a

theorem inclusion_injective (B: Type u₁) (A: Set B): Injective (Inclusion A) := by
  intro x₁ x₂ h
  unfold Inclusion at h
  exact Subtype.ext h



-- Image

def Range (f: X → Y): Set Y :=
  λ y ↦ ∃ x, f x = y

def restrictToRange (f: X → Y): X → f.Range :=
  λ x ↦ Subtype.mk (f x) (by exists x)
