import Algebra.SetTheory.Function

variable {X: Type u₁} {Y: Type u₂}

-- Define a quotient from an equivalence relation

def EquivalenceRelation.toSetoid (R: EquivalenceRelation X): Setoid X := {
  r := R
  iseqv := by
    constructor
    · exact R.reflexive
    · intro x₁ x₂ h
      exact R.symmetric x₁ x₂ h
    · intro x₁ x₂ x₃ h₁ h₂
      exact R.transitive x₁ x₂ x₃ h₁ h₂
}

def EquivalenceRelation.toQuotient (R: EquivalenceRelation X): Type u₁ :=
  Quotient R.toSetoid



-- Canonical decomposition of a function

/--
For a set X and equivalence relation ~ on X, the "canonical project" of a set into its
quotient is a map X → X / ~ given by x ↦ [x]_~.
-/
def EquivalenceRelation.CanonicalProjection (R: EquivalenceRelation X): X → R.toQuotient :=
  λ x ↦ Quotient.mk R.toSetoid x

/--
The "canonical projection" map is surjective.
-/
theorem EquivalenceRelation.canonical_projection_surjective (R: EquivalenceRelation X): Function.Surjective R.CanonicalProjection := by
  intro q
  refine Quotient.inductionOn q ?_
  intro x
  exists x

/--
Given any function f: X → Y, you can define an equivalence relation on X by x₁ ~ x₂ ↔ f(x₁) = f(x₂).
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

/--
For a set X and a function f: X → Y, using the equivalence relation defined above, the "canonical bijection" is a map
X/~ → range(f) given by [x]_~ ↦ f(x).
-/
def Function.CanonicalBijection (f: X → Y) : f.toEquivalenceRelation.toQuotient → f.Range :=
  Quotient.lift f.restrictToRange (by
    intro x₁ x₂ h
    apply Subtype.ext
    exact h
  )

/--
This map is a bijection.
-/
theorem Function.canonical_bijection_bijective (f: X → Y): Function.Bijective f.CanonicalBijection := by
  constructor
  · intro q₁ q₂ h
    revert h
    refine Quotient.inductionOn₂ q₁ q₂ ?_
    intro x₁ x₂ h
    apply Quotient.sound
    exact Subtype.mk.inj h
  · intro ⟨y, x, hx⟩
    exists Quotient.mk f.toEquivalenceRelation.toSetoid x
    exact Subtype.ext hx

/--
Given a function f: X → Y, the following is the "canonical decomposition":
-/
theorem Function.canonical_decomposition (f: X → Y): f = (Function.Inclusion f.Range) ∘ (f.CanonicalBijection) ∘ (f.toEquivalenceRelation.CanonicalProjection) := by
  funext x
  simp [comp_apply]
  rfl
