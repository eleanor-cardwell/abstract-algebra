-- Algebra.Set.Function

import Algebra.Set.Basic

variable {X: Type u₁} {Y: Type u₂} {Z: Type u₃}

namespace Function

-- Injective, surjective, bijective

def Bijective (f: X → Y): Prop :=
  Injective f ∧ Surjective f

-- Identity map

def Identity: X → X :=
  λ x ↦ x
  
-- Inclusion map

def Inclusion (S: Set X): S → X :=
  λ a ↦ a

theorem inclusion_injective (S: Set X): Injective (Inclusion S) := by
  intro _ _ h
  exact Subtype.ext h

-- Range

def Range (f: X → Y): Set Y :=
  λ y ↦ ∃ x, f x = y

theorem range_mem (f: X → Y) (a: X): f a ∈ Range f := by
  exists a

def RestrictCodomain (f: X → Y): X → f.Range :=
  λ x ↦ Subtype.mk (f x) (by exists x)
  
-- Image and preimage of sets

def Set.Image (f: X → Y) (A: Set X): Set Y :=
  λ b ↦ ∃ a ∈ A, f a = b

def Set.Preimage (f: X → Y) (B: Set Y): Set X :=
  λ a ↦ f a ∈ B
