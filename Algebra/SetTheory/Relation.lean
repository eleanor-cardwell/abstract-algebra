import Algebra.SetTheory.Set

-- Relation

def Relation (X: Type u₁) (Y: Type u₂): Type (max u₁ u₂) :=
  X → Y → Prop

variable {X: Type u₁} {Y: Type u₂}
namespace Relation

def Reflexive (R: Relation X X): Prop :=
  ∀ x: X, R x x

def Symmetric (R: Relation X X): Prop :=
  ∀ x y: X, R x y → R y x

def Transitive (R: Relation X X): Prop :=
  ∀ x y z: X, R x y → R y z → R x z

end Relation



-- Equivalence relation and partition

/-
Let X be a set. An equivalence on X is a relation R on X such that
- R is reflexive;
- R is symmetric; and
- R is transitive
-/
structure EquivalenceRelation (X: Type u₁) where
  R: Relation X X
  reflexive: Relation.Reflexive R
  symmetric: Relation.Symmetric R
  transitive: Relation.Transitive R

/-
Let A be a set. A partition on A is a set F ⊆ 𝓟(A) such that
- each set S ∈ F is nonempty;
- for any sets S, T ∈ F, S and T are disjoint; and
- ∪ F = A
-/
structure Partition (X: Type u₁) where
  F: Set (Set X)
  nonempty: ∀ S ∈ F, Set.Nonempty S
  disjoint: ∀ S ∈ F, ∀ T ∈ F, S ≠ T → S ∩ T = ∅
  union: Set.BigUnion F = Set.FullSet

/--
If you have an equivalence relation on A, then you have a partition on A.
-/
def EquivalenceRelation.toPartition (R: EquivalenceRelation X): Partition X := by
  sorry

/--
If you have a parition on A, then you have an equivalence relation on A.
-/
def Partition.toEquivalence (𝓟: Partition X): EquivalenceRelation X := by
  sorry

/-
TODO
Equivalence relation and partition are equivalent notions, that is, for any set A,
there exists a bijection between equivalence relations on A and partitions on A.
-/
