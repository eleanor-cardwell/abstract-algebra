-- Algebra/Set/Basic

import Algebra.Basic

variable {X: Type u₁} {Y: Type u₂} {Z: Type u₃}

-- Set

def Set (X: Type u₁): Type u₁ :=
  X → Prop

instance (X: Type u₁): CoeSort (Set X) (Type u₁) := ⟨Subtype⟩
namespace Set



-- Membership and subset

def Mem (A: Set X) (x: X): Prop :=
  A x

instance: Membership X (Set X) := ⟨Mem⟩

def Subset (A B: Set X): Prop :=
  ∀ x, x ∈ A → x ∈ B

instance: HasSubset (Set X) := ⟨Subset⟩

/-
Every set is a subset of itself.
-/
theorem subset_self (A: Set X): A ⊆ A := by
  intro _ h
  exact h



-- Empty set

def EmptySet {X: Type u₁}: Set X :=
  λ _ ↦ False

instance: EmptyCollection (Set X) := ⟨EmptySet⟩

/-
The empty set is a subset of every set.
-/
theorem empty_subset (A: Set X): ∅ ⊆ A := by
  exact λ _ ↦ False.elim



-- Full set

def FullSet {X: Type u₁}: Set X :=
  λ _ ↦ True

/-
Every set is a subset of the full set of which it is a subset... Redundant statement.
-/
theorem subset_full (A: Set X): A ⊆ FullSet := by
  exact λ _ _ ↦ trivial

end Set

-- Union

def Set.Union (A B: Set X): Set X :=
  λ x ↦ x ∈ A ∨ x ∈ B

instance: Union (Set X) := {
  union := Set.Union
}

namespace Set

/-
If a ∈ A, then a ∈ A ∪ B.
-/
theorem union_left {A B: Set X} {a: X} (h: a ∈ A): a ∈ A ∪ B := by
  apply Or.inl
  exact h

/-
If a ∈ B, then a ∈ A ∪ B.
-/
theorem union_right {A B: Set X} {a: X} (h: a ∈ B): a ∈ A ∪ B := by
  apply Or.inr
  exact h

/-
∅ ∪ A = A.
-/
theorem union_left_identity: LeftIdentity Union (@EmptySet X) := by
  intro
  funext
  simp [Union]
  exact or_iff_right id

/-
A ∪ ∅ = A.
-/
theorem union_right_identity: RightIdentity Union (@EmptySet X) := by
  intro
  funext
  simp [Union]
  exact or_iff_left id

/-
The empty set is an identity under union.
-/
theorem union_identity: Identity Union (@EmptySet X) := by
  exact ⟨union_left_identity, union_right_identity⟩

/-
Union is associative, that is, A ∪ (B ∪ C) = (A ∪ B) ∪ C.
-/
theorem union_assoc: Associative (@Union X) := by
  intro _ _ _
  funext
  simp [Union]
  constructor
  · intro h; cases h with
    | inl h => cases h with
      | inl => apply Or.inl; assumption
      | inr => apply Or.inr; apply Or.inl; assumption
    | inr => apply Or.inr; apply Or.inr; assumption
  · intro h; cases h with
    | inl => apply Or.inl; apply Or.inl; assumption
    | inr h => cases h with
      | inl => apply Or.inl; apply Or.inr; assumption
      | inr => apply Or.inr; assumption

/-
Union is commutative, that is, A ∪ B = B ∪ A.
-/
theorem union_comm: Commutative (@Union X) := by
  intro A B
  funext x
  simp [Union]
  exact Or.comm



-- Intersection

def Intersection (A B: Set X): Set X :=
  λ x ↦ x ∈ A ∧ x ∈ B

instance: Inter (Set X) := ⟨Intersection⟩

/-
If a ∈ A ∩ B, then a ∈ A.
-/
theorem inter_left {A B: Set X} {a: X} (h: a ∈ A ∩ B): a ∈ A := by
  exact h.left

/-
If a ∈ A ∩ B, then a ∈ B.
-/
theorem inter_right {A B: Set X} {a: X} (h: a ∈ A ∩ B): a ∈ B := by
  exact h.right

/-
The full set is an identity under intersection.
-/
theorem inter_identity: Identity Intersection (@FullSet X) := by
  constructor
  · intro
    funext
    simp [Intersection]
    constructor
    · intro h; exact h.right
    · intro h; exact ⟨trivial, h⟩
  · intro
    funext
    simp [Intersection]
    constructor
    · intro h; exact h.left
    · intro h; exact ⟨h, trivial⟩

/-
Intersection is assocative, that is, A ∩ (B ∩ C) = (A ∩ B) ∩ C.
-/
theorem inter_assoc: Associative (@Intersection X) := by
  intro _ _ _
  funext
  simp [Intersection]
  apply and_assoc

/-
Intersection is commutative, that is, A ∩ B = B ∩ A.
-/
theorem inter_comm: Commutative (@Intersection X) := by
  intro A B
  funext x
  simp [Intersection]
  constructor <;> (intro h; exact And.symm h;)



-- Complement & nonempty

def Compliment (A: Set X): Set X :=
  λ x ↦ x ∉ A

def Nonempty (S: Set X): Prop :=
  ∃ a, a ∈ S

/-
For a set A, A is nonempty iff. A ≠ ∅.
-/
theorem nonempty_iff {S: Set X}: Nonempty S ↔ S ≠ ∅ := by
  constructor
  · intro ⟨a, ha⟩
    intro h
    have: a ∉ S := by exact of_eq_false (congrFun h a)
    contradiction
  · apply contrapose
    simp [Nonempty]
    intro h
    funext _
    simp
    constructor
    · intro h'
      exact h _ h'
    · intro h'
      exact False.elim h'

/-
For a set A, A is not nonempty iff. A = ∅.
-/
theorem not_nonempty_iff {S: Set X}: ¬(Nonempty S) ↔ S = ∅ := by
  apply contrapose_iff
  simp
  exact Iff.symm nonempty_iff



-- Singleton

def Singleton {X: Type u₁} (a: X): Set X :=
  λ x ↦ x = a



-- Union of a set of subsets

def BigUnion (S: Set (Set X)): Set X :=
  λ a ↦ ∃ A ∈ S, a ∈ A

/-
The big union of the empty set is the empty set.
-/
theorem big_union_empty: BigUnion (∅: Set (Set X)) = ∅ := by
  funext x
  simp [BigUnion]
  constructor
  · intro ⟨_, _, _⟩
    contradiction
  · intro _
    contradiction

/-
The big union of the full set is the full set.
-/
theorem big_union_full: BigUnion (FullSet: (Set (Set X))) = FullSet := by
  sorry



-- Intersection of a set of subsets

def BigIntersection (S: Set (Set X)): Set X :=
  λ a ↦ ∀ A ∈ S, a ∈ A

/-
The big intersection of the empty set is the full set.
-/
theorem big_intersection_empty: BigIntersection (∅: Set (Set X)) = FullSet := by
  funext x
  simp [BigIntersection]
  constructor
  · intro _
    trivial
  · intro _ _ _
    contradiction

/-
The big intersection of the full set is the empty set.
-/
theorem big_intersection_full: BigIntersection (FullSet: Set (Set X)) = ∅ := by
  funext x
  simp [BigIntersection]
  constructor
  · intro h
    have := h ∅ trivial
    contradiction
  · intro h
    contradiction



-- Disjoint union

/-

TODO: The disjoint union of an indexed set of sets.

-/



-- Product

def Product (A: Set X) (B: Set Y): Set (Prod X Y) :=
  λ ⟨x, y⟩ ↦ x ∈ A ∧ y ∈ B
