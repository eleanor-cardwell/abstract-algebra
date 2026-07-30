-- Algebra.Set.Basic

import Algebra.Operation
import Algebra.Logic

variable {X: Type u₁} {Y: Type u₂} {Z: Type u₃}

-- Set

def Set (X: Type u₁): Type u₁ :=
  X → Prop

instance (X: Type u₁): CoeSort (Set X) (Type u₁) := ⟨Subtype⟩

namespace Set

-- Membership

def Mem (A: Set X) (a: X): Prop :=
  A a

instance: Membership X (Set X) := ⟨Mem⟩

-- Subset

def Subset (A B: Set X): Prop :=
  ∀ x, A x → B x

instance: HasSubset (Set X) := ⟨Subset⟩

-- Empty set

def Empty: Set X :=
  λ _ ↦ False

instance: EmptyCollection (Set X) := ⟨Empty⟩

theorem empty_subset (A: Set X): ∅ ⊆ A := by
  exact λ _ ↦ False.elim
  
-- Full set

def Full: Set X :=
  λ _ ↦ True

theorem subset_full (A: Set X): A ⊆ Full := by
  exact λ _ _ ↦ trivial
  
-- Intersection

def Intersection (A B: Set X): Set X :=
  λ x ↦ x ∈ A ∧ x ∈ B

instance: Inter (Set X) := ⟨Intersection⟩

theorem inter_left {A B: Set X} {a: X} (h: a ∈ A ∩ B): a ∈ A := by
  exact h.left

theorem inter_right {A B: Set X} {a: X} (h: a ∈ A ∩ B): a ∈ B := by
  exact h.right

theorem inter_identity: Identity Intersection (@Full X) := by
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

theorem inter_assoc: Associative (@Intersection X) := by
  intro _ _ _
  funext
  simp [Intersection]
  apply Iff.symm
  apply And.associative

theorem inter_comm: Commutative (@Intersection X) := by
  intro A B
  funext x
  simp [Intersection]
  constructor <;> (intro h; exact And.symm h;)
  
-- Union

def Union (A B: Set X): Set X :=
  λ x ↦ x ∈ A ∨ x ∈ B

instance: _root_.Union (Set X) := ⟨Union⟩

theorem union_left {A B: Set X} {a: X} (h: a ∈ A): a ∈ A ∪ B := by
  apply Or.inl
  exact h

theorem union_right {A B: Set X} {a: X} (h: a ∈ B): a ∈ A ∪ B := by
  apply Or.inr
  exact h

theorem union_left_identity: LeftIdentity Union (@Empty X) := by
  intro
  funext
  simp [Union]
  exact or_iff_right id

theorem union_right_identity: RightIdentity Union (@Empty X) := by
  intro
  funext
  simp [Union]
  exact or_iff_left id

theorem union_identity: Identity Union (@Empty X) := by
  exact ⟨union_left_identity, union_right_identity⟩

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

theorem union_comm: Commutative (@Union X) := by
  intro A B
  funext x
  simp [Union]
  exact Or.comm
  
-- Complement

def Complement (A: Set X): Set X :=
  λ x ↦ x ∉ A
  
-- Nonempty

def Nonempty (S: Set X): Prop :=
  ∃ a, a ∈ S

theorem nonempty_iff {S: Set X}: S.Nonempty ↔ S ≠ ∅ := by
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

theorem not_nonempty_iff {S: Set X}: ¬S.Nonempty ↔ S = ∅ := by
  apply contrapose_iff
  simp
  exact Iff.symm nonempty_iff

theorem complement_empty_iff {S: Set X}: S.Complement = ∅ ↔ S = Full := by
  constructor
  · intro h
    funext x
    simp
    constructor
    · intro
      trivial
    · intro _
      by_cases hx: x ∈ S
      · exact hx
      · have: x ∈ S.Complement := by exact hx
        simp_all
        contradiction
  · intro h
    funext x
    simp
    constructor
    · intro h'
      by_cases hx: x ∈ S
      · contradiction
      · rw [h] at hx
        have: x ∈ Full := by trivial
        contradiction
    · intro h'
      contradiction
