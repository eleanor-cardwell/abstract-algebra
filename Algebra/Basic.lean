variable {X: Type u₁} {Y: Type u₂} {Z: Type u₃}

/-

Logic

-/

theorem contrapose {P Q: Prop}: (¬Q → ¬P) → (P → Q) := by
  intro h hP
  by_cases hQ: Q
  · exact hQ
  · have := h hQ
    contradiction

theorem contrapose_iff {P Q: Prop}: (¬Q ↔ ¬P) → (P ↔ Q) := by
  intro ⟨h1, h2⟩
  constructor
  · apply contrapose
    exact h1
  · apply contrapose
    exact h2

def ExistsUnique (P: X → Prop): Prop :=
  (∃ x, P x) ∧ (∀ x y, P x ∧ P y → x = y)



/-

Operations

-/

def Op (X: Type u₁): Type u₁ :=
  X → X → X

def LeftIdentity (op: X → Y → Y) (e: X): Prop :=
  ∀ x, op e x = x

def RightIdentity (op: X → Y → X) (e: Y): Prop :=
  ∀ x, op x e = x

def Identity (op: Op X) (e: X): Prop :=
  LeftIdentity op e ∧ RightIdentity op e

def Associative (op: X → X → X): Prop :=
  ∀ x y z, op (op x y) z = op x (op y z)

def Commutative (op: X → X → Y): Prop :=
  ∀ a b, op a b = op b a

def Inverses (op: Op X) (a b e: X): Prop :=
  op a b = e ∧ op b a = e

def LeftInverse (op: Op X) (inv: X → X) (e: X): Prop :=
  ∀ a, op (inv a) a = e

def RightInverse (op: Op X) (inv: X → X) (e: X): Prop :=
  ∀ a, op a (inv a) = e

def Inverse (op: Op X) (inv: X → X) (e: X): Prop :=
  LeftInverse op inv e ∧ RightInverse op inv e

def DistributiveLeft (op₁ op₂: Op X): Prop :=
  ∀ a b c, op₁ a (op₂ b c) = op₂ (op₁ a b) (op₁ a c)

def DistributiveRight (op₁ op₂: Op X): Prop :=
  ∀ a b c, op₁ (op₂ a b) c = op₂ (op₁ a c) (op₁ b c)

def Distributive (op₁ op₂: Op X): Prop :=
  DistributiveLeft op₁ op₂ ∧ DistributiveRight op₁ op₂

def AbsorbsLeft (op: Op X) (z: X): Prop :=
  ∀ a, op z a = z

def AbsorbsRight (op: Op X) (z: X): Prop :=
  ∀ a, op a z = z

def Absorbs (op: Op X) (z: X): Prop :=
  AbsorbsLeft op z ∧ AbsorbsRight op z



/-

Sets

-/

def Set (X: Type u₁): Type u₁ :=
  X → Prop

instance (X: Type u₁): CoeSort (Set X) (Type u₁) := ⟨Subtype⟩

def Mem (A: Set X) (x: X): Prop :=
  A x

instance: Membership X (Set X) := ⟨Mem⟩

def Subset (A B: Set X): Prop :=
  ∀ x, x ∈ A → x ∈ B

instance: HasSubset (Set X) := ⟨Subset⟩

theorem subset_self (A: Set X): A ⊆ A := by
  intro _ h
  exact h



/-

Empty set

-/

def EmptySet {X: Type u₁}: Set X :=
  λ _ ↦ False

instance: EmptyCollection (Set X) := ⟨EmptySet⟩

theorem empty_subset (A: Set X): ∅ ⊆ A := by
  exact λ _ ↦ False.elim



/-

Full set

-/

def FullSet {X: Type u₁}: Set X :=
  λ _ ↦ True

theorem subset_full (A: Set X): A ⊆ FullSet := by
  exact λ _ _ ↦ trivial



/-

Union

-/

def union (A B: Set X): Set X :=
  λ x ↦ x ∈ A ∨ x ∈ B

instance: Union (Set X) := {
  union := union
}

theorem union_left {A B: Set X} {a: X} (h: a ∈ A): a ∈ A ∪ B := by
  apply Or.inl
  exact h

theorem union_right {A B: Set X} {a: X} (h: a ∈ B): a ∈ A ∪ B := by
  apply Or.inr
  exact h

theorem union_left_identity: LeftIdentity union (@EmptySet X) := by
  intro
  funext
  simp [union]
  exact or_iff_right id

theorem union_right_identity: RightIdentity union (@EmptySet X) := by
  intro
  funext
  simp [union]
  exact or_iff_left id

theorem union_identity: Identity union (@EmptySet X) := by
  exact ⟨union_left_identity, union_right_identity⟩

theorem union_assoc: Associative (@union X) := by
  intro _ _ _
  funext
  simp [union]
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

theorem union_comm: Commutative (@union X) := by
  intro A B
  funext x
  simp [union]
  exact Or.comm



/-

Intersection

-/

def inter (A B: Set X): Set X :=
  λ x ↦ x ∈ A ∧ x ∈ B

instance: Inter (Set X) := ⟨inter⟩

theorem inter_left {A B: Set X} {a: X} (h: a ∈ A ∩ B): a ∈ A := by
  exact h.left

theorem inter_right {A B: Set X} {a: X} (h: a ∈ A ∩ B): a ∈ B := by
  exact h.right

theorem inter_identity: Identity inter (@FullSet X) := by
  constructor
  · intro
    funext
    simp [inter]
    constructor
    · intro h; exact h.right
    · intro h; exact ⟨trivial, h⟩
  · intro
    funext
    simp [inter]
    constructor
    · intro h; exact h.left
    · intro h; exact ⟨h, trivial⟩

theorem inter_assoc: Associative (@inter X) := by
  intro _ _ _
  funext
  simp [inter]
  apply and_assoc

theorem inter_comm: Commutative (@inter X) := by
  intro A B
  funext x
  simp [inter]
  constructor <;> (intro h; exact And.symm h;)



/-

Compliment & nonempty

-/

def Compliment (A: Set X): Set X :=
  λ x ↦ x ∉ A

def nonempty (S: Set X): Prop :=
  ∃ a, a ∈ S

theorem nonempty_iff {S: Set X}: nonempty S ↔ S ≠ ∅ := by
  constructor
  · intro ⟨a, ha⟩
    intro h
    have: a ∉ S := by exact of_eq_false (congrFun h a)
    contradiction
  · apply contrapose
    simp [nonempty]
    intro h
    funext _
    simp
    constructor
    · intro h'
      exact h _ h'
    · intro h'
      exact False.elim h'

theorem not_nonempty_iff {S: Set X}: ¬(nonempty S) ↔ S = ∅ := by
  apply contrapose_iff
  simp
  exact Iff.symm nonempty_iff



/-

Image, preimage, and range

-/

def Image (f: X → Y) (A: Set X): Set Y :=
  λ b ↦ ∃ a ∈ A, f a = b

def Preimage (f: X → Y) (B: Set Y): Set X :=
  λ a ↦ f a ∈ B

def Range (f: X → Y): Set Y :=
  λ b ↦ ∃ a, f a = b

theorem range_mem (f: X → Y) (a: X): f a ∈ Range f := by
  exists a



/-

Singleton

-/

def SingletonSet {X: Type u₁} (a: X): Set X :=
  λ x ↦ x = a



/-

sUnion: The union of a set of subsets

-/

def sUnion (S: Set (Set X)): Set X :=
  λ a ↦ ∃ A ∈ S, a ∈ A

theorem sUnion_empty: sUnion (∅: Set (Set X)) = ∅ := by
  funext x
  simp [sUnion]
  constructor
  · intro ⟨_, _, _⟩
    contradiction
  · intro _
    contradiction

theorem sUnion_full: sUnion (FullSet: (Set (Set X))) = FullSet := by
  sorry



/-

sInter: The intersection of a set of subsets.

-/

def sInter (S: Set (Set X)): Set X :=
  λ a ↦ ∀ A ∈ S, a ∈ A

theorem sInter_empty: sInter (∅: Set (Set X)) = FullSet := by
  funext x
  simp [sInter]
  constructor
  · intro _
    trivial
  · intro _ _ _
    contradiction

theorem sInter_full: sInter (FullSet: Set (Set X)) = ∅ := by
  funext x
  simp [sInter]
  constructor
  · intro h
    have := h ∅ trivial
    contradiction
  · intro h
    contradiction



/-

Functions

-/

def Injective (f: X → Y): Prop :=
  ∀ x₁ x₂, f x₁ = f x₂ → x₁ = x₂

def Surjective (f: X → Y): Prop :=
  ∀ y, ∃ x, f x = y

def Bijective (f: X → Y): Prop :=
  Injective f ∧ Surjective f



/-

Finite, countable

-/

def Finite (S: Set X): Prop :=
  ∃ n, ∃ f: (S → Fin n), Bijective f

theorem empty_finite: Finite (∅: Set X) := by
  exists 0
  exists (λ x ↦ nomatch x)
  constructor
  · intro x₁ x₂ h
    nomatch x₁
  · intro y
    nomatch y

def Countable (S: Set X): Prop :=
  ∃ f: Nat → S, Bijective f
