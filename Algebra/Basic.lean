-- Algebra/Basic

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
  ∀ y, op e y = y

def RightIdentity (op: X → Y → X) (e: Y): Prop :=
  ∀ x, op x e = x

def Identity (op: Op X) (e: X): Prop :=
  LeftIdentity op e ∧ RightIdentity op e

def Associative (op: X → X → X): Prop :=
  ∀ x y z, op (op x y) z = op x (op y z)

def Commutative (op: X → X → Y): Prop :=
  ∀ a b, op a b = op b a

def DistributiveLeft (op₁ op₂: Op X): Prop :=
  ∀ a b c, op₁ a (op₂ b c) = op₂ (op₁ a b) (op₁ a c)

def DistributiveRight (op₁ op₂: Op X): Prop :=
  ∀ a b c, op₁ (op₂ a b) c = op₂ (op₁ a c) (op₁ b c)

def Distributive (op₁ op₂: Op X): Prop :=
  DistributiveLeft op₁ op₂ ∧ DistributiveRight op₁ op₂
