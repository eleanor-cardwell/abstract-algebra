-- Algebra.Set.Relation

-- Relation properties

def Reflexive {X: Type u} (R: X → X → Prop): Prop :=
  ∀ a, R a a

def Irreflexive {X: Type u} (R: X → X → Prop): Prop :=
  ∀ a, ¬ R a a

def Symmetric {X: Type u} (R: X → X → Prop): Prop :=
  ∀ a b, R a b → R b a

def Antisymmetric {X: Type u} (R: X → X → Prop): Prop :=
  ∀ a b, R a b → R b a → a = b

def Transitive {X: Type u} (R: X → X → Prop): Prop :=
  ∀ a b c, R a b → R b c → R a c

def Total {X: Type u} (R: X → X → Prop): Prop :=
  ∀ a b, R a b ∨ R b a

-- Relation structure

class Relation (X₁: Type u₁) (X₂: Type u₂) where
  R: X₁ → X₂ → Prop

instance {X₁: Type u₁} {X₂: Type u₂}: CoeFun (Relation X₁ X₂) (λ _ ↦ X₁ → X₂ → Prop) := ⟨λ R ↦ R.R⟩
  
-- Order

class Preorder (X: Type u) extends Relation X X where
  reflexive: Reflexive toRelation
  transitive: Transitive toRelation

class PartialOrder (X: Type u) extends Preorder X where
  antisymmetric: Antisymmetric toRelation

-- Equivalence relation

structure EquivalenceRelation (X: Type u) extends Relation X X where
  reflexive: Reflexive toRelation
  symmetric: Symmetric toRelation
  transitive: Transitive toRelation
