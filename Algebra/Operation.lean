-- Algebra.Operation

variable {X: Type u} {Y: Type v}

def Op (X: Type u): Type u :=
  X → X → X

def LeftIdentity (op: X → Y → Y) (e: X): Prop :=
  ∀ x, op e x = x

def RightIdentity (op: X → Y → X) (e: Y): Prop :=
  ∀ x, op x e = x

def Identity (op: Op X) (e: X): Prop :=
  LeftIdentity op e ∧ RightIdentity op e

def Associative (op: Op X): Prop :=
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
