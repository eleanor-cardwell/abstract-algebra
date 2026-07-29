import Algebra.Basic

/-
A category C consists of:
- a class Obj(C) of objects of the category; and
- for any objects A, B ∈ Obj(C), a class of morphisms Hom(A, B)
Satisfying the following:
- there is composition of morphisms; and
- composition of morphisms is associative; and
- for any object A ∈ Obj(C), there exists an identity morphism 1_A ∈ Hom(A, A)
-/
structure Category (Obj: Type u₁) where
  Hom: Obj → Obj → Type u₂
  id (A: Obj): Hom A A
  comp {A B C: Obj} (g: Hom B C) (f: Hom A B): Hom A C
  comp_assoc {A B C D: Obj} (f: Hom A B) (g: Hom B C) (h: Hom C D): comp h (comp g f) = comp (comp h g) f
  comp_id_left {A B: Obj} (f: Hom A B): comp (id B) f = f
  comp_id_right {A B: Obj} (f: Hom A B): comp f (id A) = f

namespace Category
variable {X: Type u₁}

/-
Given a category C, we can form its opposite category C^op.
-/
def Op (C: Category X): Category X := {
  Hom := λ A B ↦ C.Hom B A
  id := λ A ↦ C.id A
  comp := λ g f ↦ C.comp f g
  comp_assoc := by
    intro _ _ _ _ f g h
    exact Eq.symm (C.comp_assoc h g f)
  comp_id_left := by
    intro A B f
    exact C.comp_id_right f
  comp_id_right := by
    intro A B F
    exact C.comp_id_left F
}

def LeftInverse {C: Category X} {A B: X} (f: C.Hom A B) (g: C.Hom B A): Prop :=
  C.comp g f = C.id A

def RightInverse {C: Category X} {A B: X} (f: C.Hom A B) (g: C.Hom B A): Prop :=
  C.comp f g = C.id B

def Inverses {C: Category X} {A B: X} (f: C.Hom A B) (g: C.Hom B A): Prop :=
  LeftInverse f g ∧ RightInverse f g

/-
A morphism is an isomorphism if it has a two-sided inverse under composition.
-/
def Isomorphism {C: Category X} {A B: X} (f: C.Hom A B): Prop :=
  ∃ g: C.Hom B A, Inverses f g

def Isomorphic (C: Category X) (A B: X): Prop :=
  ∃ f: C.Hom A B, Isomorphism f

theorem inverse_unique {C: Category X} {A B: X} (f: C.Hom A B): ∀ g₁ g₂: C.Hom B A, Inverses f g₁ → Inverses f g₂ → g₁ = g₂ := by
  intro g₁ g₂ hg₁ hg₂
  calc g₁
  _ = C.comp g₁ (C.id B)      := by rw [C.comp_id_right]
  _ = C.comp g₁ (C.comp f g₂) := by rw [hg₂.right]
  _ = C.comp (C.comp g₁ f) g₂ := by rw [C.comp_assoc]
  _ = C.comp (C.id A) g₂      := by rw [hg₁.left]
  _ = g₂                      := by rw [C.comp_id_left]

theorem identity_inverse_self (C: Category X) (A: X): Inverses (C.id A) (C.id A) := by
  constructor
  · unfold LeftInverse
    rw [C.comp_id_left (C.id A)]
  · unfold RightInverse
    rw [C.comp_id_right (C.id A)]

theorem identity_isomorphism (C: Category X) (A: X): Isomorphism (C.id A) := by
  exists C.id A
  exact identity_inverse_self C A

/-
A morphism is monic if it is left cancellable under composition.
-/
def Monomorphism {C: Category X} {A B: X} (f: C.Hom A B): Prop :=
  ∀ Z: X, ∀ g₁ g₂: C.Hom Z A, C.comp f g₁ = C.comp f g₂ → g₁ = g₂

/-
A morphism is epic if it is right cancellable under composition.
-/
def Epimorphism {C: Category X} {A B: X} (f: C.Hom A B): Prop :=
  ∀ Z: X, ∀ g₁ g₂: C.Hom B Z, C.comp g₁ f = C.comp g₂ f → g₁ = g₂

theorem epic_if_right_inverse {C: Category X} {A B: X} {f: C.Hom A B} (h: ∃ g: C.Hom B A, RightInverse f g): Epimorphism f := by
  have ⟨g, hg⟩ := h
  intro Z g₁ g₂ hg₁
  calc g₁
  _ = C.comp g₁ (C.id B)     := by rw [C.comp_id_right]
  _ = C.comp g₁ (C.comp f g) := by rw [hg]
  _ = C.comp (C.comp g₁ f) g := by rw [C.comp_assoc]
  _ = C.comp (C.comp g₂ f) g := by rw [hg₁]
  _ = C.comp g₂ (C.comp f g) := by rw [C.comp_assoc]
  _ = C.comp g₂ (C.id B)     := by rw [hg]
  _ = g₂                     := by rw [C.comp_id_right]

/-
An object I ∈ Obj(C) is initial if for every object A ∈ Obj(C), there exists exactly one morphism
in Hom(I, A)
-/
def Initial (C: Category X) (I: X): Prop :=
  ∀ A: X, ∃ f: C.Hom I A, ∀ g: C.Hom I A, f = g

theorem initial_objects_isomorphic {C: Category X} {I₁ I₂: X} (h₁: Initial C I₁) (h₂: Initial C I₂): Isomorphic C I₁ I₂ := by
  have ⟨f₁, hf₁⟩ := h₁ I₂
  have ⟨f₂, hf₂⟩ := h₂ I₁
  exists f₁
  exists f₂
  -- Simplify?
  constructor
  · let f₂f₁: C.Hom I₁ I₁ := C.comp f₂ f₁
    have ⟨fI₁, hfI₁⟩ := h₁ I₁
    have h₃: fI₁ = f₂f₁ := by rw [hfI₁ f₂f₁]
    have h₄: fI₁ = C.id I₁ := by rw [hfI₁ (C.id I₁)]
    have h₅: f₂f₁ = C.id I₁ := by rw [←h₃, ←h₄]
    unfold LeftInverse
    unfold f₂f₁ at h₅
    exact h₅
  · let f₁f₂: C.Hom I₂ I₂ := C.comp f₁ f₂
    have ⟨fI₂, hfI₂⟩ := h₂ I₂
    have h₃: fI₂ = f₁f₂ := by rw [hfI₂ f₁f₂]
    have h₄: fI₂ = C.id I₂ := by rw [hfI₂ (C.id I₂)]
    have h₅: f₁f₂ = C.id I₂ := by rw [←h₃, ←h₄]
    unfold RightInverse
    unfold f₁f₂ at h₅
    exact h₅

/-
An object F ∈ Obj(C) is final if for every object A ∈ Obj(C), there exists exactly one morphism
in Hom(A, F)
-/
def Final (C: Category X) (F: X): Prop :=
  ∀ A: X, ∃ f: C.Hom A F, ∀ g: C.Hom A F, f = g

/-
Product and coproduct (simple)
-/

def HasProduct (C: Category X): Prop :=
  ∀ A B: X, ∃ AB: X, ∃ πA: C.Hom AB A, ∃ πB: C.Hom AB B, ∀ Z: X, ∀ fA: C.Hom Z A, ∀ fB: C.Hom Z B, ExistsUnique (λ σ: C.Hom Z AB ↦ C.comp πA σ = fA ∧ C.comp πB σ = fB)

def HasCoproduct (C: Category X): Prop :=
  ∀ A B: X, ∃ AB: X, ∃ iA: C.Hom A AB, ∃ iB: C.Hom B AB, ∀ Z: X, ∀ fA: C.Hom A Z, ∀ fB: C.Hom B Z, ExistsUnique (λ σ: C.Hom AB Z ↦ C.comp σ iA = fA ∧ C.comp σ iB = fB)
