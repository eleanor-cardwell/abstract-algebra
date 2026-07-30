-- Algebra.Category.Basic

import Algebra.Logic

/-
A category C consists of:
- a class Obj(C) of objects of the category; and
- for any objects A, B ∈ Obj(C), a class of morphisms Hom(A, B)
Satisfying the following:
- there is composition of morphisms; and
- composition of morphisms is associative; and
- for any object A ∈ Obj(C), there exists an identity morphism 1_A ∈ Hom(A, A)
-/

structure Category where
  Obj: Type u₁
  Hom: Obj → Obj → Type u₂
  id (A: Obj): Hom A A
  comp {A B C: Obj} (g: Hom B C) (f: Hom A B): Hom A C
  comp_assoc {A B C D: Obj} (f: Hom A B) (g: Hom B C) (h: Hom C D): comp h (comp g f) = comp (comp h g) f
  comp_id_left {A B: Obj} (f: Hom A B): comp (id B) f = f
  comp_id_right {A B: Obj} (f: Hom A B): comp f (id A) = f

instance: CoeSort (Category.{u₁, u₂}) (Type u₁) where
  coe C := C.Obj

namespace Category

abbrev compLeft {C: Category} {A B D: C} (g: C.Hom B D) (f: C.Hom A B): C.Hom A D :=
  C.comp g f

abbrev compRight {C: Category} {A B D: C} (f: C.Hom A B) (g: C.Hom B D): C.Hom A D :=
  C.comp g f

infixr:81 " ≪ " => compLeft
infixr:81 " ≫ " => compRight

def LeftInverse {C: Category} {A B: C} (f: C.Hom A B) (g: C.Hom B A): Prop :=
  g ≪ f = C.id A

def RightInverse {C: Category} {A B: C} (f: C.Hom A B) (g: C.Hom B A): Prop :=
  f ≪ g = C.id B

def Inverses {C: Category} {A B: C} (f: C.Hom A B) (g: C.Hom B A): Prop :=
  LeftInverse f g ∧ RightInverse f g

/-
A morphism is an isomorphism if it has a two-sided inverse under composition.
-/
def Isomorphism {C: Category} {A B: C} (f: C.Hom A B): Prop :=
  ∃ g: C.Hom B A, Inverses f g

def Isomorphic (C: Category) (A B: C): Prop :=
  ∃ f: C.Hom A B, Isomorphism f

theorem inverse_unique {C: Category} {A B: C} (f: C.Hom A B): ∀ g₁ g₂: C.Hom B A, Inverses f g₁ → Inverses f g₂ → g₁ = g₂ := by
  intro g₁ g₂ hg₁ hg₂
  calc g₁
  _ = g₁ ≪ C.id B   := by rw [compLeft, C.comp_id_right]
  _ = g₁ ≪ (f ≪ g₂) := by rw [hg₂.right]
  _ = (g₁ ≪ f) ≪ g₂ := by simp only [compLeft, C.comp_assoc]
  _ = C.id A ≪ g₂   := by rw [hg₁.left]
  _ = g₂             := by rw [compLeft, C.comp_id_left]

theorem identity_inverse_self (C: Category) (A: C): Inverses (C.id A) (C.id A) := by
  constructor
  · unfold LeftInverse
    rw [compLeft, C.comp_id_left (C.id A)]
  · unfold RightInverse
    rw [compLeft, C.comp_id_right (C.id A)]

theorem identity_isomorphism (C: Category) (A: C): Isomorphism (C.id A) := by
  exists C.id A
  exact identity_inverse_self C A

/-
A morphism is monic if it is left cancellable under composition.
-/
def Monomorphism {C: Category} {A B: C} (f: C.Hom A B): Prop :=
  ∀ Z: C, ∀ g₁ g₂: C.Hom Z A, f ≪ g₁ = f ≪ g₂ → g₁ = g₂

/-
A morphism is epic if it is right cancellable under composition.
-/
def Epimorphism {C: Category} {A B: C} (f: C.Hom A B): Prop :=
  ∀ Z: C, ∀ g₁ g₂: C.Hom B Z, g₁ ≪ f = g₂ ≪ f → g₁ = g₂

theorem epic_if_right_inverse {C: Category} {A B: C} {f: C.Hom A B} (h: ∃ g: C.Hom B A, RightInverse f g): Epimorphism f := by
  have ⟨g, hg⟩ := h
  intro Z g₁ g₂ hg₁
  calc g₁
  _ = g₁ ≪ C.id B   := by rw [compLeft, C.comp_id_right]
  _ = g₁ ≪ (f ≪ g)  := by rw [hg]
  _ = (g₁ ≪ f) ≪ g  := by simp only [compLeft, C.comp_assoc]
  _ = (g₂ ≪ f) ≪ g  := by rw [hg₁]
  _ = g₂ ≪ (f ≪ g)  := by simp only [compLeft, C.comp_assoc]
  _ = g₂ ≪ C.id B   := by rw [hg]
  _ = g₂             := by rw [compLeft, C.comp_id_right]

/-
An object I ∈ Obj(C) is initial if for every object A ∈ Obj(C), there exists exactly one morphism
in Hom(I, A)
-/
def Initial (C: Category) (I: C): Prop :=
  ∀ A: C, ∃ f: C.Hom I A, ∀ g: C.Hom I A, f = g

theorem initial_objects_isomorphic {C: Category} {I₁ I₂: C} (h₁: Initial C I₁) (h₂: Initial C I₂): Isomorphic C I₁ I₂ := by
  have ⟨f₁, hf₁⟩ := h₁ I₂
  have ⟨f₂, hf₂⟩ := h₂ I₁
  exists f₁
  exists f₂
  -- Simplify?
  constructor
  · let f₂f₁: C.Hom I₁ I₁ := f₂ ≪ f₁
    have ⟨fI₁, hfI₁⟩ := h₁ I₁
    have h₃: fI₁ = f₂f₁ := by rw [hfI₁ f₂f₁]
    have h₄: fI₁ = C.id I₁ := by rw [hfI₁ (C.id I₁)]
    have h₅: f₂f₁ = C.id I₁ := by rw [←h₃, ←h₄]
    unfold LeftInverse
    unfold f₂f₁ at h₅
    exact h₅
  · let f₁f₂: C.Hom I₂ I₂ := f₁ ≪ f₂
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
def Final (C: Category) (F: C): Prop :=
  ∀ A: C, ∃ f: C.Hom A F, ∀ g: C.Hom A F, f = g

theorem final_objects_isomorphic {C: Category} {F₁ F₂: C} (h₁: Final C F₁) (h₂: Final C F₂): Isomorphic C F₁ F₂ := by
  sorry

/-
Product
-/
def IsProduct (C: Category) (A B AB: C): Prop :=
  ∃ πA: C.Hom AB A, ∃ πB: C.Hom AB B, ∀ Z: C, ∀ fA: C.Hom Z A, ∀ fB: C.Hom Z B, ExistsUnique (λ σ: C.Hom Z AB ↦ πA ≪ σ = fA ∧ πB ≪ σ = fB)

def PairHasProduct (C: Category) (A B: C): Prop :=
  ∃ AB: C, IsProduct C A B AB

def HasProduct (C: Category): Prop :=
  ∀ A B: C, PairHasProduct C A B
