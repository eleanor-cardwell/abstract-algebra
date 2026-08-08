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

class Category (C: Type u) where
  Hom: C → C → Type v
  id (X: C): Hom X X
  comp {X Y Z: C} (g: Hom Y Z) (f: Hom X Y): Hom X Z
  comp_assoc {X Y Z W: C} (f: Hom X Y) (g: Hom Y Z) (h: Hom Z W): comp h (comp g f) = comp (comp h g) f
  comp_id_left {X Y: C} (f: Hom X Y): comp (id Y) f = f
  comp_id_right {X Y: C} (f: Hom X Y): comp f (id X) = f

namespace Category

infixr:81 " ≪ " => comp
infixr:81 " ≫ " => λ f g ↦ comp g f

def LeftInverse {C: Type u} [Category C] {X Y: C}
    (f: Hom X Y) (g: Hom Y X): Prop :=
  g ≪ f = id X

def RightInverse {C: Type u} [Category C] {X Y: C}
    (f: Hom X Y) (g: Hom Y X): Prop :=
  f ≪ g = id Y

def Inverses {C: Type u} [Category C] {X Y: C}
    (f: Hom X Y) (g: Hom Y X): Prop :=
  LeftInverse f g ∧ RightInverse f g

/-
A morphism is an isomorphism if it has a two-sided inverse under composition.
-/
def Isomorphism {C: Type u} [Category C] {X Y: C}
    (f: Hom X Y): Prop :=
  ∃ g: Hom Y X, Inverses f g

def Isomorphic {C: Type u} [Category C] (X Y: C): Prop :=
  ∃ f: Hom X Y, Isomorphism f

theorem inverse_unique {C: Type u} [Category C] {X Y: C}
    (f: Hom X Y): ∀ g₁ g₂: Hom Y X, Inverses f g₁ → Inverses f g₂ → g₁ = g₂ := by
  intro g₁ g₂ hg₁ hg₂
  calc g₁
  _ = g₁ ≪ id Y     := by rw [comp_id_right]
  _ = g₁ ≪ (f ≪ g₂) := by rw [hg₂.right]
  _ = (g₁ ≪ f) ≪ g₂ := by simp only [comp_assoc]
  _ = id X ≪ g₂     := by rw [hg₁.left]
  _ = g₂             := by rw [comp_id_left]

theorem identity_inverse_self {C: Type u} [Category C] (X: C): Inverses (id X) (id X) := by
  constructor
  · unfold LeftInverse
    rw [comp_id_left (id X)]
  · unfold RightInverse
    rw [comp_id_right (id X)]

theorem identity_isomorphism {C: Type u} [Category C] (X: C): Isomorphism (id X) := by
  exists id X
  exact identity_inverse_self X

/-
A morphism is monic if it is left cancellable under composition.
-/
def Monomorphism {C: Type u} [Category C] {X Y: C} (f: Hom X Y): Prop :=
  ∀ Z: C, ∀ g₁ g₂: Hom Z X, f ≪ g₁ = f ≪ g₂ → g₁ = g₂

/-
A morphism is epic if it is right cancellable under composition.
-/
def Epimorphism {C: Type u} [Category C] {X Y: C} (f: Hom X Y): Prop :=
  ∀ Z: C, ∀ g₁ g₂: Hom Y Z, g₁ ≪ f = g₂ ≪ f → g₁ = g₂

theorem epic_if_right_inverse {C: Type u} [Category C] {X Y: C}
    {f: Hom X Y} (h: ∃ g: Hom Y X, RightInverse f g): Epimorphism f := by
  have ⟨g, hg⟩ := h
  intro Z g₁ g₂ hg₁
  calc g₁
  _ = g₁ ≪ id Y    := by rw [comp_id_right]
  _ = g₁ ≪ (f ≪ g) := by rw [hg]
  _ = (g₁ ≪ f) ≪ g := by simp only [comp_assoc]
  _ = (g₂ ≪ f) ≪ g := by rw [hg₁]
  _ = g₂ ≪ (f ≪ g) := by simp only [comp_assoc]
  _ = g₂ ≪ id Y    := by rw [hg]
  _ = g₂            := by rw [comp_id_right]

/-
An object I ∈ Obj(C) is initial if for every object A ∈ Obj(C), there exists exactly one morphism
in Hom(I, A)
-/
def Initial {C: Type u} [Category C] (I: C): Prop :=
  ∀ X: C, ∃ f: Hom I X, ∀ g: Hom I X, f = g

theorem initial_objects_isomorphic {C: Type u} [Category C] {I₁ I₂: C}
    (h₁: Initial I₁) (h₂: Initial I₂): Isomorphic I₁ I₂ := by
  have ⟨f₁, hf₁⟩ := h₁ I₂
  have ⟨f₂, hf₂⟩ := h₂ I₁
  exists f₁
  exists f₂
  -- Simplify?
  constructor
  · let f₂f₁: Hom I₁ I₁ := f₂ ≪ f₁
    have ⟨fI₁, hfI₁⟩ := h₁ I₁
    have h₃: fI₁ = f₂f₁ := by rw [hfI₁ f₂f₁]
    have h₄: fI₁ = id I₁ := by rw [hfI₁ (id I₁)]
    have h₅: f₂f₁ = id I₁ := by rw [←h₃, ←h₄]
    unfold LeftInverse
    unfold f₂f₁ at h₅
    exact h₅
  · let f₁f₂: Hom I₂ I₂ := f₁ ≪ f₂
    have ⟨fI₂, hfI₂⟩ := h₂ I₂
    have h₃: fI₂ = f₁f₂ := by rw [hfI₂ f₁f₂]
    have h₄: fI₂ = id I₂ := by rw [hfI₂ (id I₂)]
    have h₅: f₁f₂ = id I₂ := by rw [←h₃, ←h₄]
    unfold RightInverse
    unfold f₁f₂ at h₅
    exact h₅

/-
An object F ∈ Obj(C) is final if for every object A ∈ Obj(C), there exists exactly one morphism
in Hom(A, F)
-/
def Final {C: Type u} [Category C] (F: C): Prop :=
  ∀ X: C, ∃ f: Hom X F, ∀ g: Hom X F, f = g

theorem final_objects_isomorphic {C: Type u} [Category C] {F₁ F₂: C}
    (h₁: Final F₁) (h₂: Final F₂): Isomorphic F₁ F₂ := by
  sorry

/-
Product
-/
def IsProduct {C: Type u} [Category C] (X Y XY: C): Prop :=
  ∃ πX: Hom XY X, ∃ πY: Hom XY Y, ∀ Z: C, ∀ fX: Hom Z X, ∀ fY: Hom Z Y,
    ExistsUnique (λ σ: Hom Z XY ↦ πX ≪ σ = fX ∧ πY ≪ σ = fY)

def PairHasProduct {C: Type u} [Category C] (X Y: C): Prop :=
  ∃ XY: C, IsProduct X Y XY

def HasProduct (C: Type u) [Category C]: Prop :=
  ∀ X Y: C, PairHasProduct X Y
