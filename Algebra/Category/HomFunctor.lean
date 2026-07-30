import Algebra.Category.Functor
import Algebra.Set.CatSet
import Algebra.Category.Constructions
namespace Category

def CovariantHomFunctor {X: Type u} (C: Category X) (A: X): Functor C CatSet := {
  objMap := λ Z: X ↦ C.Hom A Z
  homMap := λ f ↦ (λ g ↦ C.comp f g)
  id := by
    intro Z
    funext h
    calc
      C.comp (C.id Z) h
      _ = h := by rw [C.comp_id_left]
      _ = CatSet.id (C.Hom A Z) h := by rfl
  comp := by
    intro _ _ _ f g
    funext h
    calc
      C.comp (C.comp g f) h
      _ = C.comp g (C.comp f h) := by rw [C.comp_assoc]
      _ = (fun p => C.comp g p) (C.comp f h) := by rfl
      _ = (fun p => C.comp g p) ((fun q => C.comp f q) h) := by rfl
      _ = ((fun p => C.comp g p) ∘ (fun q => C.comp f q)) h := by rfl
      _ = (CatSet.comp (fun p => C.comp g p) (fun q => C.comp f q)) h := by rfl
}

def ContravariantHomFunctor {X: Type u} (C: Category X) (B: X): Functor (Op C) CatSet := {
  objMap := λ Z: X ↦ C.Hom Z B
  homMap := λ f ↦ (λ g ↦ C.comp g f)
  id := by
    intro Z
    funext h
    calc
      C.comp h (C.id Z)
      _ = h := by rw [C.comp_id_right]
      _ = CatSet.id (C.Hom Z B) h := by rfl
  comp := by
    intro _ _ _ f g
    funext h
    calc
      C.comp h (C.Op.comp g f)
      _ = C.comp h (C.comp f g) := by rfl
      _ = C.comp (C.comp h f) g := by rw [C.comp_assoc]
      _ = CatSet.comp (fun g_1 => C.comp g_1 g) (fun g => C.comp g f) h := by rfl
}

def ContravariantHomFunctor.v2 {X: Type u} (C: Category X) (B: X): Functor (Op C) CatSet :=
  CovariantHomFunctor C.Op B

/-
Hom Functor

For a given category C, construct a functor C_op × C → Set as follows:

Define the object map F: Obj(C_op) × Obj(C) → Set by
  (A₁, A₂) ↦ Hom(A₁, A₂)

For objects (A₁, A₂), (B₁, B₂), define the hom map F: Hom((A₁, A₂), (B₁, B₂)) → Hom_Set(Hom(A₁, A₂), Hom(B₁, B₂)) by
  (f₁, f₂) ↦ (λ g ↦ f₂ ∘ g ∘ f₁),
noting that f₁ has source B₁ and target A₁ because it comes from C_op.

(Proof) The obj map F and hom map F preserves identity:

Fix an object A = (A₁, A₂) ∈ Obj(C). WTS F(id_A) = id_(F(A)).

F(id_A) : Hom_C(A₁, A₂) → Hom_C(A₁, A₂)
id_(F(A)) : Hom_C(A₁, A₂) → Hom_C(A₁, A₂)

By definition, F(id_A) = F((id_A₁, id_A₂)) = (λ h ↦ id_A₂ ∘ h ∘ id_A₁ ), where h ∈ Hom_C(A₁, A₂).
Then by defn. of identity under composition we know F(id_A) = id_(Hom_C(A₁, A₂)).
And we know F(A) = F((A₁, A₂)) = Hom_C(A₁, A₂). So they are equal :)

(Proof) The obj map F and hom map F respects composition:

Fix objects (A₁, A₂), (B₁, B₂), (C₁, C₂) and morphisms (f₁, f₂): (A₁, A₂) → (B₁, B₂) and (g₁, g₂): (B₁, B₂) → (C₁, C₂).

So we have:
A₁ A₂ B₁ B₂ C₁ C₂ ∈ Obj(C)
f₁ ∈ Hom_C(B₁, A₁)
f₂ ∈ Hom_C(A₂, B₂)
g₁ ∈ Hom_C(C₁, B₁)
g₂ ∈ Hom_C(B₂, C₂)

(g₁, g₂) ∘ (f₁, f₂) = (f₁ ∘ g₁, g₂ ∘ f₂) ∈ (Hom_C(C₁, A₁), Hom_C(A₂, C₂)) = Hom_(C_op × C)((A₁, A₂), (C₁, C₂))

Let's look at where the hom map sends this composition:

F(f₁ ∘ g₁, g₂ ∘ f₂) = (λ h ↦ (g₂ ∘ f₂) ∘ h ∘ (f₁ ∘ g₁)), where h ∈ Hom_C(A₁, A₂).
(g₂ ∘ f₂) ∘ h ∘ (f₁ ∘ g₁) ∈ Hom_C(C₁, C₂).
Then F(f₁ ∘ g₁, g₂ ∘ f₂) ∈ Hom_C(A₁, A₂) → Hom_C(C₁, C₂)

Ok and look for the individual maps too:
F((f₁, f₂)) = (λ h ↦ f₂ ∘ h ∘ f₁)
F((g₁, g₂)) = (λ h ↦ g₂ ∘ h ∘ g₁)

And their composition

F((g₁, g₂)) ∘ F((f₁, f₂)) = (λ h ↦ g₂ ∘ h ∘ g₁) ∘ (λ h ↦ f₂ ∘ h ∘ f₁)

So WTS
(λ h ↦ (g₂ ∘ f₂) ∘ h ∘ (f₁ ∘ g₁)) = (λ h ↦ g₂ ∘ h ∘ g₁) ∘ (λ h ↦ f₂ ∘ h ∘ f₁)

These are morphisms in Set so let's use function extensionality. Let h ∈ Hom(A₁, A₂).

So WTS
(λ h ↦ (g₂ ∘ f₂) ∘ h ∘ (f₁ ∘ g₁))(h) = ((λ h ↦ g₂ ∘ h ∘ g₁) ∘ (λ h ↦ f₂ ∘ h ∘ f₁))(h)

(λ h ↦ (g₂ ∘ f₂) ∘ h ∘ (f₁ ∘ g₁))(h)
= (g₂ ∘ f₂) ∘ h ∘ (f₁ ∘ g₁))

Ok this is essentially just associativity

-/
def HomFunctor {X: Type u} (C: Category X): Functor (Prod C.Op C) CatSet := {
  objMap := λ (A₁, A₂) ↦ C.Hom A₁ A₂
  homMap := by
    intro (A₁, A₂) (B₁, B₂) (f₁, f₂)
    intro g
    exact C.comp f₂ (C.comp g f₁)
  id := by
    unfold Prod
    unfold Op
    simp_all
    intro A₁ A₂
    simp [C.comp_id_left, C.comp_id_right]
    rfl
  comp := by
    unfold Prod
    unfold Op
    simp_all
    intro A₁ A₂ B₁ B₂ C₁ C₂
    intro f₁ f₂ g₁ g₂
    funext h
    calc C.comp (C.comp g₂ f₂) (C.comp h (C.comp f₁ g₁))
    _ = C.comp g₂ (C.comp (C.comp f₂ (C.comp h f₁)) g₁) := by simp [C.comp_assoc]
    _ = (fun g => C.comp g₂ (C.comp g g₁)) (C.comp f₂ (C.comp h f₁)) := by rfl
    _ = (fun g => C.comp g₂ (C.comp g g₁)) ((fun g => C.comp f₂ (C.comp g f₁)) h) := by rfl
    _ = ((fun g => C.comp g₂ (C.comp g g₁)) ∘ (fun g => C.comp f₂ (C.comp g f₁))) h := by rfl
    _ = CatSet.comp (fun g => C.comp g₂ (C.comp g g₁)) (fun g => C.comp f₂ (C.comp g f₁)) h := by rfl
}
