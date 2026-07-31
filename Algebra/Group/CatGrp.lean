import Algebra.Category.Basic
import Algebra.Group.Hom

-- Help the sigma thing is making this really hard to read 

def Grp: Category := {
  Obj := Sigma (λ X ↦ Group X)
  Hom := λ ⟨_, G₁⟩ ⟨_, G₂⟩ ↦ Group.Hom G₁ G₂
  id := λ ⟨_, G⟩ ↦ Group.IdentityHom
  comp := by
    intro ⟨_, G₁⟩ ⟨_, G₂⟩ ⟨_, G₃⟩ g f
    exact Group.ComposeHom g f
  comp_assoc := sorry
  comp_id_left := sorry
  comp_id_right := sorry
}
