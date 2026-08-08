-- Algebra.Category.Groupoid

import Algebra.Category.Basic

class Groupoid (C: Type u) extends Category C where
  iso {X Y: C} (f: @Category.Hom C toCategory X Y):
    @Category.Isomorphism C toCategory X Y f
