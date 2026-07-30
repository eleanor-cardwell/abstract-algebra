-- Algebra.Category.Groupoid

import Algebra.Category.Basic

structure Groupoid (X: Type u₁) extends Category X where
  iso {A B: X} (f: Hom A B): Category.Isomorphism f
