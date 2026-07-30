-- Algebra.Category.Groupoid

import Algebra.Category.Basic

structure Groupoid extends Category where
  iso {A B: Obj} (f: Hom A B): Category.Isomorphism f
