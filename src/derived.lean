
import category_theory.abelian.basic
import algebra.homology.homotopy_category
import category_theory.morphism_property

import verdier

open category_theory
noncomputable theory

namespace category_theory

namespace derived

universe u

variables {A : Type u} [small_category A] [abelian A]

def c := complex_shape.up ℤ

class homotopy_quasi_iso {X Y : homotopy_category A c} (f : X ⟶ Y):= 
  (i : A → A)

end derived

end category_theory