
import category_theory.abelian.basic
import algebra.homology.homotopy_category
import category_theory.morphism_property

import verdier

open category_theory
noncomputable theory

namespace category_theory

namespace derived

universe u

variables (A : Type u) [small_category A] [abelian A]

def c := complex_shape.up ℤ

class h_quasi_iso {X Y : homotopy_category A c} (f : X ⟶ Y) : Prop := 
  (is_iso : ∀ i, is_iso ((homotopy_category.homology_functor A c i).map f))

attribute [instance] h_quasi_iso.is_iso

def W : morphism_property (homotopy_category A c) := 
  λ _ _ f, h_quasi_iso A f

-- What we probably want is to bring any theorems about quasi isomorphisms
-- down to the homotopy category

@[priority 100]
instance h_quasi_iso_of_iso {X Y : homotopy_category A c} (f : X ⟶ Y) [is_iso f] : h_quasi_iso A f :=
{ is_iso := λ i, begin
    change is_iso (((homotopy_category.homology_functor A c i).map_iso (as_iso f)).hom),
    apply_instance,
  end }


def quasi_iso_is_rms : verdier.right_mult_sys (W A) := 
{ id   := λ X, ⟨ λ i, sorry ⟩,
  comp := sorry,
  sq   := sorry,
  pair := sorry}

end derived

end category_theory