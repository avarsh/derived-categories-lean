
import category_theory.abelian.basic
import category_theory.localization.construction
import category_theory.triangulated.basic
import algebra.homology.homological_complex
import algebra.homology.homotopy_category
import algebra.homology.quasi_iso
import category_theory.morphism_property

import verdier

namespace category_theory

namespace derived

open category abelian verdier

-- We define the derived category of a (small) abelian category

universes v u

variables (A : Type u) [small_category A] [abelian A]

def c := complex_shape.up ℤ

variables (X Y : homotopy_category A c)

-- Mirror the definition of quasi-iso, but for the homotopy category 
class quasi_iso {X Y : homotopy_category A c} (f : X ⟶ Y) : Prop :=
(is_iso : ∀ i, is_iso ((homotopy_category.homology_functor A c i).map f))

def W : morphism_property (homotopy_category A c) :=
  λ _ _ f, quasi_iso A f

def derived_category := (W A).localization

end derived

end category_theory
