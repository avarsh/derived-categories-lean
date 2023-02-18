
import category_theory.abelian.basic
import category_theory.triangulated.basic
import algebra.homology.homological_complex
import algebra.homology.homotopy_category
import algebra.homology.quasi_iso

namespace category_theory

namespace derived

open category pretriangulated abelian

-- We define the derived category of a (small) abelian category

universes v u

variables {A : Type u} [small_category A] [abelian A]

-- The derived category has cochain complexes of objects in an abelian 
-- category as objects
abbreviation cochain_complex (A : Type u) [category.{v} A] [abelian A] := 
  homological_complex A (complex_shape.up ℤ)

variables (X Y : cochain_complex A)

-- The morphisms are given by roofs up to equivalence
-- A roof consists of an object Z, a quasi-isomorphism
-- Z → X and a morphism in the homotopy category Z → Y.

def homotopy_quot := homotopy_category.quotient A (complex_shape.up ℤ)

structure roof (X Y : cochain_complex A) :=
  (Z   : cochain_complex A)
  (l   : Z ⟶ X)
  (r   : homotopy_quot.obj Z ⟶ homotopy_quot.obj Y)
  (qis : quasi_iso l)

-- Two roofs are equivalent if they are dominated in the homotopy
-- category by a third such diagram

def equiv_roofs (X Y : cochain_complex A) (F G : roof X Y) : Prop := 
  ∃ Z' : cochain_complex A, ∃ H  : Z' ⟶ F.Z, ∃ H' : Z' ⟶ G.Z,
    sorry

def hom := quot (equiv_roofs X Y)

def id_roof (X : cochain_complex A) : roof X X :=
{ Z := X,
  l := homological_complex.id X,
  r := homotopy_quot.map (homological_complex.id X),
  qis := quasi_iso_of_iso (homological_complex.id X) }

def id (X : cochain_complex A) : hom X X := 
  quot.mk (equiv_roofs X X) (id_roof X)

instance derived_category : category (cochain_complex A) :=
{ hom  := hom,
  id   := id,
  comp := sorry }

end derived

end category_theory