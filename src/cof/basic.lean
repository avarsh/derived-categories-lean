import category_theory.morphism_property

-- In these files we define the concept of localizing a category at a
-- (left) multiplicative system.
-- The presence of conditions defining a multiplicative system mean
-- that the resulting category is much easier to work with than
-- localization through the path category.
-- See Stacks Project [Tag 04VB]

noncomputable theory

namespace category_theory

namespace derived

universe u

variables {C : Type u} [small_category C] {S : morphism_property C}

-- Define a left multiplicative system for a morphism property S
structure left_mult_sys (S : morphism_property C) :=
  (id     : ∀ {X : C}, S (𝟙 X))
  (comp   : ∀ {X Y Z : C}, ∀ f : X ⟶ Y, ∀ g : Y ⟶ Z, S f ∧ S g → S ( f ≫ g ))
  (ore    : ∀ {X Y Z : C}, ∀ g : X ⟶ Y, ∀ t : X ⟶ Z, S t →
            ∃ W : C, ∃ f : Z ⟶ W, ∃ s : Y  ⟶ W, S s ∧ (g ≫ s) = (t ≫ f))
  (cancel : ∀ {X Y Z : C}, ∀ f g : X ⟶ Y, ∀ t : Z ⟶ X, S t ∧ (t ≫ f) = (t ≫ g) →
            ∃ W : C, ∃ s : Y ⟶ W, S s ∧ (f ≫ s) = (g ≫ s))

-- Wrap the objects of C into a new category
@[ext]
structure left_calculus 
  (C : Type u) [small_category C]
  (M : left_mult_sys S) := 
(as : C)

end derived

end category_theory