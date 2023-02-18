import category_theory.morphism_property

-- In this file we define the concept of a Verdier localization.
-- The presence of conditions defining a multiplicative system mean
-- that the resulting category is much easier to work with.
-- See Stacks Project [Tag 04VB]

noncomputable theory

namespace category_theory

namespace verdier

universe u

variables {C : Type u} [small_category C] {S : morphism_property C}

-- Define a right multiplicative system for a morphism property S 
-- I'm doing everything right multiplicatively to begin with so we can work with
-- roofs, but it doesn't really matter
structure right_mult_sys (S : morphism_property C) :=
  (id   : ∀ X : C, S (𝟙 X))
  (comp : ∀ X Y Z : C, ∀ f : X ⟶ Y, ∀ g : Y ⟶ Z, S f ∧ S g → S ( f ≫ g ))
  (sq   : ∀ Y Z W : C, ∀ f : Z ⟶ W, ∀ s : Y ⟶ W, S s →
            ∃ X : C, ∃ t : X ⟶ Z, ∃ g : X ⟶ Y, S t ∧ (g ≫ s) = (t ≫ f))
  (pair : ∀ X Y Z : C, ∀ f g : X ⟶ Y, ∀ s : Y ⟶ Z, S s ∧ (f ≫ s) = (g ≫ s) →
            ∃ W : C, ∃ t : W ⟶ X, S t ∧ (t ≫ f) = (t ≫ g))

variables (M : right_mult_sys S)

-- Wrap the objects of C into a new category
@[ext]
structure verdier_loc 
  (C : Type u) [small_category C]
  (M : right_mult_sys S) := 
(as : C)


-- Define the right calculus of fractions for a right multiplicative system

structure roof (X Y : verdier_loc C M) :=
  (Z   : verdier_loc C M)
  (f   : Z.as ⟶ X.as)
  (s   : Z.as ⟶ Y.as)
  (qis : S s)

def roof_equiv (X Y : verdier_loc C M) (r₁ r₂ : roof M X Y) : Prop :=
  ∃ r₃ : roof M X Y, ∃ u₁ : r₃.Z.as ⟶ r₁.Z.as, ∃ u₂ : r₃.Z.as ⟶ r₂.Z.as, 
    (u₁ ≫ r₁.s) = r₃.s ∧ (u₁ ≫ r₁.f) = r₃.f ∧ 
    (u₂ ≫ r₂.s) = r₃.s ∧ (u₂ ≫ r₂.f) = r₃.f

def id_roof (X : verdier_loc C M) : roof M X X :=
{ Z   := X,
  f   := 𝟙 X.as,
  s   := 𝟙 X.as,
  qis := M.id X.as }

def comp_roof (X₁ X₂ X₃ : verdier_loc C M) (r₁ : roof M X₁ X₂) (r₂ : roof M X₂ X₃) : roof M X₁ X₃ :=
have h : _ :=
  M.sq r₁.Z.as r₂.Z.as X₂.as r₂.f r₁.s r₁.qis,
let Z' := classical.some h in
have h₁ : (∃ (t : Z' ⟶ r₂.Z.as) (g : Z' ⟶ r₁.Z.as), S t ∧ g ≫ r₁.s = t ≫ r₂.f) := 
  classical.some_spec h,
let t := classical.some h₁ in
have h₂ : (∃ (g : Z' ⟶ r₁.Z.as), S t ∧ g ≫ r₁.s = t ≫ r₂.f) := 
  classical.some_spec h₁,
let g := classical.some h₂ in
have h₃ : (S t ∧ g ≫ r₁.s = t ≫ r₂.f) := 
  classical.some_spec h₂,
{ Z := {as := Z'},
  f   := g ≫ r₁.f,
  s   := t ≫ r₂.s,
  qis := 
    suffices h' : S t, by begin
      have comp : _ := M.comp Z' r₂.Z.as X₃.as t r₂.s,
      exact comp ⟨h', r₂.qis⟩
    end,
    h₃.left}
  
instance right_calc_of_fracs : category (verdier_loc C M) :=
{ hom  := λ X Y, quot (roof_equiv M X Y),
  id   := λ X, quot.mk (roof_equiv M X X) (id_roof M X),
  comp := λ X Y Z f g, quot.mk (roof_equiv M X Z) (comp_roof M X Y Z (quot.out f) (quot.out g)),
  -- It seems like we need to prove these manually too
  id_comp' := λ X Y f, sorry,
  comp_id' := sorry,
  assoc' := sorry,
}

end verdier

end category_theory