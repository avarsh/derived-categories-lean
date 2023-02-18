import category_theory.category.basic

noncomputable theory

namespace category_theory

universe u

-- MINIMAL EXAMPLE
variables (C : Type u) [small_category C]

structure my_struct (Z : C) :=
  (X : C)
  (f : X ⟶ Z)


-- Dummy hypothesis
def hyp : ∃ X : C, ∃ f : X ⟶ X, f = f := 
  sorry

variables (Z : C)

def object : my_struct C Z :=
let X' := begin
  have h, from hyp C,
  choose X hX using h,
  exact X
end in
{ X := X',
  f := begin
    simp at X',
    sorry
    -- Lean wants something of type
    -- classical.some _ ⟶ Z
    -- I think we can do this with
    -- classical.some_spec but not sure how 
  end }

end category_theory