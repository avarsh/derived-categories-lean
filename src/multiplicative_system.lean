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

-- Define a left multiplicative system for a morphism property S
structure left_mult_sys (S : morphism_property C) :=
  (id     : ∀ X : C, S (𝟙 X))
  (comp   : ∀ X Y Z : C, ∀ f : X ⟶ Y, ∀ g : Y ⟶ Z, S f ∧ S g → S ( f ≫ g ))
  (ore    : ∀ X Y Z : C, ∀ g : X ⟶ Y, ∀ t : X ⟶ Z, S t →
            ∃ W : C, ∃ f : Z ⟶ W, ∃ s : Y  ⟶ W, S s ∧ (g ≫ s) = (t ≫ f))
  (cancel : ∀ X Y Z : C, ∀ f g : X ⟶ Y, ∀ t : Z ⟶ X, S t ∧ (t ≫ f) = (t ≫ g) →
            ∃ W : C, ∃ s : Y ⟶ W, S s ∧ (f ≫ s) = (g ≫ s))

variables (M : left_mult_sys S)

-- Wrap the objects of C into a new category
@[ext]
structure left_calculus 
  (C : Type u) [small_category C]
  (M : left_mult_sys S) := 
(as : C)


-- Define the left calculus of fractions for a right multiplicative system

-- The morphisms are given by valleys, under an equivalence
structure valley (X Y : left_calculus C M) :=
  (obj : left_calculus C M)
  (f   : X.as ⟶ obj.as)
  (s   : Y.as ⟶ obj.as)
  (qis : S s)

-- Define the equivalence

def valley_equiv (X Y : left_calculus C M) (v₁ v₂ : valley M X Y) : Prop :=
  ∃ v₃ : valley M X Y, ∃ u₁ : v₁.obj.as ⟶ v₃.obj.as, ∃ u₂ : v₂.obj.as ⟶ v₃.obj.as, 
    (v₁.f ≫ u₁) = v₃.f ∧ (v₁.s ≫ u₁) = v₃.s ∧ 
    (v₂.f ≫ u₂) = v₃.f ∧ (v₂.s ≫ u₂) = v₃.s

lemma valley_equiv_refl (X Y : left_calculus C M) : reflexive (valley_equiv M X Y) :=
  λ v, ⟨ v, 𝟙 v.obj.as, 𝟙 v.obj.as, by simp, by simp, by simp, by simp ⟩

lemma valley_equiv_symm (X Y : left_calculus C M) : symmetric (valley_equiv M X Y) :=
λ v w h, let ⟨u, ⟨ f, g, comm₁, comm₂, comm₃, comm₄ ⟩ ⟩ := h in
  ⟨ u, g, f, comm₃, comm₄, comm₁, comm₂ ⟩

def valley_elem_equiv (X Y : left_calculus C M) (v₁ v₂ : valley M X Y) : Prop :=
  ∃ a : v₁.obj.as ⟶ v₂.obj.as, v₁.f ≫ a = v₂.f ∧ v₁.s ≫ a = v₂.s
 
lemma valley_elem_equiv_refl (X Y : left_calculus C M) : reflexive (valley_elem_equiv M X Y) :=
begin
  intro u,
  use (𝟙 u.obj.as),
  simp,
end

lemma valley_elem_equiv_trans (X Y : left_calculus C M) : transitive (valley_elem_equiv M X Y) :=
begin
  intros u v w huv huw,
  rcases huv with ⟨ a₁, h₁ ⟩,
  rcases huw with ⟨ a₂, h₂ ⟩,
  use a₁ ≫ a₂,
  split,
  { rw ←(h₁.left) at h₂,
    simp at h₂,
    exact h₂.left },
  { rw ←(h₁.right) at h₂,
    simp at h₂,
    exact h₂.right }
end

-- failed attempt
lemma valley_equiv_trans (X Y : left_calculus C M) : transitive (valley_equiv M X Y) :=
begin
  intros u v w huv hvw,
  rcases huv with ⟨ v₁, ⟨f₁, g₁, _, _ , _, _ ⟩ ⟩,  
  rcases hvw with ⟨ v₂, ⟨f₂, g₂, _, _ , _, _ ⟩ ⟩,  
  have ore₁ : _, from M.ore Y.as v.obj.as u.obj.as v.s u.s u.qis,
  rcases ore₁ with ⟨ Z', f', s', ⟨ qis₁, _ ⟩ ⟩,
  have ore₂ : _, from M.ore Y.as v.obj.as w.obj.as v.s w.s w.qis,
  rcases ore₂ with ⟨ Z'', f'', s'', ⟨ qis₂, _ ⟩⟩,
  have ore₃ : _, from M.ore v.obj.as Z' Z'' s' s'' qis₂,
  rcases ore₃ with ⟨ W, f₃, s_w, ⟨ qis₃, _ ⟩ ⟩,
  use W,
  use w.f ≫ f'' ≫ f₃,
  use v.s ≫ s' ≫ s_w,
  simp,
  have qis_comp : S (s' ≫ s_w), from M.comp _ _ _ s' s_w ⟨qis₁, qis₃⟩,
  exact M.comp _ _ _ v.s (s' ≫ s_w) ⟨v.qis, qis_comp⟩,
  simp,
  use (f' ≫ s_w),
  split,
  sorry,
end

instance (X Y : left_calculus C M) : setoid (valley M X Y) :=
  { r := valley_equiv M X Y,
    iseqv := ⟨ valley_equiv_refl M X Y, valley_equiv_symm M X Y, valley_equiv_trans M X Y ⟩
  }

def id_valley (X : left_calculus C M) : valley M X X :=
{ obj := X,
  f   := 𝟙 X.as,
  s   := 𝟙 X.as,
  qis := M.id X.as }


def comp_valley (X Y Z : left_calculus C M) (v₁ : valley M X Y) (v₂ : valley M Y Z) : valley M X Z :=
let Y' := v₁.obj, Z' := v₂.obj in
have hyp : _ :=
  M.ore Y.as Z'.as Y'.as v₂.f v₁.s v₁.qis,
let Z'' := classical.some hyp in
have hyp₁ : ∃ (f : Y'.as ⟶ Z'') (s : Z'.as ⟶ Z''), S s ∧ v₂.f ≫ s = v₁.s ≫ f := 
  classical.some_spec hyp,
let h := classical.some hyp₁ in
have hyp₂ : ∃ (s : Z'.as ⟶ Z''), S s ∧ v₂.f ≫ s = v₁.s ≫ h := 
  classical.some_spec hyp₁,
let u := classical.some hyp₂ in
have hyp₃ : S u := (classical.some_spec hyp₂).left,
{ obj := ⟨ Z'' ⟩,
  f   := v₁.f ≫ h,
  s   := v₂.s ≫ u,
  qis := have comp : _ := M.comp Z.as Z'.as Z'' v₂.s u, comp ⟨v₂.qis, hyp₃⟩ }

instance : category (left_calculus C M) :=
{ hom  := λ X Y, quot (valley_equiv M X Y),
  id   := λ X, quot.mk (valley_equiv M X X) (id_valley M X),
  comp := λ X Y Z f g, quot.mk (valley_equiv M X Z) (comp_valley M X Y Z (quot.out f) (quot.out g)),
  -- It seems like we need to prove these manually too
  id_comp' := λ X Y f, sorry,
  comp_id' := sorry,
  assoc' := sorry,
}

end verdier

end category_theory