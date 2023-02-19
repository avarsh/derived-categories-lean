import category_theory.morphism_property

-- In this file we define the concept of a Verdier localization.
-- The presence of conditions defining a multiplicative system mean
-- that the resulting category is much easier to work with.
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

variables {M : left_mult_sys S}

lemma triple_comp {W X Y Z : C} (f₁ : W ⟶ X) (f₂ : X ⟶ Y) (f₃ : Y ⟶ Z) :
  S f₁ ∧ S f₂ ∧ S f₃ → S (f₁ ≫ f₂ ≫ f₃) := sorry

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

def valley_equiv (X Y : left_calculus C M) (v₁ v₂ : valley X Y) : Prop :=
  ∃ v₃ : valley X Y, ∃ u₁ : v₁.obj.as ⟶ v₃.obj.as, ∃ u₂ : v₂.obj.as ⟶ v₃.obj.as, 
    (v₁.f ≫ u₁) = v₃.f ∧ (v₁.s ≫ u₁) = v₃.s ∧ 
    (v₂.f ≫ u₂) = v₃.f ∧ (v₂.s ≫ u₂) = v₃.s

lemma valley_equiv_refl (X Y : left_calculus C M) : reflexive (valley_equiv X Y) :=
  λ v, ⟨ v, 𝟙 v.obj.as, 𝟙 v.obj.as, by simp, by simp, by simp, by simp ⟩

lemma valley_equiv_symm (X Y : left_calculus C M) : symmetric (valley_equiv X Y) :=
λ v w h, let ⟨u, ⟨ f, g, comm₁, comm₂, comm₃, comm₄ ⟩ ⟩ := h in
  ⟨ u, g, f, comm₃, comm₄, comm₁, comm₂ ⟩

-- We show transitivity using the notion of an "elementary equivalence"
-- It is just an aid to break the proof down into smaller chunks

def valley_elem_equiv {M : left_mult_sys S} {X Y : left_calculus C M} (v₁ v₂ : valley X Y) : Prop :=
  ∃ a : v₁.obj.as ⟶ v₂.obj.as, v₁.f ≫ a = v₂.f ∧ v₁.s ≫ a = v₂.s

lemma elem_implies_equiv {X Y : left_calculus C M} (u v : valley X Y) : 
  (∃ w : valley X Y, valley_elem_equiv u w ∧ valley_elem_equiv v w) → valley_equiv X Y u v :=
begin
  rintro ⟨ w, h₁, h₂ ⟩,
  rcases h₁ with ⟨ f, h₁' ⟩,
  rcases h₂ with ⟨ g, h₂' ⟩,
  use w.obj.as, use w.f, use w.s, use w.qis, use f, use g,
  exact ⟨ h₁'.left, h₁'.right, h₂' ⟩,
end

lemma dom_elem_implies_equiv {X Y : left_calculus C M} (u v : valley X Y) : 
  (∃ w : valley X Y, valley_elem_equiv w u ∧ valley_elem_equiv w v) → 
  valley_equiv X Y u v :=
begin
  intro h,
  rcases h with ⟨ w, hwu, hwv ⟩,
  rcases hwu with ⟨ a, ha ⟩,
  rcases hwv with ⟨ b, hb ⟩,
  have hore : _, from M.ore v.s u.s u.qis,
  rcases hore with ⟨ Z₁, c₁, s₁, hc₁, hcomm₁ ⟩,
  
  have hcancel : w.s ≫ b ≫ s₁ = w.s ≫ a ≫ c₁, by {
    rw [←hb.right, ←ha.right] at hcomm₁,
    simp at hcomm₁,
    exact hcomm₁ },
  have ht : _ := M.cancel (b ≫ s₁) (a ≫ c₁) w.s ⟨w.qis, hcancel⟩,
  rcases ht with ⟨ Z₂, t, ht₁, ht₂ ⟩,

  use Z₂, use u.f ≫ c₁ ≫ t, use v.s ≫ s₁ ≫ t,
  exact triple_comp v.s s₁ t ⟨v.qis, hc₁, ht₁⟩,

  use c₁ ≫ t,
  use s₁ ≫ t,
  
  split, { simp },
  split,
    { 
      suffices heq : u.s ≫ c₁ ≫ t = v.s ≫ s₁ ≫ t, from 
        begin
          simp, exact heq,
        end,
      have heq' : (u.s ≫ c₁) ≫ t = (v.s ≫ s₁) ≫ t, by rw hcomm₁,
      simp at heq', assumption,
    },
  split,
    { 
      simp,
      rw [←hb.left, ←ha.left],
      simp,
      simp at ht₂,
      rw ht₂
    },
    { simp }
end

lemma valley_equiv_trans (X Y : left_calculus C M) : transitive (valley_equiv X Y) :=
begin
  intros u v w huv hvw,
  rcases huv with ⟨ v₁, ⟨auv, a, i, j, k, l ⟩ ⟩,  
  rcases hvw with ⟨ v₂, ⟨b, avw, i', j', k', l' ⟩ ⟩,  
  have uelem : valley_elem_equiv u v₁, from ⟨ auv, ⟨ i, j ⟩ ⟩,
  have welem : valley_elem_equiv w v₂, from ⟨ avw, ⟨ k', l' ⟩ ⟩ ,
  have elem' : ∃ x, valley_elem_equiv x v₁ ∧ valley_elem_equiv x v₂, from begin
    use v,
    have velem₁ : valley_elem_equiv v v₁, from ⟨ a, ⟨ k, l ⟩ ⟩,
    have velem₂ : valley_elem_equiv v v₂, from ⟨ b, ⟨ i', j' ⟩ ⟩,
    exact ⟨ velem₁, velem₂ ⟩,
  end,
  have equiv : valley_equiv X Y v₁ v₂, from (dom_elem_implies_equiv v₁ v₂) elem',
  have equiv' : ∃ x, valley_elem_equiv u x ∧ valley_elem_equiv w x, from 
    begin
      rcases equiv with ⟨ z, u₁, u₂, hequiv ⟩,
      use z,
      split,
      { rw [← i, ← j ] at hequiv,
        simp at hequiv,
        rcases hequiv with ⟨ ha, hb, _ ⟩,
        exact ⟨auv ≫ u₁, ⟨ ha, hb⟩ ⟩ },
      { rw [← k', ← l'] at hequiv,
        simp at hequiv,
        rcases hequiv with ⟨ _, _, ha, hb ⟩,
        exact ⟨ avw ≫ u₂, ⟨ ha, hb ⟩⟩ }
    end, 
  exact (elem_implies_equiv u w) equiv',
end

instance (X Y : left_calculus C M) : setoid (valley X Y) :=
  { r := valley_equiv X Y,
    iseqv := ⟨ valley_equiv_refl X Y, valley_equiv_symm X Y, valley_equiv_trans X Y ⟩
  }

-- Define the identity and composition of valleys

def id_valley (X : left_calculus C M) : valley X X :=
{ obj := X,
  f   := 𝟙 X.as,
  s   := 𝟙 X.as,
  qis := M.id }

def comp_valley (X Y Z : left_calculus C M) (v₁ : valley X Y) (v₂ : valley Y Z) : valley X Z :=
  let Y' := v₁.obj, Z' := v₂.obj in
  have hyp : _ :=
    M.ore v₂.f v₁.s v₁.qis,
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
    qis := have comp : _ := M.comp v₂.s u, comp ⟨v₂.qis, hyp₃⟩ }

-- Define the category structure

instance : category (left_calculus C M) :=
{ hom  := λ X Y, quot (valley_equiv X Y),
  id   := λ X, quot.mk (valley_equiv X X) (id_valley X),
  comp := λ X Y Z f g, quot.mk (valley_equiv X Z) (comp_valley X Y Z (quot.out f) (quot.out g)),
  -- It seems like we need to prove these manually too
  id_comp' := λ X Y f, sorry,
  comp_id' := sorry,
  assoc' := sorry,
}

end derived

end category_theory