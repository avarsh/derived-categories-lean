import category_theory.morphism_property

-- In this file we define the concept of localizing a category at a
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

variables {M : left_mult_sys S}

lemma triple_comp {W X Y Z : C} (M : left_mult_sys S) (f₁ : W ⟶ X) (f₂ : X ⟶ Y) (f₃ : Y ⟶ Z) :
  S f₁ ∧ S f₂ ∧ S f₃ → S (f₁ ≫ f₂ ≫ f₃) := 
begin
  rintro ⟨ s₁, s₂, s₃ ⟩,
  have s₄ : S (f₂ ≫ f₃) := M.comp f₂ f₃ ⟨s₂, s₃⟩,
  exact M.comp f₁ (f₂ ≫ f₃) ⟨s₁, s₄⟩  
end

-- Wrap the objects of C into a new category
@[ext]
structure left_calculus 
  (C : Type u) [small_category C]
  (M : left_mult_sys S) := 
(as : C)


-- Define the left calculus of fractions for a lwft multiplicative system

-- The morphisms are given by valleys, under an equivalence
structure valley (X Y : left_calculus C M) :=
  (obj : left_calculus C M)
  (f   : X.as ⟶ obj.as)
  (s   : Y.as ⟶ obj.as)
  (qis : S s)

-- Define the equivalence

def veq (X Y : left_calculus C M) (v₁ v₂ : valley X Y) : Prop :=
  ∃ v₃ : valley X Y, ∃ u₁ : v₁.obj.as ⟶ v₃.obj.as, ∃ u₂ : v₂.obj.as ⟶ v₃.obj.as, 
    (v₁.f ≫ u₁) = v₃.f ∧ (v₁.s ≫ u₁) = v₃.s ∧ 
    (v₂.f ≫ u₂) = v₃.f ∧ (v₂.s ≫ u₂) = v₃.s

lemma valley_equiv_refl (X Y : left_calculus C M) : reflexive (veq X Y) :=
  λ v, ⟨ v, 𝟙 v.obj.as, 𝟙 v.obj.as, by simp, by simp, by simp, by simp ⟩

lemma valley_equiv_symm (X Y : left_calculus C M) : symmetric (veq X Y) :=
λ v w h, let ⟨u, ⟨ f, g, comm₁, comm₂, comm₃, comm₄ ⟩ ⟩ := h in
  ⟨ u, g, f, comm₃, comm₄, comm₁, comm₂ ⟩

-- We show transitivity using the notion of "dominance"
-- It is just an aid to break the proof down into smaller chunks

def valley_dom {M : left_mult_sys S} {X Y : left_calculus C M} (v₁ v₂ : valley X Y) : Prop :=
  ∃ a : v₁.obj.as ⟶ v₂.obj.as, v₁.f ≫ a = v₂.f ∧ v₁.s ≫ a = v₂.s

notation a ` E ` b := valley_dom a b

-- Equivalence of valleys is equivalent to dominating a common valley 
lemma dom_iff_equiv {X Y : left_calculus C M} (u v : valley X Y) : 
  (∃ w : valley X Y, (u E w) ∧ (v E w)) ↔ veq X Y u v :=
begin
  split,
    rintro ⟨ w, h₁, h₂ ⟩,
    rcases h₁ with ⟨ f, h₁' ⟩,
    rcases h₂ with ⟨ g, h₂' ⟩,
    use w.obj.as, use w.f, use w.s, use w.qis, use f, use g,
    exact ⟨ h₁'.left, h₁'.right, h₂' ⟩,

    rintro ⟨ w, f, g, h₁, h₂, h₃, h₄ ⟩,
    use w,
    split,
      exact ⟨f, ⟨h₁, h₂⟩⟩,
      exact ⟨g, ⟨h₃, h₄⟩⟩
end

-- If both u and v are dominated by some w, then they are equivalent valleys
lemma mut_dom_implies_equiv {X Y : left_calculus C M} (u v : valley X Y) : 
  (∃ w : valley X Y, (w E u) ∧ (w E v)) → veq X Y u v :=
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
  exact triple_comp M v.s s₁ t ⟨v.qis, hc₁, ht₁⟩,

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

lemma valley_equiv_trans (X Y : left_calculus C M) : transitive (veq X Y) :=
begin
  intros u v w huv hvw,
  rcases huv with ⟨ v₁, ⟨auv, a, i, j, k, l ⟩ ⟩,  
  rcases hvw with ⟨ v₂, ⟨b, avw, i', j', k', l' ⟩ ⟩,  
  have uelem : (u E v₁), from ⟨ auv, ⟨ i, j ⟩ ⟩,
  have welem : (w E v₂), from ⟨ avw, ⟨ k', l' ⟩ ⟩ ,
  have elem' : ∃ x, (x E v₁) ∧ (x E v₂), from begin
    use v,
    have velem₁ : (v E v₁), from ⟨ a, ⟨ k, l ⟩ ⟩,
    have velem₂ : (v E v₂), from ⟨ b, ⟨ i', j' ⟩ ⟩,
    exact ⟨ velem₁, velem₂ ⟩,
  end,
  have equiv : veq X Y v₁ v₂, from (mut_dom_implies_equiv v₁ v₂) elem',
  have equiv' : ∃ x, (u E x) ∧ (w E x), from 
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
  exact (dom_iff_equiv u w).mp equiv',
end

def valley_setoid (X Y : left_calculus C M) : setoid (valley X Y) :=
  { r := veq X Y,
    iseqv := ⟨ valley_equiv_refl X Y, valley_equiv_symm X Y, valley_equiv_trans X Y ⟩
  }
attribute [instance] valley_setoid


-- Define the identity and composition of valleys

def id_valley (X : left_calculus C M) : valley X X :=
{ obj := X,
  f   := 𝟙 X.as,
  s   := 𝟙 X.as,
  qis := M.id }

-- Mathematically we should check that the composition doesn't depend on
-- the choices we make, once we pass to the equivalence relation.
-- I'm not sure when we need to prove this here though!

structure comp_data {X Y Z : left_calculus C M} (v₁ : valley X Y) (v₂ : valley Y Z) :=
  (W    : C) 
  (h    : v₁.obj.as ⟶ W) 
  (u    : v₂.obj.as ⟶ W) 
  (hu   : S u)
  (comm : v₂.f ≫ u = v₁.s ≫ h)

-- The Ore condition gives us composition data automatically
def data_from_ore {X Y Z : left_calculus C M} {v₁ : valley X Y} {v₂ : valley Y Z} : comp_data v₁ v₂ :=
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
  have hyp₃ : S u ∧ v₂.f ≫ u = v₁.s ≫ h := (classical.some_spec hyp₂),
  { W    := Z'',
    h    := h,
    u    := u,
    hu   := hyp₃.left,
    comm := hyp₃.right }

def comp_valley_from_data {X Y Z : left_calculus C M} 
    (v₁ : valley X Y) (v₂ : valley Y Z) (data : comp_data v₁ v₂)
  : valley X Z :=
  { obj := ⟨ data.W ⟩,
    f   := v₁.f ≫ data.h,
    s   := v₂.s ≫ data.u,
    qis := M.comp v₂.s data.u ⟨v₂.qis, data.hu⟩ }

-- As a default, we can always define composition using the Ore data
def comp_valley {X Y Z : left_calculus C M} (v₁ : valley X Y) (v₂ : valley Y Z) : valley X Z :=
  comp_valley_from_data v₁ v₂ data_from_ore

-- Composition is well defined under the equivalence relation

lemma comp_independent_of_data {X Y Z : left_calculus C M} (v₁ : valley X Y) (v₂ : valley Y Z) (d₁ d₂ : comp_data v₁ v₂) :
  ⟦ comp_valley_from_data v₁ v₂ d₁ ⟧ = ⟦ comp_valley_from_data v₁ v₂ d₂ ⟧  :=
begin
  sorry
end

lemma comp_well_def {X Y Z : left_calculus C M}  (v₁ v₁' : valley X Y) (v₂ v₂' : valley Y Z) :
  ⟦ v₁ ⟧ = ⟦ v₁' ⟧ ∧ ⟦ v₂ ⟧ = ⟦ v₂' ⟧ → ⟦ comp_valley v₁ v₂ ⟧ = ⟦ comp_valley v₁' v₂' ⟧ := 
begin
  rintro ⟨ h₁, h₂ ⟩,
  sorry,
end

-- The axioms for the category

def hom_type (X Y : left_calculus C M) := quotient (valley_setoid X Y)

def id (X : left_calculus C M) := ⟦ id_valley X ⟧

def comp {X Y Z : left_calculus C M} (f : hom_type X Y) (g : hom_type Y Z) := 
  ⟦ comp_valley (quotient.out f) (quotient.out g) ⟧
  

lemma id_comp' (X Y : left_calculus C M) (f :hom_type X Y) :
  comp (id X) f = f :=
let g  := comp (id X) f,
    f' := f.out,
    data : comp_data (id_valley X) f' :=
      { W := f'.obj.as,
        h := f'.f,
        u := (𝟙 f'.obj.as),
        hu := M.id,
        comm := have h : (id_valley X).s = 𝟙 X.as, from rfl,
          by {simp, rw h, simp},
      },
    g' := comp_valley_from_data (id_valley X) f.out data in
begin
  suffices hlift : veq X Y g.out f', from begin
      apply quotient.out_equiv_out.mp,
      exact hlift,
    end,
  have h₁ : veq X Y g.out g', from begin
      suffices heq : g = ⟦g'⟧, from begin 
        have hout : veq X Y g.out (⟦g'⟧.out), from quotient.out_equiv_out.mpr heq,
        have hout' : veq X Y ⟦g'⟧.out g', from quotient.mk_out g',
        exact valley_equiv_trans X Y hout hout',
      end,
      -- We will need to apply both comp_independent_of_data
      -- and comp_well_def here.
      sorry,
    end,
  suffices h' : veq X Y g' f', from valley_equiv_trans X Y h₁ h',
  use g', use 𝟙 g'.obj.as, use 𝟙 g'.obj.as, 
  simp,
  have heq₁ : g'.f = (𝟙 X.as ≫ f'.f), from rfl,
  have heq₂ : g'.s = (f'.s ≫ 𝟙 f'.obj.as), from rfl,
  rw [heq₁, heq₂],
  have h₁ : 𝟙 g'.obj.as = 𝟙 f'.obj.as, from rfl,
  rw h₁,
  simp,
end

-- Define the category structure

-- Question about choice: I'm defining a category where the morphisms are
-- some structure under an equivalence relation. When defining composition,
-- there's a bunch of choices which are made, but the quivalence class
-- of the composition is independent of these choices. 
-- It looks like the only place where I need this independence is when
-- proving id_comp', comp_id' and assoc'. Is this enough? Shouldn't I have to prove 
-- it at the point where composition is even defined, i.e. while taking the quotient?

instance : category (left_calculus C M) :=
{ hom  := hom_type,
  id   := id,
  comp := λ _ _ _ f g, comp f g,
  -- It seems like we need to prove these manually too
  id_comp' := id_comp',
  comp_id' := sorry,
  assoc' := sorry,
}

end derived

end category_theory