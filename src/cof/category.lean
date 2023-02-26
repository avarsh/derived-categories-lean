import cof.basic
import cof.valley

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
variables {M : left_mult_sys S}

-- Define the identity and composition of valleys

def id_valley (X : left_calculus C M) : valley X X :=
{ obj := X,
  f   := 𝟙 X.as,
  s   := 𝟙 X.as,
  qis := M.id }

structure ore_data {X Y Z : C} := 
  (W  : C)
  (f₁ : X ⟶ Y) 
  (s₁ : X ⟶ Z) 
  (s₂ : Y ⟶ W) 
  (f₂ : Z ⟶ W)
  (hs : (S s₁ ∧ S s₂))
  (comm : (s₁ ≫ f₂) = (f₁ ≫ s₂))

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
    qis := M.comp ⟨v₂.qis, data.hu⟩ }

lemma comp_valley_obj {X Y Z : left_calculus C M} 
    (v₁ : valley X Y) (v₂ : valley Y Z) (data : comp_data v₁ v₂)
  : (comp_valley_from_data v₁ v₂ data).obj.as = data.W := rfl

-- As a default, we can always define composition using the Ore data
def comp_valley {X Y Z : left_calculus C M} (v₁ : valley X Y) (v₂ : valley Y Z) : valley X Z :=
  comp_valley_from_data v₁ v₂ data_from_ore

-- Composition is well defined under the equivalence relation

lemma comp_independent_of_data' {X Y Z : left_calculus C M} (v₁ : valley X Y) (v₂ : valley Y Z) (d₁ d₂ : comp_data v₁ v₂) :
  ⟦ comp_valley_from_data v₁ v₂ d₁ ⟧ = ⟦ comp_valley_from_data v₁ v₂ d₂ ⟧  :=
let c₁ := comp_valley_from_data v₁ v₂ d₁, c₂ := comp_valley_from_data v₁ v₂ d₂ in
match M.ore d₂.u d₁.u d₁.hu with ⟨W, h', u', hu', hc⟩ := 
  begin
    have h₁ : _, by calc
      v₁.s ≫ d₂.h ≫ u' = (v₂.f ≫ d₂.u) ≫ u' : by rw [←category.assoc, d₂.comm]
      ... = v₂.f ≫ (d₁.u ≫ h') : by rw [category.assoc, hc]
      ... = v₁.s ≫ d₁.h ≫ h' : by {rw [←category.assoc, d₁.comm], simp},
    have h₂ : _, from M.cancel ⟨v₁.qis, h₁⟩,
    rcases h₂ with ⟨Z', s', hs', hc'⟩,

    let h'' := h' ≫ s',
    let u'' := u' ≫ s',
    have h₂ : d₂.h ≫ u'' = d₁.h ≫ h'', by rw [←category.assoc, hc', category.assoc],
    have h₃ : d₂.u ≫ u'' = d₁.u ≫ h'', by rw [←category.assoc, hc, category.assoc],
    have hu'' : S u'', from M.comp ⟨hu', hs'⟩,

    apply quotient.eq.mpr,
    have v : valley X Z := {
      obj := {as := Z'},
      f   := v₁.f ≫ d₂.h ≫ u'',
      s   := v₂.s ≫ d₂.u ≫ u'',
      qis := triple_comp M ⟨v₂.qis, d₂.hu, hu''⟩,
    },
    have heq : v.obj.as = Z', from
    begin
      sorry -- Aargh!
    end,
    use v,
    -- We want to use h'' here but it won't unify the types
    sorry,
  end
end


lemma comp_independent_of_data {X Y Z : left_calculus C M} (v₁ : valley X Y) (v₂ : valley Y Z) (d : comp_data v₁ v₂) :
  ⟦ comp_valley v₁ v₂ ⟧ = ⟦ comp_valley_from_data v₁ v₂ d ⟧  :=
comp_independent_of_data' v₁ v₂ data_from_ore d

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

-- We don't need this here
def modify_ore {X Y Z W A₁ A₂ : C} (data : @ore_data C _ S X Y Z) 
  {s : A₁ ⟶ A₂} (hs : S s) (g₁ : A₂ ⟶ Y) (g₂ : A₂ ⟶ Z) (hc : s ≫ g₂ ≫ data.f₂ = s ≫ g₁ ≫ data.s₂) : 
  ∃ (d' : @ore_data C _ S X Y Z), g₂ ≫ d'.f₂ = g₁ ≫ d'.s₂ := 
sorry

lemma assoc_out {W X Y Z : left_calculus C M} (a : valley W X) (b : valley X Y) (c : valley Y Z) :
  veq W Z (comp_valley (comp_valley a b) c) (comp_valley a (comp_valley b c)) :=
let lassoc := (comp_valley (comp_valley a b) c),
    rassoc := (comp_valley a (comp_valley b c)) in
begin
  rcases (M.ore b.f a.s a.qis) with ⟨Y'', f₁, s₁, hs₁, hc₁⟩,
  rcases (M.ore c.f b.s b.qis) with ⟨Z'', f₂, s₂, hs₂, hc₂⟩,
  rcases (M.ore f₂ s₁ hs₁)     with ⟨Z''', f₃, s₃, hs₃, hc₃⟩,

  have v : valley W Z := {
    obj := ⟨ Z''' ⟩,
    f   := a.f ≫ f₁ ≫ f₃,
    s   := c.s ≫ s₂ ≫ s₃,
    qis  := triple_comp M c.s s₂ s₃ ⟨c.qis, hs₂, hs₃⟩,
  },

  have heq₁ : veq W Z lassoc v, from sorry,
  have heq₂ : veq W Z v rassoc, from sorry,
  exact valley_equiv_trans W Z heq₁ heq₂,
end

lemma assoc' {W X Y Z : left_calculus C M} (f : hom_type W X) (g : hom_type X Y) (h : hom_type Y Z) :
  comp (comp f g) h = comp f (comp g h) :=
let a := f.out,
    b := g.out,
    c := h.out in
begin
  sorry
end

-- Define the category structure

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