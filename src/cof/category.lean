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
    
    let v : valley X Z := {
      obj := {as := Z'},
      f   := v₁.f ≫ d₂.h ≫ u'',
      s   := v₂.s ≫ d₂.u ≫ u'',
      qis := triple_comp M ⟨v₂.qis, d₂.hu, hu''⟩,
    },
    use [v, h'', u''],

    simp, split,
    have hlemma : c₁.f = (v₁.f ≫ d₁.h), by refl, 
    rw [hlemma, h₂], simp,

    split,
    have hlemma : c₁.s = (v₂.s ≫ d₁.u), by refl,
    rw [hlemma, h₃], simp,

    split,
    have hlemma : c₂.f = (v₁.f ≫ d₂.h), by refl,
    rw hlemma, simp,

    have hlemma : c₂.s = (v₂.s ≫ d₂.u), by refl,
    rw hlemma, simp,
  end
end


lemma comp_independent_of_data {X Y Z : left_calculus C M} (v₁ : valley X Y) (v₂ : valley Y Z) (d : comp_data v₁ v₂) :
  ⟦ comp_valley v₁ v₂ ⟧ = ⟦ comp_valley_from_data v₁ v₂ d ⟧  :=
comp_independent_of_data' v₁ v₂ data_from_ore d

lemma dom_imp_post_comp {X Y Z : left_calculus C M} (v₁ v₂ : valley X Y) (w : valley Y Z) (dom : v₁ E v₂) : 
  ⟦ comp_valley v₁ w ⟧ = ⟦ comp_valley v₂ w ⟧ :=
begin
  rcases dom with ⟨a, ha₁, ha₂⟩,

  let g := w.f,
  have hore : _ := M.ore g v₂.s v₂.qis,
  rcases hore with ⟨Z'', h, u, hu, hcomm⟩,

  have hcomm' : g ≫ u = v₁.s ≫ a ≫ h, by rw [←category.assoc, ha₂, hcomm],
  let d₁ : comp_data v₁ w := {
    W := Z'',
    h := a ≫ h,
    u := u,
    hu := hu,
    comm := hcomm',
  },
  let d₂ : comp_data v₂ w := {
    W := Z'',
    h := h,
    u := u,
    hu := hu,
    comm := hcomm,
  },
  have hcomp₁ : _ := comp_independent_of_data v₁ w d₁,
  have hcomp₂ : _ := comp_independent_of_data v₂ w d₂,

  let c₁ := comp_valley_from_data v₁ w d₁,
  let c₂ := comp_valley_from_data v₂ w d₂,
  suffices heq : ⟦ c₁ ⟧ = ⟦ c₂ ⟧, by rw [hcomp₁, hcomp₂, heq],

  suffices heq' : veq X Z c₁ c₂, by {apply quotient.eq.mpr, exact heq'},
  
  use [Z'', c₁.f, c₂.s, c₂.qis, 𝟙 Z'', 𝟙 Z''],
  simp,
  -- idk why we need this, but simp can't seem to take care of it
  -- otherwise.
  have hlemma : ∀ {X : C}, ∀ f : X ⟶ Z'', f ≫ 𝟙 Z'' = f, by {intro f, simp},
  split, exact hlemma c₁.f, rw [hlemma c₁.s],
  split, refl, 
  split, rw [hlemma c₂.f],

  have hc₁ : c₁.f = v₁.f ≫ a ≫ h, by refl, rw hc₁,
  have hc₂ : c₂.f = v₂.f ≫ h, by refl, rw hc₂,
  rw [←category.assoc, ha₁],
  rw hlemma c₂.s,
end


lemma dom_imp_pre_comp {X Y Z : left_calculus C M} (v₁ v₂ : valley X Y) (w: valley Z X) (dom : v₁ E v₂) : 
  ⟦ comp_valley w v₁ ⟧ = ⟦ comp_valley w v₂ ⟧ :=
begin
  rcases dom with ⟨a, ha₁, ha₂⟩,

  have hore₁ : _ := M.ore v₁.f w.s w.qis,
  rcases hore₁ with ⟨Z₁, h₁, t₁, ht₁, hcomm₁⟩,
  have hore₂ : _ := M.ore a t₁ ht₁,
  rcases hore₂ with ⟨Z₂, h₂, t₂, ht₂, hcomm₂⟩,

  let d₁ : comp_data w v₁ := {
    W := Z₁,
    h := h₁,
    u := t₁,
    hu := ht₁,
    comm := hcomm₁,
  },

  have hcomm' : v₂.f ≫ t₂ = w.s ≫ h₁ ≫ h₂, by
    {rw [←ha₁, category.assoc, hcomm₂, ←category.assoc, hcomm₁], simp},
  let d₂ : comp_data w v₂ := {
    W := Z₂,
    h := h₁ ≫ h₂,
    u := t₂,
    hu := ht₂,
    comm := hcomm',
  },

  have hcomp₁ : _ := comp_independent_of_data w v₁ d₁,
  have hcomp₂ : _ := comp_independent_of_data w v₂ d₂,

  let c₁ := comp_valley_from_data w v₁ d₁,
  let c₂ := comp_valley_from_data w v₂ d₂,
  suffices heq : ⟦ c₁ ⟧ = ⟦ c₂ ⟧, by rw [hcomp₁, hcomp₂, heq],
  suffices heq' : veq Z Y c₁ c₂, by {apply quotient.eq.mpr, exact heq'},

  use [c₂, h₂, 𝟙 Z₂],  
  split, 
  { have hlemma₁ : c₁.f = w.f ≫ h₁, by refl,
    rw hlemma₁, simp,
    have hlemma₂ : c₂.f = w.f ≫ (h₁ ≫ h₂), by refl,
    rw hlemma₂ },
  split, 
  { have hlemma₁ : c₁.s = v₁.s ≫ t₁, by refl, 
    have hlemma₂ : c₂.s = v₂.s ≫ t₂, by refl,
    rw [hlemma₁, hlemma₂], simp, rw [←hcomm₂, ←category.assoc, ha₂] },
   
  have hlemma : ∀ {X : C}, ∀ f : X ⟶ Z₂, f ≫ 𝟙 Z₂ = f, by {intro f, simp},
  split,
  rw hlemma c₂.f,
  rw hlemma c₂.s,
end

lemma comp_well_def {X Y Z : left_calculus C M}  (v₁ v₁' : valley X Y) (v₂ v₂' : valley Y Z) :
  ⟦ v₁ ⟧ = ⟦ v₁' ⟧ ∧ ⟦ v₂ ⟧ = ⟦ v₂' ⟧ → ⟦ comp_valley v₁ v₂ ⟧ = ⟦ comp_valley v₁' v₂' ⟧ := 
begin
  rintro ⟨ h₁, h₂ ⟩,
  have h₁' : _ := quotient.eq.mp h₁,
  have h₂' : _ := quotient.eq.mp h₂,
  
  show ⟦ comp_valley v₁ v₂ ⟧ = ⟦ comp_valley v₁' v₂' ⟧,

  have dom₁ : _ := (dom_iff_equiv _ _).mpr h₁',
  have dom₂ : _ := (dom_iff_equiv _ _).mpr h₂',

  rcases dom₁ with ⟨w₁, dv₁, dv₁'⟩,
  rcases dom₂ with ⟨w₂, dv₂, dv₂'⟩,
  
  have heq₁ : ⟦ comp_valley v₁ v₂ ⟧ = ⟦ comp_valley w₁ w₂ ⟧,
  by calc
    ⟦ comp_valley v₁ v₂ ⟧ 
        = ⟦ comp_valley w₁ v₂ ⟧ : by { apply (dom_imp_post_comp _ _ _ dv₁)}
    ... = ⟦ comp_valley w₁ w₂ ⟧ : by { apply (dom_imp_pre_comp  _ _ _ dv₂)},
  
  have heq₂ : ⟦ comp_valley v₁' v₂' ⟧ = ⟦ comp_valley w₁ w₂ ⟧,
  by calc
    ⟦ comp_valley v₁' v₂' ⟧
        = ⟦ comp_valley w₁ v₂' ⟧ : by { apply (dom_imp_post_comp _ _ _ dv₁')}
    ... = ⟦ comp_valley w₁ w₂ ⟧  : by { apply (dom_imp_pre_comp  _ _ _ dv₂')},
  
  rw [heq₁, heq₂],
end

-- The axioms for the category

def hom_type (X Y : left_calculus C M) := quotient (valley_setoid X Y)

def id (X : left_calculus C M) := ⟦ id_valley X ⟧

def comp {X Y Z : left_calculus C M} (f : hom_type X Y) (g : hom_type Y Z) := 
  ⟦ comp_valley (quotient.out f) (quotient.out g) ⟧

lemma id_comp' (X Y : left_calculus C M) (f : hom_type X Y) :
  comp (id X) f = f :=
let g := comp (id X) f,
    f' := f.out,
    data : comp_data (id_valley X) f' :=
      { W := f'.obj.as,
        h := f'.f,
        u := (𝟙 f'.obj.as),
        hu := M.id,
        comm := have h : (id_valley X).s = 𝟙 X.as, from rfl,
          by {simp, rw h, simp},
      },
    g' := comp_valley_from_data (id_valley X) f' data in
begin
  change g = f,
  have h₁ : g = ⟦ comp_valley (id_valley X) f' ⟧, 
    by { apply comp_well_def, split, simp, refl, refl },
  have h₂ : ⟦ comp_valley (id_valley X) f' ⟧ = ⟦ comp_valley_from_data (id_valley X) f' data ⟧,
    from comp_independent_of_data _ _ _,
  rw [h₁, h₂],
  suffices : veq X Y g' f', by {
      apply quotient.mk_eq_iff_out.mpr,
      exact this,
  },
  use [f', 𝟙 f'.obj.as, 𝟙 f'.obj.as], simp,
  have hlemma : ∀ {X : C}, ∀ f : X ⟶ f'.obj.as, f ≫ 𝟙 f'.obj.as = f, by {intro f, simp},
  split,
  { have : g'.f = (𝟙 X.as) ≫ f'.f, by refl, rw this,
    simp,
    rw hlemma f'.f },
  { have : g'.s = f'.s ≫ (𝟙 f'.obj.as), by refl, rw this, 
    simp,
    rw hlemma f'.s},
end

lemma comp_id' (X Y : left_calculus C M) (f : hom_type X Y) :
  comp f (id Y) = f :=
let g := comp f (id Y),
    f' := f.out,
    data : comp_data f' (id_valley Y) :=
      { W := f'.obj.as,
        h := (𝟙 f'.obj.as),
        u := f'.s,
        hu := f'.qis,
        comm := have h : (id_valley Y).f = 𝟙 Y.as, from rfl,
          by {simp, rw h, simp},
      },
    g' := comp_valley_from_data f' (id_valley Y) data in
begin
  change g = f,
  have h₁ : g = ⟦ comp_valley f' (id_valley Y) ⟧, 
    by { apply comp_well_def, split, simp, simp, refl },
  have h₂ : ⟦ comp_valley f' (id_valley Y) ⟧ = ⟦ comp_valley_from_data f' (id_valley Y) data ⟧,
    from comp_independent_of_data _ _ _,
  rw [h₁, h₂],
  suffices : veq X Y g' f', by {
      apply quotient.mk_eq_iff_out.mpr,
      exact this,
  },
  use [f', 𝟙 f'.obj.as, 𝟙 f'.obj.as], simp,
  have hlemma : ∀ {X : C}, ∀ f : X ⟶ f'.obj.as, f ≫ 𝟙 f'.obj.as = f, by {intro f, simp},
  split,
  { have : g'.f = f'.f ≫ (𝟙 f'.obj.as), by refl, rw this,
    simp,
    rw hlemma f'.f },
  { have : g'.s = (𝟙 Y.as) ≫ f'.s, by refl, rw this, 
    simp,
    rw hlemma f'.s},
end

lemma assoc' {W X Y Z : left_calculus C M} (f : hom_type W X) (g : hom_type X Y) (h : hom_type Y Z) :
  comp (comp f g) h = comp f (comp g h) :=
let a := f.out,
    b := g.out,
    c := h.out in
begin
  rcases (M.ore b.f a.s a.qis) with ⟨Y'', f₁, s₁, hs₁, hc₁⟩,
  rcases (M.ore c.f b.s b.qis) with ⟨Z'', f₂, s₂, hs₂, hc₂⟩,
  rcases (M.ore f₂ s₁ hs₁)     with ⟨Z''', f₃, s₃, hs₃, hc₃⟩,

  let v : valley W Z := {
    obj := ⟨ Z''' ⟩,
    f   := a.f ≫ f₁ ≫ f₃,
    s   := c.s ≫ s₂ ≫ s₃,
    qis  := triple_comp M ⟨c.qis, hs₂, hs₃⟩,
  },

  let d₁ : comp_data a b := {
    W := Y'',
    h := f₁,
    u := s₁,
    hu := hs₁,
    comm := hc₁,
  },
  let d₂ : comp_data b c := {
    W := Z'',
    h := f₂,
    u := s₂,
    hu := hs₂,
    comm := hc₂,
  },

  let cab := comp_valley_from_data a b d₁,
  let cbc := comp_valley_from_data b c d₂,
  have h₁ : comp f g = ⟦ cab ⟧, by {apply comp_independent_of_data},
  have h₂ : comp g h = ⟦ cbc ⟧, by {apply comp_independent_of_data},
  rw [h₁, h₂],

  let d₃ : comp_data cab c := {
    W := Z''',
    h := f₃,
    u := s₂ ≫ s₃,
    hu := M.comp ⟨hs₂, hs₃⟩,
    comm := begin 
      have : cab.s = b.s ≫ s₁, by refl, 
      rw [this, category.assoc, ←hc₃, ←category.assoc, hc₂], 
      simp, 
    end,
  },
  let d₄ : comp_data a cbc := {
    W := Z''',
    h := f₁ ≫ f₃,
    u := s₃,
    hu := hs₃,
    comm := begin 
      rw [←category.assoc, ←hc₁, category.assoc, ←hc₃, ←category.assoc], 
      refl,
    end,
  },
  let ccabc := comp_valley_from_data cab c d₃,
  let cacbc := comp_valley_from_data a cbc d₄,
  
  have hcomp₁ : comp ⟦cab⟧ h = ⟦ ccabc ⟧, by calc
    comp ⟦cab⟧ h = ⟦comp_valley cab c⟧ : by {apply comp_well_def, simp}
    ... = ⟦ ccabc ⟧ : by {apply comp_independent_of_data},
  have hcomp₂ : comp f ⟦cbc⟧ = ⟦ cacbc ⟧, by calc
    comp f ⟦cbc⟧ = ⟦comp_valley a cbc⟧ : by {apply comp_well_def, simp}
    ... = ⟦ cacbc ⟧ : by {apply comp_independent_of_data},
  rw [hcomp₁, hcomp₂],

  clear hcomp₁, clear hcomp₂,

  apply quotient.eq.mpr,
  use [v, (𝟙 Z'''), (𝟙 Z''')],
  simp, 
  have hlemma : ∀ {X : C}, ∀ f : X ⟶ Z''', f ≫ 𝟙 Z''' = f, by {intro f, simp},
  repeat {rw hlemma}, split, 
    {rw ←category.assoc, refl},
  split,
    {refl},
  split,
    {refl},
    {rw ←category.assoc, refl}
end

-- Define the category structure

instance : category (left_calculus C M) :=
{ hom  := hom_type,
  id   := id,
  comp := λ _ _ _ f g, comp f g,
  id_comp' := id_comp',
  comp_id' := comp_id',
  assoc' := λ _ _ _ _, assoc',
}

end derived

end category_theory