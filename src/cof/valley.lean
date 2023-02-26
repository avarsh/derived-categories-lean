import cof.basic

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

-- Define the left calculus of fractions for a left multiplicative system

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


lemma triple_comp {W X Y Z : C} (M : left_mult_sys S) {f₁ : W ⟶ X} {f₂ : X ⟶ Y} {f₃ : Y ⟶ Z} :
  S f₁ ∧ S f₂ ∧ S f₃ → S (f₁ ≫ f₂ ≫ f₃) := 
begin
  rintro ⟨ s₁, s₂, s₃ ⟩,
  have s₄ : S (f₂ ≫ f₃) := M.comp ⟨s₂, s₃⟩,
  exact M.comp ⟨s₁, s₄⟩  
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
  have ht : _ := M.cancel ⟨w.qis, hcancel⟩,
  rcases ht with ⟨ Z₂, t, ht₁, ht₂ ⟩,

  use Z₂, use u.f ≫ c₁ ≫ t, use v.s ≫ s₁ ≫ t,
  exact triple_comp M ⟨v.qis, hc₁, ht₁⟩,

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
  intros u v w,
  rintro ⟨v₁, ⟨auv, a, i, j, k, l⟩⟩, 
  rintro ⟨v₂, ⟨b, avw, i', j', k', l'⟩⟩,
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

end derived

end category_theory