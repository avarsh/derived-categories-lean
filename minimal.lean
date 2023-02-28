import data.int.basic

universe u

structure my_struct :=
  (f : ℤ → ℤ)

example : ∃ s : my_struct, s.g ∘ s.f = id :=
begin
  
end