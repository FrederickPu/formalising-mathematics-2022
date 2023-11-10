variables (P Q : Prop)
example : P ∧ Q → Q ∧ P := 
begin
intro h,
split,
exact h.right,
exact h.left,
end
example : 2 = 2 :=
begin
refl,
end
example : 2 = 2 :=
begin

end
example : 2 = 2 :=
begin

end