-- if two propositions are provable then they are equal
#check propext
example (P Q : Prop) : P → Q → P = Q := begin
intros  p q,
apply propext,
split,
exact λ _, q,
exact λ _, p,
end
