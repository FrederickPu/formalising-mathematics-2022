import data.real.irrational
import tactic

open classical

variables (P Q : Prop) 
example : P ∧ ¬ Q → P := begin
tauto,
end   

example :(P ∧ ¬ Q) → Q := begin
tauto,
end

example : (P → Q) ∧ (Q → P) := begin
tauto,
end 

example : (P ∧ ¬ P) → Q := begin
tauto,
end
example : (P ∧ Q) → P := begin
tauto,
end  

#check real.exists_floor
#check real.floor_ring
#check real.archimedean

#check λ x, ite (irrational x) 0 1