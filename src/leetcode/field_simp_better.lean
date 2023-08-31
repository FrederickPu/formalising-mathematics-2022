import data.list.basic
import tactic 

open tactic expr

-- Check if an expression is a denominator (recursively defined for simplicity)
meta def find_denoms : expr → list expr
| `(has_inv.inv %%e) := [e]
| `(%%e1 = %%e2) := (find_denoms e1) ++ (find_denoms e2)
| `(%%e1 / %%e2) := [e2]
| `(%%e1 + %%e2) := (find_denoms e1) ++ (find_denoms e2)
| `(%%e1 * %%e2) := (find_denoms e1) ++ (find_denoms e2)
| _ := []

#eval tactic.trace $ find_denoms `(1/2 = 0)

meta def bruh : tactic (list expr) :=
do tgt ← target, 
return (find_denoms tgt)

meta def trace_b : tactic unit :=
do n ← bruh,
trace n

open tactic.interactive («suffices»)

meta def assert_denoms_nonzero : tactic unit :=
do tgt ← target, 
let denoms := find_denoms tgt,
denoms.mmap' (λ d, do «suffices» none ``(%%d≠0))

-- Apply the tactic to the current goal
example (a b c : ℤ) (h : 1/2 = 0) : 1/a+1/3=0 :=
begin
  trace_b,
  assert_denoms_nonzero,
end