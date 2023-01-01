-- interactive tactics [1:00]

import tactic

open tactic expr

meta def add_nonneg_proof_aux (n : expr) (h : option name) : tactic unit :=
do pf ← mk_app `nat.zero_le [n],
nm ← get_unused_name,
note (h.get_or_else nm) none pf,
skip

namespace tactic
namespace interactive

setup_tactic_parser

-- question mark is notation for optional (special for interactive mode)
meta def add_nonneg_proof (n : parse parser.pexpr) (h : parse ident?):
tactic unit :=
do n ← to_expr n,
add_nonneg_proof_aux n h

meta def add_nonneg_proofs (l : parse pexpr_list) : tactic unit :=
do j ← l.mmap to_expr,
j.mmap' (λ e, add_nonneg_proof_aux e none)

end interactive
end tactic

meta def split_clone : tactic unit:=
do split, intro `banana,
skip

example (n : ℕ) : true :=
begin
  add_nonneg_proof 55 hx,
  add_nonneg_proofs [n+n+n, 2*n^2],
  trivial,
end


-- pattern matching[12:45]
meta def mk_list : tactic (list ℕ) :=
return [1, 4,6]

run_cmd do
  [a, b, c] ← mk_list,
  trace b

-- metavariables and multiple goals [15:00]
example : true ∧ true := 
by do
  split, gs ← get_goals, gs.mmap'(λ e, trace e.to_raw_fmt)

variables (P Q : Prop)
example : (P → Q) ∧ Q :=
begin
split_clone,
end