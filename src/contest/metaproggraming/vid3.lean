/-
  The tactic monad allows us to modify global state

  More specifically, tactic ℕ is a function that:
   takes in a tactic state and produces a new tactic state 
    along with something of type ℕ
  
  roughly speaking. tactic ℕ : tacticstate ⨯ ℕ 

  *tactic unit* basically returns a tactic state since *unit* is negligable
  tactic unit : tacticstate ⨯ unit
-/
import tactic

open tactic

-- simple tactics [2:34]

-- return
meta def make_a_nat : tactic ℕ :=
return 14

-- trace
-- use @ to see full type
#check @tactic.trace

-- do notation [4:41]
meta def trace_a_nat : tactic unit :=
do n ← make_a_nat,
  trace n

-- running tactics [6:35]
run_cmd trace_a_nat

example (a b c : ℤ) : false :=
begin
  trace_a_nat,
end

example (a b c : ℤ) : false :=
by do trace_a_nat

-- seeing proof/tactic state (trace state) [8:30]
example (a b c : ℤ) : false :=
by do trace_state

-- inspecting a tactic state cont. [9:20]
meta def inspect : tactic unit :=
do t ← target,
  trace t,
  a_expr ← get_local `a,
  trace (expr.to_raw_fmt a_expr),
  a_type ← infer_type a_expr,
  trace a_type,
  ctx ← local_context,
  trace ctx
example (a b c : ℤ) : a = b :=
by do inspect

-- oh fuck, what if there's no a? [14:41]
example (b c : ℤ) : c = b :=
by do inspect

-- or else combinators (conditionals) [15:53]
meta def inspect_1 : tactic unit :=
do t ← target,
  trace t,
  a_expr ← get_local `a <|> fail "oops no a",
  a_expr ← get_local `a <|> return `(0),

  trace (expr.to_raw_fmt a_expr)

-- what if there's no `a? [14:41]
example (b c : ℤ) : c = b :=
by do inspect_1

-- just a nat [17:47]
meta def just_a_nat : tactic unit :=
do t ← target,
  trace t,
  new_nat ← 40,
  trace new_nat

meta def just_a_nat' : tactic unit :=
do t ← target,
  trace t,
  new_nat ← return 40,
  trace new_nat

meta def just_a_nat'' : tactic unit :=
do t ← target,
  trace t,
  let new_nat := 40,
  trace new_nat

-- looping [19:28]
#check @list.mmap -- runs a function over a list

meta def looping : tactic unit :=
do t ← target,
  ctx ← local_context,
  ctx' ← ctx.mmap(λ e, infer_type e),
  trace ctx,
  ctx.mmap' (λ e, do tp ← infer_type e, trace tp)
example (a b c : ℤ) : a = b :=
by do looping

#check @list.mmap' -- operates over a list but does a sideeffect