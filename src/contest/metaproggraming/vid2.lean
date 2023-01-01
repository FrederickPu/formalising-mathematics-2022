import tactic
set_option pp.numerals false
set_option pp.generalized_field_notation false

-- all expressions have a normal form (canonical form)
def n : ℕ := 3 * 2
#reduce n

#reduce (show 2≤10, from dec_trivial)

/-
  #reduce is much slower but safer (kernel reduction)
  #eval is much faster but less safe (VM reduction)
  that being said, VM computation will never produce soundness errors
-/

-- in lean, programs must be well-founded (ie we must show that they will always terminate)
-- the meta keyword allows us to make functions that are *not safe* in this way.
meta def f : ℕ → ℕ
| n := if n = 1 then 1
else if n % 2 = 0 then f (n / 2)
else f (3*n+1)
-- fyi the above function f is actually the collatz conjecture!

#eval (list.iota 1000).map f