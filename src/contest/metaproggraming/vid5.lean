-- let's sit down and have some fun [0:00]

import tactic

open tactic expr

-- implementing *assump*

  -- version 0
  meta def test (hyp tgt : expr) : tactic bool :=
  do hyp_tp ← infer_type hyp,
    return (hyp_tp = tgt)

  meta def map_over_lc (tgt : expr) : list expr → tactic unit
  | [] := fail "ur wonky, nothing in context matches target"
  | (h::t) := 
    do is_match ← test h tgt,
      if is_match then exact h else map_over_lc t

  meta def assump : tactic unit :=
  do 
  tgt ← target,
  ctx ← local_context,
  map_over_lc tgt ctx

  -- version 1
  meta def test1 (hyp tgt : expr) : tactic unit :=
  do hyp_tp ← infer_type hyp,
    guard (hyp_tp = tgt)

  meta def map_over_lc1 (tgt : expr) : list expr → tactic unit
  | [] := fail "ur wonky, nothing in context matches target"
  | (h::t) := 
    (do test1 h tgt,
      exact h) <|> map_over_lc1 t
  meta def assump1 : tactic unit :=
  do 
  tgt ← target,
  ctx ← local_context,
  map_over_lc1 tgt ctx

  --version 2
  meta def test2 (hyp tgt : expr) : tactic unit :=
  do hyp_tp ← infer_type hyp,
    guard (hyp_tp = tgt),
    exact hyp

  meta def map_over_lc2(tgt : expr) : list expr → tactic unit
  | [] := fail "ur wonky, nothing in context matches target"
  | (h::t) := 
    (do test1 h tgt) <|> map_over_lc2 t
  meta def assump2 : tactic unit :=
  do 
  tgt ← target,
  ctx ← local_context,
  map_over_lc1 tgt ctx

  -- version 3
  #check @list.mfirst
  meta def test3 (hyp tgt : expr) : tactic unit :=
  do hyp_tp ← infer_type hyp,
    is_def_eq hyp_tp tgt,
    exact hyp
  meta def assump3 : tactic unit :=
  do 
  tgt ← target,
  ctx ← local_context,
  ctx.mfirst (λ e, test3 e tgt)


  example (A B C : Prop) (ha : A) (hb : B) (hc : C) : C :=
  by assump2

  example (n : ℕ) (hx : n + 0 = 5) : n = 5:=
  by assump2
  example (n : ℕ) (hx : n + 0 = 5) : n = 5:=
  by assump3

  -- version 4
  #check @list.mfirst
  meta def assump4 : tactic unit :=
  do ctx ← local_context,
    ctx.mfirst (λ e, exact e)

  -- version holy cow monad majggiic
  #check @list.mfirst
  meta def assump_holyflippingcow : tactic unit :=
  local_context >>= list.mfirst exact

-- add refls [17:23]
meta def add_single_refl (e : expr) : tactic unit :=
do tp ← infer_type e,
  guard (tp = `(ℕ)),
  pf ← mk_app `eq.refl [e],
  nm ← get_unused_name e.local_pp_name,
  note nm none pf,
  skip -- skip ends tactic with no sideeffects

meta def add_single_refl1 (e : expr) : tactic unit :=
do tp ← infer_type e,
  guard (tp = `(ℕ)),
  pf ← mk_app `eq.refl [e],
  nm ← get_unused_name `h,
  note nm none pf,
  skip -- skip ends tactic with no sideeffects

meta def add_refl : tactic unit :=
do ctx ← local_context,
ctx.mmap' (λ e, try (add_single_refl e))

example (a b c : ℕ) (ha : a = b) : true :=
by do add_refl

-- to expr [26:03]
meta def add_single_ge (e : expr) : tactic unit :=
do tp ← infer_type e,
  guard (tp = `(ℕ)),
  pf ← to_expr ``(not_lt_of_ge (nat.zero_le %%e)),
  nm ← get_unused_name e.local_pp_name,
  note nm none pf,
  skip -- skip ends tactic with no sideeffects

meta def add_ge : tactic unit :=
do ctx ← local_context,
ctx.mmap' (λ e, try (add_single_ge e))

example (a b c : ℕ) (ha : a = b) : true :=
by do add_ge