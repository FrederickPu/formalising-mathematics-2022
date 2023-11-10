import data.real.basic
import system.io

import data.buffer.parser
import tactic

lemma my_lemma : true := trivial

example (α β γ : Type*) (f : α → β) (g : β → γ) : f.injective → g.injective → (g ∘ f).injective := begin
intros hf hg,
intros x y,
intro h,
exact hf (hg h),
end

constant inc : ((ℝ → ℝ) → Prop)
constant dec : ((ℝ → ℝ) → Prop)
constant continuous : ((ℝ → ℝ) → Prop)
axiom not_inc_dec (f : ℝ → ℝ) : ¬ (inc f ∧ dec f)
axiom cont_imp (f : ℝ → ℝ) : (continuous f) → inc f ∨ dec f
axiom inc_dec (f g : ℝ → ℝ) : inc f → dec g → dec (f ∘ g)
axiom dec_inc (f g : ℝ → ℝ) : dec f → inc g → dec (f ∘ g)
axiom dec_dec (f g : ℝ → ℝ) :  dec f → dec g → inc (f ∘ g)
axiom inc_inc (f g : ℝ → ℝ) : inc f → inc g → inc (f ∘ g)

example (f g : ℝ → ℝ) (hf : continuous f) (hg : continuous g) (hg' : dec g) : 
  f ∘ f ≠ g := begin
intro h,
have l1 : f ∘ (f ∘ f) = f ∘ g,
exact congr_arg (function.comp f) h,

have := cont_imp f hf,
cases this,
{
  have w := inc_inc f _ this (inc_inc f f this this),
  have := inc_dec f g this hg',
  rw l1 at w,
  exact not_inc_dec _ ⟨w, this⟩,
},
{
  have w := inc_dec (f ∘ f) f (dec_dec f f this this) this,
  have := dec_dec f g this hg',
  rw l1 at w,
  exact not_inc_dec _ ⟨this, w⟩,
},
end 


-- Define a tactic to trace the proof state
meta def trace_proof : tactic unit :=
do
  goal ← tactic.target,
  tactic.trace format!"Current goal: {goal}",
  tactic.trace "Proof state:",
  local_context ← tactic.local_context, 
  local_context.mmap' $ λ h,
    do {
      declaration ← tactic.get_decl h.local_pp_name,
      tactic.trace format!"Definition of {h.local_pp_name}: {declaration}",
      -- Optionally, you can also check the type or reduce the expression using #check or #reduce:
      
      h_type ← tactic.infer_type h,
      pp_type ← tactic.pp h_type,
      tactic.trace format!"{h} : {h_type} aka, {pp_type}"
    },
  tactic.trace "-------------------".

-- Example usage
theorem example_lemma : ∀ (n : ℕ), n = n :=
begin
  intros n,
  trace_proof, -- Call your custom tactic
  -- Continue with your proof
end

meta def extract_just : expr → tactic (expr × list expr) 
| (expr.app f arg) := do
  (outer, args) ← extract_just f,
  return (outer, args ++ [arg])
| e := return (e, [])

meta def justification_from_expr : expr → string
| `(not_inc_dec %%f) := to_string format!"a function cannot be both increasing and decreasing (in this case ${f}$)"
| `(false.elim) := to_string format!"anything is true if the premise is impossible"
| _ := "unknown justification"

meta def isProp : expr → tactic bool := λ e, 
do
e_type ← tactic.infer_type e,
return $ e_type = `(Prop)
open expr
namespace tactic.interactive

setup_tactic_parser

meta def extractPremise : tactic expr :=
do
  -- Introduce a hypothesis using `tactic.interactive.intro`
  tactic.intros,
  -- Get the list of hypotheses
  hypotheses ← tactic.local_context,
  -- Pattern match on the first hypothesis
  if h : hypotheses = list.nil then do 
  return $ expr.const `empty []
  else do
    pp ← tactic.get_local_type (hypotheses.last h).local_pp_name,
    return pp


meta def my_intro_aux (h : name) : tactic unit :=
do 
tactic.interactive.intro h,
prem ← extractPremise,
pp ← tactic.pp prem,
isprop ← isProp prem,
if isprop then
tactic.trace format!"Assume {pp} {prem} ({h})"
else
tactic.trace format!"Let {h} be of type {pp} {prem} be arbitrary"
-- Define a user command that uses the custom `my_intro` tactic
meta def my_intro (h : parse ident) : tactic unit :=
do
my_intro_aux h

meta def my_apply (h : parse texpr) : tactic unit :=
do
l ← tactic.to_expr h, 
⟨a, b⟩ ← extract_just l, 
a' ← tactic.pp a,
b' ← tactic.pp b,
tactic.trace format!"Using {a'} with {b'}",
tactic.interactive.apply h

end tactic.interactive

-- TODO :: store export a list and intros and applys, exacts
-- then have a dictionary mapping lemmas to natural language explanations.
-- postprocess using GPT models such as LLAMA
example (f g : ℝ → ℝ) (hf : continuous f) (hg : continuous g) (hg' : dec g) : 
  f ∘ f ≠ g := 
begin
my_intro u,
my_apply false.elim,
my_apply not_inc_dec f,

end 
