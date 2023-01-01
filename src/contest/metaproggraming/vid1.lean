import tactic

-- lean can be thought of in two ways: a *proggraming language* and a *type checker*

/- 
  proofs are functions that pass a specific type-check (produce a proof term)
  lean uses elaboration to fill in implicit type information

  in this sense lean is a *type checker*
-/
lemma my_lemma : ∀ n : ℕ, n ≥ 0 :=
λ n, nat.zero_le n

/- 
  tactics within the begin-end block are instructions for consttructing a proof term
  the proof script is called a tactic state (inside the begin-end block)

  the begin-end (in blue) takes a tactic state and produces a proof term
  (it follows the instructions to construct a proof term)
-/
-- in this sense lean is a *proggramming language*
lemma my_lemma2 : ∀ n : ℕ, n ≥ 0 :=
begin
  intro n,
  apply nat.zero_le,
end

-- tactics don't just produces expressions (eg. proof terms) but are also themselves lean expressions.
-- the proofs script for *my_lemma2* has type "tactic unit"
#check `[intro, apply nat.zero_le]

-- note: `[] tells lean to parse the contents as an interactive tactic.
