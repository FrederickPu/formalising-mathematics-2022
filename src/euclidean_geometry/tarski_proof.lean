-- creating a type of proofs inside a tarski geometry
-- the goal is to create a clean interface for automatic proof search (not just rewrite search)

-- a term is either a statement of congruence or betweeness or equality
structure term_cong : Type :=
(aindex : ℕ)
(bindex : ℕ)
(cindex : ℕ)
(dindex : ℕ)

structure term_bet : Type :=
(xindex : ℕ)
(yindex : ℕ)
(zindex : ℕ)

structure term_eq: Type :=
(aindex : ℕ)
(bindex : ℕ)

inductive term : Type
| mk_bet (bet : term_bet) : term
| mk_cong (cong : term_cong) : term
| mk_eq (eq : term_eq) : term


-- a proof state consists of:
-- varindex is the number of free variables (a0 a1 a2 ... aindex)
-- a list of terms
structure proof_state : Type :=
(numvars: ℕ)
(numterms : ℕ)
(terms : array numterms term)

inductive inference : Type
| cong_refl (xi yi : ℕ) : inference -- indices of variables x and y
| cong_id (xi yi zi : ℕ) : inference
| cong_trans (xi yi zi ui vi wi : ℕ) (congxyzu congxyvw : ℕ) : inference -- indices variables and precedent terms
| bet_id (xi yi : ℕ) (betxyx : ℕ) : inference
| ax_pasch (xi yi zi ui vi : ℕ) (betxuz betyvz : ℕ): inference
| seg_con (xi yi ai bi : ℕ): inference

-- match statement simple example
-- def f (x : ℕ) : ℕ :=
-- match x with 
-- | m+1 := m
-- | 0 := 0
-- end

#check array.read
#check array.push_back
#check mk_array

def banana : ℕ → fin 10 :=
λ n, 
if h : n < 10 then ⟨n, h⟩ else 0 -- if there is a proof h that n < 10 ...

def is_cong (xi yi zi ui : ℕ) (t : term) : bool :=
match t with
| term.mk_bet (bet : term_bet) := ff
| term.mk_cong (cong : term_cong) := cong.aindex = xi ∧ cong.bindex = yi ∧ cong.cindex = zi ∧ cong.dindex = ui
| term.mk_eq (eq : term_eq) := ff
end

def is_eq (xi yi : ℕ) (t : term) : bool :=
match t with
| term.mk_bet (bet : term_bet) := ff
| term.mk_cong (cong : term_cong) := ff
| term.mk_eq (eq : term_eq) := eq.aindex = xi ∧ eq.bindex = yi
end

def is_bet (xi yi zi : ℕ) (t : term) : bool :=
match t with
| term.mk_bet (bet : term_bet) := term_bet.xindex = xi ∧ term_bet.yindex = yi ∧ term.zindex = zi
| term.mk_cong (cong : term_cong) := ff
| term.mk_eq (eq : term_eq) := ff
end

-- we need to include ff case for when the hypothesis don't line up
def apply_inference (ps : proof_state) (i : inference) : option proof_state :=
do
match i with
| inference.cong_refl xi yi := some ⟨ 
  ps.numvars, 
  ps.numterms + 1, 
  ps.terms.push_back (term.mk_cong ⟨xi, yi, yi, xi⟩)
  ⟩
| inference.cong_id xi yi zi := some ⟨
  ps.numvars, 
  ps.numterms + 1, 
  ps.terms.push_back (term.mk_cong ⟨xi, yi, zi, zi⟩) 
  ⟩
| inference.cong_trans xi yi zi ui vi wi congxyzu congxyvw := 
if h : congxyzu < ps.numterms 
then if is_cong xi yi zi ui (ps.terms.read ⟨congxyzu, h⟩)
     then some ⟨
      ps.numvars, 
      ps.numterms + 1, 
      ps.terms.push_back (term.mk_cong ⟨zi, ui, vi, wi⟩) 
      ⟩
     else none
else none
| inference.bet_id xi yi betxyx := 
if h : betxyx < ps.numterms
then if is_bet xi yi xi (ps.terms.read ⟨betxyx, h⟩)
     then some ⟨
      ps.numvars,
      ps.numterms + 1,
      ps.terms.push_back (term.mk_eq ⟨xi, yi⟩)
      ⟩
      else none
else none
| inference.ax_pasch xi yi zi ui vi betxuz betyvz := --  ∃ a, (H.B y a u ∧ H.B v a x)
if h : betxuz < ps.numterms ∧ betyvz < ps.numterms
then if is_bet xi ui zi (ps.terms.read ⟨betxuz, h.left⟩) ∧ is_bet yi vi zi (ps.terms.read ⟨betyvz, h.right⟩)
     then some ⟨
      ps.numvars + 1,
      ps.numterms + 2, 
      do 
        let temp := ps.terms.push_back (term.mk_bet ⟨yi, (ps.numvars + 1), ui⟩),
        temp.push_back (term.mk_bet ⟨vi, (ps.numvars + 1), xi⟩)
      ⟩
     else none
else none
| inference.seg_con xi yi ai bi := -- ∃z, H.B x y z ∧ H.cong y z a b
some ⟨
  ps.numvars + 1,
  ps.numterms + 2,
  do let temp := ps.terms.push_back (term.mk_bet ⟨xi, yi, (ps.numvars + 1)⟩),
  temp.push_back (term.mk_cong ⟨yi, (ps.numvars + 1), ai, bi⟩)
⟩
end

structure proof : Type :=
(initial_hyp : proof_state)
(length : ℕ)
(inferences : array length inference)

-- simple proof to Prop conversion test:
--
-- n : ℕ gets mapped to the proof that n * x = n*x 
-- ex 3 -> 3*x = 3*x
  -- def toProp (n : ℕ) := ∀x, n*x = n*x 

    --notice  this is a dependent type since output type depends on n
  -- def toPropProof (n : ℕ) : toProp n :=
  -- begin
  -- intro x,
  -- refl,
  -- end

-- now let's do it for the tarksi geometry
