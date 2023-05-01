import tactic
import data.vector
import data.list.defs
-- creating a type of proofs inside a tarski geometry
-- the goal is to create a clean interface for automatic proof search (not just rewrite search)

-- a term is either a statement of congruence or betweeness or equality

set_option trace.eqn_compiler.elim_match true

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
| cong_refl (xyi : ℕ × ℕ) : inference -- indices of variables x and y
| cong_id (xyzi: ℕ × ℕ × ℕ) (congxyzz : ℕ) : inference
| cong_trans (xyzuvwi : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) (congxyzucongxyvw : ℕ × ℕ) : inference -- indices variables and precedent terms
| bet_id (xyi: ℕ × ℕ) (betxyx : ℕ) : inference
| ax_pasch (xyzuv : ℕ × ℕ × ℕ × ℕ × ℕ) (betxuzbetyvz : ℕ × ℕ): inference
| seg_con (xyab : ℕ × ℕ × ℕ × ℕ): inference

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
| term.mk_bet (bet : term_bet) := bet.xindex = xi ∧ bet.yindex = yi ∧ bet.zindex = zi
| term.mk_cong (cong : term_cong) := ff
| term.mk_eq (eq : term_eq) := ff
end

-- we need to include ff case for when the hypothesis don't line up
def apply_inference (ps : proof_state) (i : inference) : option proof_state :=
do
match i with
| inference.cong_refl xyi := some ⟨ 
  ps.numvars, 
  ps.numterms + 1, 
  match xyi with
  | (xi, yi) := ps.terms.push_back (term.mk_cong ⟨xi, yi, yi, xi⟩)
  end
  ⟩
| inference.cong_id xyzi congxyzz := 
match xyzi with
| (xi, (yi, zi)) := 
if h : congxyzz < ps.numterms
then if is_cong xi yi zi zi (ps.terms.read ⟨congxyzz, h⟩)
    then some ⟨
      ps.numvars, 
      ps.numterms + 1, 
      ps.terms.push_back (term.mk_cong ⟨xi, yi, zi, zi⟩) 
      ⟩
    else none
else none
end
| inference.cong_trans xyzuvwi congxyzucongxyvwi := 
match xyzuvwi, congxyzucongxyvwi with
  | (xi, (yi, (zi, (ui, (vi, wi))))), (congxyzu, congxyvw) :=
  if h : congxyzu < ps.numterms 
  then if is_cong xi yi zi ui (ps.terms.read ⟨congxyzu, h⟩)
      then some ⟨
        ps.numvars, 
        ps.numterms + 1, 
        ps.terms.push_back (term.mk_cong ⟨zi, ui, vi, wi⟩) 
        ⟩
      else none
  else none
  end
| inference.bet_id xyi betxyx := 
  match xyi with
  | (xi, yi) :=
  if h : betxyx < ps.numterms
  then if is_bet xi yi xi (ps.terms.read ⟨betxyx, h⟩)
      then some ⟨
        ps.numvars,
        ps.numterms + 1,
        ps.terms.push_back (term.mk_eq ⟨xi, yi⟩)
        ⟩
        else none
  else none
  end
| inference.ax_pasch xyzuvi betxuzbetyvz := --  ∃ a, (H.B y a u ∧ H.B v a x)
  match xyzuvi, betxuzbetyvz with 
  | (xi, (yi, (zi, (ui, vi)))), (betxuz, betyvz) :=
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
  end
| inference.seg_con xyabi := -- ∃z, H.B x y z ∧ H.cong y z a b
  match xyabi with
  | (xi, (yi, (ai, bi))) :=
  some ⟨
    ps.numvars + 1,
    ps.numterms + 2,
    do let temp := ps.terms.push_back (term.mk_bet ⟨xi, yi, (ps.numvars + 1)⟩),
    temp.push_back (term.mk_cong ⟨yi, (ps.numvars + 1), ai, bi⟩)
  ⟩
  end
end

structure proof : Type :=
(initial_hyp : proof_state)
(inferences : list inference)

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

def conclusion (initial : proof_state):  list inference → option proof_state
| list.nil := initial
| (list.cons (i: inference) (tl : list inference) ) := do
  match conclusion tl with
  | none := none
  | some (ps : proof_state) := apply_inference ps i
  end

-- note that (x : α) will always have a coexercion to (option α)
-- example : option ℕ := ↑2

-- let's test our code out
def thing : proof :=
{
  initial_hyp := ⟨2, 0, array.nil⟩,
  inferences := [inference.cong_refl (0, 1), inference.seg_con (0, 1, 0, 1)]
}

#eval has_repr.repr 2


def naming_convention : list string := ["a", "b", "c", "d", "x", "y", "z"]
#eval naming_convention.to_array

-- variable name assigned to a particular (natural number) variable index
def nname : ℕ → string := 
λ n, do
  let lookup := naming_convention.to_array,
  let len := naming_convention.length,
  if h : n < len then lookup.read ⟨n, h⟩
  else repr n

instance : has_repr term :=
{
  repr := λ t, 
  match t with 
  | term.mk_bet (bet : term_bet) := 
     "B" ++ " " ++ (nname bet.xindex) ++ " " ++ (nname bet.yindex) ++ " " ++ (nname bet.zindex)
  | term.mk_cong (cong : term_cong) :=
  (nname cong.aindex) ++ " " ++ (nname cong.bindex) ++ " ≅ " ++ (nname cong.cindex) ++ " " ++ (nname cong.dindex)
  | term.mk_eq (eq : term_eq) :=
  (nname eq.aindex) ++ " = " ++ (nname eq.bindex)
  end
}

def list.vars_repr : list string → string
| list.nil := ""
| (list.cons hd tl) :=  
if tl = list.nil then hd -- avoiding trailing comma "a, b,"
else hd ++  ", " ++ list.vars_repr tl

instance : has_repr proof_state :=
{
  repr := λ ps, ((list.range ps.numvars).map nname).vars_repr ++ " ⊢ " ++  (repr ps.terms)
}


-- we want to be able to generate a list of all pairs of (xi, yi) or a list of all (xi, yi, zi) in order to iterate over all possible inferences of a given kind (ex bet_id)
-- let's create a infix macro for list.product
infixr ` × `:35 := list.product

-- all inferences that can be applied to a given proof state
-- some of them may be invalid (ie apply_inference ps i = none)
def proof_state.infs (ps : proof_state) : list inference := 
  do 
  let varsi := list.range ps.numvars,
  let termsi := list.range ps.numterms,

  let cong_refl : list inference := (varsi × termsi).map (λ v : ℕ × ℕ, inference.cong_refl v),
  let cong_trans : list inference := 
    ((varsi × varsi × varsi × varsi × varsi × varsi) × (termsi × termsi)).map 
          (λ v : (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ), inference.cong_trans v.fst v.snd),
  let bet_id : list inference := 
    ((varsi × varsi) × (termsi)).map
          (λ v : (ℕ × ℕ) × ℕ, inference.bet_id v.fst v.snd),
  let ax_pasch : list inference :=
    ((varsi × varsi × varsi × varsi × varsi) × (termsi × termsi)).map
          (λ v : (ℕ × ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ), inference.ax_pasch v.fst v.snd),
  let seg_con : list inference :=
    (varsi × varsi × varsi × varsi).map
          (λ v : (ℕ × ℕ × ℕ × ℕ), inference.seg_con v.fst),

  cong_refl ++ cong_trans ++ bet_id ++ ax_pasch ++ seg_con

-- get all inferences that are actually valid
-- are not `none`
def proof_state.valid_infs (ps : proof_state) : list inference :=
  ps.infs.filter (λ i : inference, ! option.is_none (apply_inference ps i))

#eval conclusion thing.initial_hyp thing.inferences

def inference.repr : inference → string
| (inference.cong_refl xyi) := "cong_refl"
| (inference.cong_id xyzi congxyzz) := "cong_id"
| (inference.cong_trans xyzuvwi congxyzucongxyvw) := "cong_trans"
| (inference.bet_id xyi betxyx) := "bet_id"
| (inference.ax_pasch xyzuv betxuzbetyvz) := "ax_pasch"
| (inference.seg_con xyab) := "seg_con"
instance : has_repr inference :=
{
  repr := inference.repr
}

def last {α : Type} [inhabited α] : list α →  α
| list.nil := default α
| (list.cons hd tl) := hd

instance : inhabited inference :=
{
  default := inference.cong_refl ⟨0, 0⟩
}

def to_proof_state : option proof_state → proof_state
| none := ⟨0, 0, array.nil⟩
| (some val) := val

-- now let's begin with the actual search algorithm
-- we need a search state to encode local variables because lean is a functional proggraming language
structure search_state (α : Type):= 
(parent : α → option α)
(visited : α → bool)

-- def search (hyp : proof_state) (target : proof_state) : search_state proof_state → list inference
-- | (search_state.mk parent visited) := _
-- :=
-- do
-- let l search_state × bool

#eval [1, 2, 3] ++ [2, 3, 4]