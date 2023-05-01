import tactic

#check empty

#check bin_tree empty



inductive paren
| op : paren
| cl : paren
| none : paren

instance : has_repr paren :=
{
  repr := λ p, match p with 
  | paren.op := "("
  | paren.cl := ")"
  | paren.none := ""
  end
}

open unit paren

def list.push : char → list char → list char :=
list.cons

def list.pop : list char → (option char × list char) :=
λ l,
match l with 
| list.cons p l := ⟨some p, l⟩
| list.nil := ⟨none, list.nil⟩
end


def f (s : string) : ℕ × list char → list char :=
λ state, 
do
let (i, stack) := state,
if h : i < s.to_list.length then
  do
  let (temp, stack') := stack.pop,
  if s.to_list.to_array.read ⟨i, h⟩ = ')' ∧ temp = '(' then stack' 
  else stack.push (s.to_list.to_array.read ⟨i, h⟩)
else []

def f' (s : string) : ℕ × list char → ℕ × list char  :=
λ state,
⟨state.fst + 1, f s state⟩ 


def string.valid_aux (s : string) : ℕ × list char :=
do
let n := s.to_list.length,
(f' s)^[n] ⟨0, []⟩

def string.valid (s : string) : bool :=
do
if (s.valid_aux).snd = [] then tt else ff

-- the type of all valid parenthesis arrangments
inductive valid_paren : Type
| nil : valid_paren -- ""
| nest : valid_paren → valid_paren -- ex: nest ()() = (()())
| concat : valid_paren → valid_paren → valid_paren -- ex: (()()) ++ ()() = (()())()()

open valid_paren

def valid_paren.repr : valid_paren → string
| nil := ""
| (nest v) := "(" ++ v.repr ++ ")"
| (concat v1 v2) := v1.repr ++ v2.repr


instance : has_repr valid_paren :=
{
  repr := valid_paren.repr
}


def f_cert (s : string) : ℕ × list char × valid_paren × valid_paren → list char × valid_paren × valid_paren :=
λ state, 
do
let (i, stack, vglob, vtemp) := state,
if h : i < s.to_list.length then
  do
  let (temp, stack') := stack.pop,
  if s.to_list.to_array.read ⟨i, h⟩ = ')' ∧ temp = '(' then 
    if i > 0 ∧ s.to_list.to_array.read ⟨i - 1, by linarith [nat.sub_le i 1]⟩ = '('
      then ⟨stack', concat vtemp (nest nil), nil⟩  -- no level shift
      else ⟨stack', concat vglob (nest vtemp), nil⟩ -- go up a level
  else ⟨stack.push (s.to_list.to_array.read ⟨i, h⟩), vglob, vtemp⟩
else ⟨[], nil, nil⟩

def f'_cert (s : string) : ℕ × list char × valid_paren × valid_paren → ℕ × list char × valid_paren × valid_paren :=
λ state,
⟨state.fst + 1, f_cert s state⟩ 

def string.valid_aux_cert (s : string) : ℕ × list char × valid_paren × valid_paren :=
do
let n := s.to_list.length,
(f'_cert s)^[n] ⟨0, [], nil, nil⟩

def string.valid_cert (s : string) : bool × valid_paren  :=
do
let (i, l, v, v1) := s.valid_aux_cert,
if l = [] then ⟨tt, v1⟩ else ⟨ff, v1⟩

#eval (string.valid_cert "(())(())").snd