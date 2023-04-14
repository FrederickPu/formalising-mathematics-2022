import data.real.basic
import algebra.group.defs
import order

structure pre_tarski_geo (M α: Type)
[add_semigroup M] [linear_order M] [densely_ordered M] :=
(cong (a b c d : α) : Prop) -- ab ≅ bc
(B (x y z : α) : Prop) -- c is between a and b

structure tarski_geo (M α : Type)
[add_semigroup M] [linear_order M] [densely_ordered M]
 :=
(H : pre_tarski_geo M α)
(cong_refl (x y: α): H.cong x y y x)
(cong_id (x y z : α) : H.cong x y z z → x = y)
(cong_trans (x y z u v w: α) : H.cong x y z u ∧ H.cong x y v w → H.cong z u v w)

(bet_id (x y : α) : H.B x y x → x = y)
(ax_pasch (x y z u v : α) : (H.B x u z ∧ H.B y v z) → ∃ a, (H.B y a u ∧ H.B v a x))
(ax_cont (φ ψ : α → Prop): 
(∃ a : α, ∀ x, ∀y, ((φ x ∧ ψ y) → H.B a x y)) →  (∃ b,∀x,∀y,((φ(x) ∧ ψ(y)) → H.B x b y))
)-- axiom of continuity
(low_dim : ∃ a b c, ¬H.B a b c ∧ ¬ H.B b c a ∧ ¬ H.B c a b)
(cong_bet (x y z u v : α): 
(H.cong x u x v) ∧ (H.cong y u y v) ∧ (H.cong z u z v) ∧ (u ≠ v) → (H.B x y z ∨ H.B y z x ∨ H.B z x y))

(ax_eucA (x y z u v w : α): ((H.B x y w ∧  H.cong x y y w) ∧ (H.B x u v ∧ H.cong x u u v) ∧ (H.B y u z ∧  H.cong y u u z)) → H.cong y z v w) -- think of a parrallelagram
(five_seg (x y z u x' y' z' u' : α) :
(x ≠ y ∧ H.B x y z ∧ H.B x' y' z' ∧ H.cong x y x' y' ∧ H.cong y z y' z' ∧ H.cong x u x' u' ∧ H.cong y u y' u') → H.cong z u z' u')
(seg_con (x y a b : α): ∃z, H.B x y z ∧ H.cong y z a b)
-- congruence for triangles
-- def tarski_geo.cong' {M α : Type} [add_semigroup M] [linear_order M] [densely_ordered M] {T : tarski_geo M α}
-- (a b c a' b' c' : α) := 
-- T.H.cong a b a' b' ∧ T.H.cong b c b' c' ∧ T.H.cong a c a' c'



namespace tarski_geo

-- a term is either a statement of congruence or betweeness or equality

structure term_cong {M α : Type} [add_semigroup M] [linear_order M] [densely_ordered M] 
(T : tarski_geo M α) : Type :=
(aindex : ℕ)
(bindex : ℕ)
(cindex : ℕ)
(dindex : ℕ)

structure term_bet {M α : Type} [add_semigroup M] [linear_order M] [densely_ordered M] 
(T : tarski_geo M α) : Type :=
(xindex : ℕ)
(yindex : ℕ)
(zindex : ℕ)

structure term_eq {M α : Type} [add_semigroup M] [linear_order M] [densely_ordered M] 
(T : tarski_geo M α) : Type :=
(aindex : ℕ)
(bindex : ℕ)

inductive term {M α : Type} [add_semigroup M] [linear_order M] [densely_ordered M] 
(T : tarski_geo M α) : Type
| mk_bet (bet : term_bet T) : term
| mk_cong (cong : term_cong T) : term
| mk_eq (eq : term_eq T) : term


-- a proof state consists of:
-- varindex is the number of free variables (a0 a1 a2 ... aindex)
-- a list of terms
structure proof_state {M α : Type} [add_semigroup M] [linear_order M] [densely_ordered M] 
(T : tarski_geo M α) : Type :=
(varindex : ℕ) 
(terms : list (term T))

inductive inference {M α : Type} [add_semigroup M] [linear_order M] [densely_ordered M] 
(T : tarski_geo M α) : Type
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

-- we need to include ff case for when the hypothesis don't line up
def apply_inference {M α : Type} [add_semigroup M] [linear_order M] [densely_ordered M] 
(T : tarski_geo M α) (ps : proof_state T) (i : inference T) : proof_state T :=
do
let var_temp : ℕ × list (term T) :=
match i with
| inference.cong_refl xi yi := ⟨ps.varindex, [term.mk_cong ⟨xi, yi, yi, xi⟩]⟩
| inference.cong_id xi yi zi := ⟨ps.varindex, [term.mk_cong ⟨xi, yi, zi, zi⟩]⟩
| inference.cong_trans xi yi zi ui vi wi congxyzu congxyvw := ⟨ps.varindex, [term.mk_cong ⟨zi, ui, vi, wi⟩]⟩
| inference.bet_id xi yi betxyx := ⟨ps.varindex, [term.mk_eq ⟨xi, yi⟩]⟩
| inference.ax_pasch xi yi zi ui vi betxuz betyvz := ⟨ps.varindex + 1, [term.mk_bet ⟨yi, (ps.varindex + 1), ui⟩, term.mk_bet ⟨vi, (ps.varindex + 1), xi⟩]⟩ --  ∃ a, (H.B y a u ∧ H.B v a x)
| inference.seg_con xi yi ai bi := ⟨ps.varindex + 1, [term.mk_bet ⟨xi, yi, (ps.varindex + 1)⟩, term.mk_cong ⟨yi, (ps.varindex + 1), ai, bi⟩]⟩ -- ∃z, H.B x y z ∧ H.cong y z a b
end,
let var := var_temp.fst,
let temp := var_temp.snd,
⟨var, temp⟩

structure proof {M α : Type} [add_semigroup M] [linear_order M] [densely_ordered M] 
(T : tarski_geo M α) :=
(initial_hyp : proof_state T)
(inferences : list (inference T))

-- simple Prop & proof conversion test:
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


def cong' {M α : Type} [add_semigroup M] [linear_order M] [densely_ordered M] 
(T : tarski_geo M α) (a b c a' b' c' : α) := 
T.H.cong a b a' b' ∧ T.H.cong b c b' c' ∧ T.H.cong a c a' c'

variables {M α : Type} [add_semigroup M] [linear_order M] [densely_ordered M] {T : tarski_geo M α}

-- proving basic properties of congruency

theorem cong_refl' {x y : α} : T.H.cong x y x y :=
begin
apply T.cong_trans y x x y x y,
split;
exact T.cong_refl y x,
end

theorem cong_symm {x y a b : α} : T.H.cong x y a b → T.H.cong a b x y :=
begin
intro p,
apply T.cong_trans x y a b x y,
split,
exact p,
exact cong_refl',
end

theorem cong_trans' {x y z u v w : α} : T.H.cong x y z u → T.H.cong z u v w→ T.H.cong x y v w :=
begin
intros p q,
apply T.cong_trans z u x y v w,
split,
exact cong_symm p,
exact q,
end

-- proving basic properties of betweeness
theorem bet_triv {x y: α} : T.H.B x y y :=
begin
cases T.seg_con x y y y with y1,
have : y = y1, apply T.cong_id y y1 y,
exact h.right,
rw ← this at h,
exact h.left,
end
theorem bet_symm {x y z : α} : T.H.B x y z → T.H.B z y x:=
begin
intro h,
have : T.H.B y z z := bet_triv,
have : ∃ u, T.H.B y u y ∧ T.H.B z u x,
apply T.ax_pasch x y z,
tauto,

cases this with u,
have : y = u, apply T.bet_id, exact this_h.left,
rw this,
exact this_h.right,
end

theorem bet_triv' {x y : α} : T.H.B x x y :=
begin
apply bet_symm,
exact bet_triv,
end

-- exists perpindicular biscetor 
-- where perpindicular is defined using congruent rather than similar triangles
theorem exists_perp_bi : ∃ a b c d, cong' T a b d c b d :=
begin
simp only [cong'],

rcases T.low_dim with ⟨a, ⟨b, ⟨c, h⟩⟩⟩,

-- c ----> a ----> z ----> w
-- az and zw are both of length bc
cases T.seg_con c a b c with c1 hc1, 
cases T.seg_con a c1 b c with c2 hc2,

cases T.seg_con b a b c with b1 hb1, 
cases T.seg_con a b1 b c with b2 hb2,

have := T.ax_pasch c2 b2 a c1 b1,
have : ∃ (u : α), T.H.B b2 u c1 ∧ T.H.B b1 u c2,
apply T.ax_pasch _ _ a,
split,
apply bet_symm, exact hc2.left,
apply bet_symm, exact hb2.left,

cases this with u hu,
have : ∃ u1, T.H.B b2 u1 c2 ∧ T.H.B a u u1,
let X := λ p, ∃ q, T.H.B a q p ∧ T.H.B u q c2,
let Y := λ p, ∃ q, T.H.B a q p ∧ T.H.B u q b2,
have : ∃ (b : α), ∀ (x y : α), X x ∧ Y y → T.H.B x b y,
end

end tarski_geo