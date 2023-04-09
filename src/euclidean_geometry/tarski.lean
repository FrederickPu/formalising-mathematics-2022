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
(ax_pasch (x y z u v a : α) : (H.B x u z ∧ H.B y v z) → ∃ a, (H.B y a u ∧ H.B v a x))
(ax_cont (φ ψ : α → Prop): 
∃ a : α, (∀ x, ∀y, ((φ x ∧ ψ y) → H.B a x y) →  (∃ b,∀x,∀y,((φ(x) ∧ ψ(y)) → H.B x b y))) 
)-- axiom of continuity
(low_dim : ∃ a b c, ¬H.B a b c ∧ ¬ H.B b c a ∧ ¬ H.B c a b)
(cong_bet (x y z u v : α): 
(H.cong x u x v) ∧ (H.cong y u y v) ∧ (H.cong z u z v) ∧ (u ≠ v) → (H.B x y z ∨ H.B y z x ∨ H.B z x y))

(ax_eucA (x y z u v w : α): ((H.B x y w ∧  H.cong x y y w) ∧ (H.B x u v ∧ H.cong x u u v) ∧ (H.B y u z ∧  H.cong y u u z)) → H.cong y z v w) -- think of a parrallelagram
(five_seg (x y z u x' y' z' u' : α) :
(x ≠ y ∧ H.B x y z ∧ H.B x' y' z' ∧ H.cong x y x' y' ∧ H.cong y z y' z' ∧ H.cong x u x' u' ∧ H.cong y u y' u') → H.cong z u z' u')
(seg_con (x y a b : α): ∃z, H.B x y z ∧ H.cong x y a b)
