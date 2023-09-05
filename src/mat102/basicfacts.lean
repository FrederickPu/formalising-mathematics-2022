import tactic
import data.real.basic

inductive exactlyone3 (P Q R : Prop) : Prop 
| hP : (P ∧ ¬ Q ∧ ¬ R) → exactlyone3
| hQ : (¬ P ∧ Q ∧ ¬ R) → exactlyone3
| hR : (¬ P ∧ ¬Q ∧ R) → exactlyone3

-- proves basic facts about exactlyone3 (and possibly other custom proposition combinators)
meta def kill : tactic unit := 
do 
`[
  intro h,
  cases h;
  simp [h]
]

theorem exactlyone3.elim_p_q {P Q R : Prop} : exactlyone3 P Q R → P → Q → false :=
by kill

theorem exactlyone3.elim_p_r {P Q R : Prop} : exactlyone3 P Q R → P → R → false :=
by kill

theorem exactlyone3.elim_nq_nr {P Q R : Prop} : exactlyone3 P Q R → ¬ Q → ¬ R → P := 
by kill

-- chp 1.2
class basic (α : Type*) extends ring α, has_lt α, nontrivial α :=
(basic1 (x y : α) : exactlyone3 (x < y) (y < x) (x = y))
(basic2 (x y z : α) : x < y → y < z → x < z)
(basic3 (x y z: α) : x < y → x + z < y + z)
(basic4 (x y z : α) : z > 0 → x < y → x*z < y*z)

theorem l1 {α : Type*} [basic α] (x y z : α) : z < 0 → x < y → x*z > y*z := begin
intros p q,
have := basic.basic3 z 0 (-z) p,
simp at this,
have := basic.basic4 x y (-z) this q,
have := basic.basic3 (x*-z) (y*-z) (x*z) this,
have := basic.basic3 _ _ (y*z) this,
simp at this,
exact this,
end

theorem basic.not_one_lt_zero {α : Type*} [basic α] : ¬ ((1:α) < 0) := begin
intro h,
have := l1 (1 : α) 0 1 h h,
simp at this,
exact exactlyone3.elim_p_q (basic.basic1 (0:α) 1) this h,
end

theorem basic.one_ne_zero {α : Type*} [basic α] : (1 : α) ≠ 0 := begin
intro h,
have crux : ∀ x : α, x = 0,
{
intro x,
have : x*1 = x, simp,
simp [h] at this,
exact this.symm,
},
rcases @nontrivial.exists_pair_ne α _ with ⟨x, y, p⟩,
simp [crux x, crux y] at p,
exact p,
end

theorem basic.zero_lt_one {α : Type*} [basic α] : 0 < (1 : α) := begin
apply exactlyone3.elim_nq_nr (basic.basic1 (0:α) (1:α)),
exact basic.not_one_lt_zero,
exact basic.one_ne_zero.symm,
end