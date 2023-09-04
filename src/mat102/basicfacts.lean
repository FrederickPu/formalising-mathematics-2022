import tactic
import data.real.basic

inductive exactlyone3 (P Q R : Prop) : Prop 
| hP : (P ∧ ¬ Q ∧ ¬ R) → exactlyone3
| hQ : (¬ P ∧ Q ∧ ¬ R) → exactlyone3
| hR : (¬ P ∧ ¬Q ∧ R) → exactlyone3


theorem exactlyone3.elim_p_q {P Q R : Prop} : exactlyone3 P Q R → P → Q → false
| (exactlyone3.hP h) := by {
  intros p q,
  simp [p, q] at h,
  exact h,
}
| (exactlyone3.hQ h) := by {
  intros p q,
  simp [p, q] at h,
  exact h,
}
| (exactlyone3.hR h) := by {
  intros p q,
  simp [p, q] at h,
  exact h,
}

theorem exactlyone3.elim_p_r {P Q R : Prop} : exactlyone3 P Q R → P → R → false
| (exactlyone3.hP h) := by {
  intros p r,
  simp [p, r] at h,
  exact h,
}
| (exactlyone3.hQ h) := by {
  intros p r,
  simp [p, r] at h,
  exact h,
}
| (exactlyone3.hR h) := by {
  intros p r,
  simp [p, r] at h,
  exact h,
}

-- chp 1.2
class basic (α : Type*) extends ring α, has_lt α :=
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

example  (α : Type*) [basic α] : ¬ ((1:α) < 0) := begin
intro h,
have := l1 (1 : α) 0 1 h h,
simp at this,
exact exactlyone3.elim_p_q (basic.basic1 (0:α) 1) this h,
end

-- we can't prove (1:α) ≠ (0:α) because the ring could be trivial

