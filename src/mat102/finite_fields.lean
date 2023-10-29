import data.real.basic

inductive F4
| zero
| one
| a
| b

-- S × {0}
-- S × S
-- (a, b) "=" a + bi
-- (a, b) + (c, d) = (a+c, b+d)
-- (a, b) ⬝ (c, d) = (ac - bd, ac + bd)
-- i = (0, 1)
-- i ⬝ i = (0, 1)(0, 1) = (0 - 1, 0 + 0) = (-1, 0)

-- F₄
-- {(0, 0), (1, 1), (0, 1), (1, 0)}
-- {0, 1, 1 + i, i}
-- (1, 1)(1, 1) = (0, 1+1) = (0, 0)
-- (1, 1) = (0, 0)
-- i = 1
-- i + 1 = 0
-- i = -1 = 1

instance : has_zero F4 := ⟨F4.zero⟩
instance : has_one F4 := ⟨F4.one⟩


instance : has_repr F4 := {
  repr := λ x, F4.cases_on x "0" "1" "a" "b" 
}

-- field with specific elements designated to be one and zero
class MyField (F : Type*) [has_zero F] [has_one F] extends has_add F, has_mul F, has_inv F, has_neg F :=
(nontrivial : (0:F) ≠ 1)
(mul_assoc (a b c : F) : a * (b*c) = (a*b)*c)
(add_assoc (a b c : F) : a + (b + c) = (a + b) + c)
(mul_comm (a b : F) : a * b = b * a)
(add_comm (a b : F) : a + b = b + a)
(add_zero (a : F) : a + 0 = a)
(mul_one (a : F) : a * 1 = a)
(mul_inv (a : F) : a ≠ 0 → a * a⁻¹ = 1)
(add_neg (a : F) : a + (-a) = 0)
(distrib (a b c : F) : a*(b+c) = a*b + a*c)
(inv_zero : (0 : F)⁻¹ = 0)

namespace MyField

variables {F : Type*} [has_zero F] [has_one F] [MyField F]

-- Q4
theorem mul_canc (a b c : F) : a ≠ 0 → a*b = a*c → b = c  := begin
intro ha,
intro h,
-- only rewrite LHS 
-- basically emulating the equation chain proofs mat102 likes so much
conv
{
  to_lhs,
  rw ← mul_one b,
  rw ← mul_inv a ha,
  rw mul_assoc,
  rw mul_comm b a,
  rw h,
  rw mul_comm _ a⁻¹,
  rw mul_assoc,
  rw mul_comm _ a,
  rw mul_inv _ ha,
  rw mul_comm,
  rw mul_one,
},
end

--Q5
lemma zero_unique (a b : F) :a + b = a → b = 0 := begin
intro h,
-- again another equality chain (left to right)
conv {
  to_lhs,
  rw ← add_zero b,
  rw ← add_neg a,
  rw add_assoc,
  rw add_comm b a,
  rw h,
  rw add_neg,
},
end
lemma neg_unique (a b : F) : a + b = 0 → b = -a := begin
intro h,
conv {
  to_lhs,
  rw ← add_zero b,
  rw ← add_neg a,
  rw add_assoc,
  rw add_comm b a,
  rw h,
  rw add_comm,
  rw add_zero, 
},
end
theorem one_mul_zero : (1:F) * 0 = 0 := begin
have : (1:F) + (1*0) = 1,
have : (1:F)*1 + (1*0) = 1 + (1*0), rw mul_one, 
rw ← this,
rw ← distrib,
rw add_zero,
rw mul_one,

apply zero_unique (1:F) (1*0),
exact this,
end

theorem zero_mul_zero : (0 : F) * 0 = 0  := begin
apply zero_unique (0*1:F),
conv {
  to_lhs,
  rw ← distrib,
  rw add_zero,
},
end

theorem mul_zero (a : F) : a * 0 = 0 := begin
have l : -a*0 = -(a*0),
apply neg_unique,
conv {
  to_lhs,
  rw mul_comm a 0, rw mul_comm (-a) 0,
  rw ← distrib,
  rw add_neg,
  rw zero_mul_zero,
},
rw ← add_zero (a*0),
have : a * 0 + 0 = a*0 + (a*0 + -(a*0)),
rw add_neg,

conv {
to_lhs,
rw this,
rw ← l,
rw add_assoc,
rw ← distrib,
rw add_zero,
rw [mul_comm a 0, mul_comm (-a) 0],
rw ← distrib,
rw add_neg,
rw zero_mul_zero,
},
end

#check nat.succ_ne_self
@[simp]
lemma zero_def : F4.zero = 0 := refl 0
@[simp]
lemma one_def : F4.one = 1 := refl 1
#check field

lemma wei (a b : F) (ha : a ≠ 0): a*b = a → b = 1 := begin
intro h,
  have := congr_arg (has_mul.mul a⁻¹) h,
  rw [mul_assoc, mul_comm _ a, mul_inv a ha] at this,
  simp [mul_comm (1:F), mul_one] at this,
  exact this,
end
theorem mul_a_b [MyField F4]: F4.a*F4.b = 1 := begin
have ha : F4.a ≠ F4.zero := λ h, F4.no_confusion h,
cases h :  (F4.a*F4.b),
{
simp at h,
have : F4.a⁻¹*(F4.a*F4.b) = F4.a⁻¹*0,
exact congr_arg (has_mul.mul F4.a⁻¹) h,
rw [mul_assoc, mul_comm F4.a⁻¹ F4.a, mul_inv F4.a ha] at this,
rw [← mul_comm _ (1:F4), mul_zero, mul_one] at this,
exact F4.no_confusion this,
},

refl,
exact F4.no_confusion (wei F4.a F4.b (λ x, F4.no_confusion x) h),
{
  rw mul_comm F4.a F4.b at h,
  have := wei F4.b F4.a (λx, F4.no_confusion x) h,
  exact F4.no_confusion this,
},
end

theorem a_sq [MyField F4] : F4.a*F4.a = F4.b := begin
cases h : (F4.a * F4.a),
{
have := congr_arg (has_mul.mul F4.a⁻¹) h,
simp at this,
rw [mul_assoc, mul_comm F4.a⁻¹, mul_inv F4.a (λ x, F4.no_confusion x), mul_zero] at this,
simp [mul_comm, mul_one] at this,
exact F4.no_confusion this,
},
{
  have : (F4.a * F4.a) * F4.b = F4.one * F4.b,
  exact congr_fun (congr_arg has_mul.mul h) F4.b,
  
  rw ← mul_assoc at this,
  rw mul_a_b at this,
  simp [mul_one, mul_comm] at this,
  apply false.elim,
  exact this,
},
{
  have := wei F4.a F4.a (λ x, F4.no_confusion x) h,
  exact F4.no_confusion this,
},
refl,
end
theorem b_sq [MyField F4] : F4.b * F4.b = F4.a := begin
have := a_sq,
have : (F4.a * F4.a)*F4.b = F4.b * F4.b,
exact congr_fun (congr_arg has_mul.mul this) F4.b,

rw ← mul_assoc at this,
rw mul_a_b at this,
rw mul_one at this,
exact this.symm,
end

theorem a_cube [MyField F4]: F4.a*F4.a*F4.a = 1 := begin
rw ← mul_assoc,
rw a_sq,
rw mul_a_b,
end

theorem b_cube [MyField F4] : F4.b * F4.b * F4.b = 1 := begin
rw b_sq,
rw mul_a_b,
end

lemma left_distrib [MyField F] (a b c : F) : (a+ b)*c = a*c + b*c := begin
rw mul_comm,
rw distrib,
rw mul_comm c a, rw mul_comm b c,
end
example [MyField F4] : 1 + 1 = F4.a → F4.a*(F4.a + -1) = 0 := begin
intro h,
have : (1 + 1) * (1+1) = F4.a*F4.a,
exact congr (congr_arg has_mul.mul h) h,

have l : ((1:F4) + 1) * (1 + 1) = (1 + 1) + (1 + 1),
conv {
  to_lhs,
  rw distrib,
  rw left_distrib,
  simp [mul_one],
},
rw l at this,
rw h at this,
end

instance [MyField F4] : field F4 := {
  add := ‹MyField F4›.add,
  add_assoc := λ a b c, (‹MyField F4›.add_assoc a b c).symm,
  zero := 0, -- inherited from F4
  zero_add := begin
    intro a,
    rw add_comm,
    exact add_zero a,
  end,
  add_zero := add_zero,
  neg := λ a, -a, 
  add_left_neg := begin
    intro a,
    have : (-a) + a = 0,
      rw add_comm,
      exact add_neg a,
    exact this,
  end,
  add_comm := add_comm,
  one := 1,
  mul := λ a b, a*b,
  mul_assoc := λ a b c, (‹MyField F4›.mul_assoc a b c).symm,
  one_mul := begin
    intro a,
    rw mul_comm,
    exact mul_one a,
  end,
  mul_one := mul_one,
  left_distrib := distrib,
  right_distrib := begin
  intros a b c,
  rw [mul_comm (a + b) c, mul_comm a c, mul_comm b c],
  exact distrib c a b,
  end,
  mul_comm := mul_comm,
  inv := λ a, a⁻¹,
  exists_pair_ne := begin
  use 0, use 1,
  end,
  mul_inv_cancel := mul_inv,
  inv_zero := inv_zero
}

example (α )

example [MyField F4] : (1 : F4) + 1 = F4.a → false := begin
intro h,
have : 1 + F4.b*F4.b*F4.b = F4.b*F4.b,
rw b_cube, rw b_sq, exact h,
have : 1 + (F4.b)^3 = F4.b^2,
ring_nf at this, rw ← this, ring,
have w : (1 + (F4.b)^3) - F4.b^3 = F4.b^2 - F4.b^3,
rw this,
ring_nf at w,
have : (-1) *F4.b = -F4.b, ring,
rw mul_comm ((-1)*F4.b + 1) (F4.b^2) at w,
have l : ((-1)*F4.b + 1)= (F4.a - 1 - F4.b),
rw ← h, ring,
rw l at w,
end
example [MyField F4] : (1:F4) + 1 = 0 := begin
suffices : F4.a * F4.a*F4.a + 1 
-- suffices : F4.a * F4.a * F4.a + 1 = 0,
-- rw [a_cube] at this,
-- exact this,

-- have : (F4.a + 1) * (F4.a*F4.a + -F4.a + 1) = F4.a*F4.a*F4.a + 1,
-- conv {
-- to_lhs,

-- rw distrib,
-- rw distrib,
-- rw mul_comm,
-- rw distrib,
-- rw mul_comm _ (-F4.a),
-- rw distrib,
-- rw mul_comm _ (1:F4),
-- rw ← add_assoc (F4.a*F4.a*F4.a),
-- rw add_assoc (1*(F4.a * F4.a)), 
-- rw mul_assoc,

-- rw ← mul_assoc 1 F4.a,
-- rw mul_comm 1 (F4.a*F4.a),
-- rw mul_one,
-- rw ← left_distrib _ _ F4.a,
-- rw add_neg,
-- rw mul_comm 0 F4.a,
-- rw mul_zero,
-- rw [mul_one, mul_one],
-- rw add_comm (0:F4),
-- rw add_zero,
-- rw add_assoc,
-- rw ← add_assoc _ (-F4.a) F4.a, 
-- rw add_comm (-F4.a) F4.a,
-- rw add_neg,
-- rw add_zero,
-- },
-- rw ← this,
-- rw a_sq,
end
end MyField