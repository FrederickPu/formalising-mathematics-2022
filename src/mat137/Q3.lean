import data.int.dvd.basic
import tactic

lemma div_subst {k n m : ℤ} : k ∣ n → n = m → k ∣ m := begin
intros p q,
rw q at p,
exact p,
end
lemma div_two_case (n : ℕ) : 2 ∣ n ∨ 2 ∣ (n+1) := begin
induction n with d dh,
simp,
cases dh,
{
  right,
  have : d.succ + 1 = d + 2, ring,
  rw this,
  exact nat.dvd_add_self_right.mpr dh,
},
{
  left,
  exact dh,
},
end
theorem Q3_nat (n : ℕ) : 6 ∣ n^3 + 5*n := begin
induction n with d dh,
simp,
rw nat.succ_eq_add_one,
have : (d + 1) ^ 3 + 5 * (d + 1) = d^3 + 5*d + 3*(d^2 + d + 2),
ring,
rw this,
apply dvd_add,
exact dh,
have : 6 = 3*2, refl,
rw this,
apply mul_dvd_mul,
exact rfl.dvd,

simp,
have : d^2 + d= d*(d+1), ring,
rw this,
have := div_two_case d,
cases this,
exact dvd_mul_of_dvd_left this_1 (d + 1),
exact dvd_mul_of_dvd_right this_1 d,
end

example (n : ℤ) : 6 ∣ n^3 + 5*n := begin
cases n,
have := Q3_nat n,
have : ((6:ℕ) : ℤ) ∣ ((n^3 + 5*n:ℕ) : ℤ),
exact int.coe_nat_dvd.mpr this,
exact this,

have := int.coe_nat_dvd.mpr (Q4_nat (n+1)),
have := dvd_neg.mpr this,
apply div_subst this,
rw int.neg_succ_of_nat_eq,
push_cast,
ring,
end