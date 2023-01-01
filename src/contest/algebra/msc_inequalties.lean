import tactic
import data.real.basic

-- proved some standard inequalities
-- some successful
-- some not so successful

example (a b c : ℝ) : a^2 + b^2+c^2 ≥ a*b + b*c + a*c :=
begin
  suffices : (a^2 + b^2+c^2) - (a*b + b*c + a*c) ≥ 0,
  linarith,
  suffices : 2*(a^2 + b^2+c^2) - 2*(a*b + b*c + a*c) ≥ 0,
  linarith,
  suffices : (a-b)^2+(a-c)^2+(b-c)^2 ≥ 0,
  ring_nf at this,
  linarith,
  suffices : (a-b)^2 ≥ 0 ∧ (a-c)^2≥ 0∧ (b-c)^2≥ 0,
  rcases this with ⟨l, m, r⟩,
  linarith,
  repeat {split <|> skip, exact sq_nonneg _,},
end

example (a b c: ℝ) (h : a ≠ 0) (h1 : b ≠ 0) : a * b ≠ 0:=
begin
library_search,
end

theorem duh_right (x y z : ℝ) (h1 : z ≠ 0) (h:z * x = z*y): x = y :=
begin
library_search,
end

variables (a b c : ℝ)

example
(p : a ≠ b)
(q : b ≠ c)
(r : a ≠ c)
(h: a^2*(1-b+c)+b^2*(1-c+a)+c^2*(1-a+b) = a*b + b*c + c*a):
1/(a-b)^2 + 1/(b-c)^2+1/(c-a)^2 = 1
 :=
begin
have l : (a-b)^2 * (b-c)^2 * (a-c)^2 ≠ 0,
{
  have lp := pow_ne_zero 2 (sub_ne_zero.mpr p),
  have lq := pow_ne_zero 2 (sub_ne_zero.mpr q),
  have lr := pow_ne_zero 2 (sub_ne_zero.mpr r),

  have := mul_ne_zero lp (mul_ne_zero lq lr),
  rw mul_assoc, exact this,
},
have := mul_right_inj' l,
suffices : ((a - b) ^ 2 * (b - c) ^ 2 * (a - c) ^ 2) * (1 / (a - b) ^ 2 + 1 / (b - c) ^ 2 + 1 / (c - a) ^ 2) = (a - b) ^ 2 * (b - c) ^ 2 * (a - c) ^ 2*1,
exact (mul_right_inj' l).mp this,


/-have : (1/(a-b)+ 1/(b-c)+1/(c-a))^2 = 1/(a-b)^2 + 1/(b-c)^2+1/(c-a)^2,
{
suffices : ((a-b)*(b-c)*(c-a))*(1/(a-b)+ 1/(b-c)+1/(c-a)) = ((a-b)*(b-c)*(c-a))*(1/(a-b)+ 1/(b-c)+1/(c-a)),
have : (a-b)*(b-c)*(c-a) ≠ 0,
exact mul_div_cancel ((a-b)*(b-c)*(c-a)),
}-/
end

lemma l_min_r : a - b ≥ 0 → a ≥ b :=
begin
exact sub_nonneg.mp,
end

example (p : a ≠ 0) (q : b≠ 0) (r : c ≠ 0) : (a/c + b/c+ c/a)^2 ≥ (a+b + c)*(1/a + 1/b + 1/c):=
begin


have l : (a+b + c)*(1/a + 1/b + 1/c) = 3 + (c+a)/b + (a+b)/c + (b+c)/a,
field_simp, ring,

have lp : (a / c + b / c + c / a) ^ 2 = a^2/c^2 + b^2/c^2 + c^2/a^2+ 2*a*b/c^2 + 2 + 2 * b/a,
field_simp, ring,

apply l_min_r, rw [l, lp],
end