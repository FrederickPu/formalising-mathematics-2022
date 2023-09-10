import tactic
import data.real.sqrt

theorem ch1_1_8_a (a b : ℝ) : a > 0 → b > 0 → a + b ≤ 1/2 → ((1 - a)/a)* ((1 - b)/b) ≥ 1 := begin
intros ha hb h,
have pa : a ≤ 1 - a, linarith,
have pb  : b ≤ 1 - b, linarith,
have pa' : (1 - a)/a ≥ 1, {
  have : a/a ≤ (1 - a)/a,
  exact (div_le_div_right ha).mpr pa,
  rw div_self (ne_of_gt ha) at this,
  exact this,
},
have pb' : (1 - b)/b ≥ 1, {
  have : b/b ≤ (1 - b)/b,
  exact (div_le_div_right hb).mpr pb,
  rw div_self (ne_of_gt hb) at this,
  exact this,
},
exact one_le_mul_of_one_le_of_one_le pa' pb',
end
theorem ch1_1_8_b : ¬ (∀ a b : ℝ, a > 0 → b > 0 → (1 - a)/a + (1 - b)/b ≥ 1 → a + b ≤ 1/2) := begin
intro h,
specialize h (1/2) (1/2),
simp at h,
have : ¬ ((2:ℝ) ≤ 0), linarith,
apply this,
apply h,
norm_num,
end

theorem ch1_1_11_a (x y u v : ℝ) : 4*x*y*u*v ≤ 2*x^2*y^2+2*u^2*v^2 := begin
have : (x*y - u*v)^2 ≥ 0, exact sq_nonneg (x * y - u * v),
linarith,
end

theorem ch1_1_11_b (x y u v : ℝ) : (x*u + y*v)^2 ≤ (x^2 + y^2)*(u^2+v^2) := begin
have : (y*u - x*v)^2 ≥ 0, exact sq_nonneg (y * u - x * v),
linarith,
end

theorem ch1_1_13 (x y : ℝ) : 2*x*y ≤ 2/3*x^2 + 3/2*y^2 := begin
have : ((2/(3:ℝ)).sqrt * x - (3/(2:ℝ)).sqrt * y)^2 ≥ 0, 
exact sq_nonneg (real.sqrt (2 / 3) * x - real.sqrt (3 / 2) * y),
have l :  ((2/(3:ℝ)).sqrt * x - (3/(2:ℝ)).sqrt * y)^2 =  (2/(3:ℝ)).sqrt^2* x^2 + - 2*(((2/(3:ℝ)).sqrt)*((3/(2:ℝ)).sqrt))*x*y+  (3/(2:ℝ)).sqrt^2 * y^2,
ring,
rw l at this,
rw [real.sq_sqrt, real.sq_sqrt] at this,
rw ← @real.sqrt_mul (2 / (3:ℝ)) (by linarith) (3/(2:ℝ)) at this,
norm_num at this,
linarith,

-- prove trivial nonneg things
norm_num,
norm_num,
end 
theorem ch1_1_14 (x y z : ℝ) : x > y → y > z → x*y + y*z > ((x+y)*(y+z))/2 := begin
intros h1 h2,
have : y - z > 0, linarith only [h2],
have : x*(y-z) > y*(y - z), exact (mul_lt_mul_right this).mpr h1,
linarith,
end