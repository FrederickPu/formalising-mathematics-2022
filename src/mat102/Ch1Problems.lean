import tactic
import data.real.basic

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
theorem ch1_1_14 (x y z : ℝ) : x > y → y > z → x*y + y*z > ((x+y)*(y+z))/2 := begin
intros h1 h2,
have : y - z > 0, linarith only [h2],
have : x*(y-z) > y*(y - z), exact (mul_lt_mul_right this).mpr h1,
linarith,
end