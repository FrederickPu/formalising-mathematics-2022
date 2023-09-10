import tactic
import data.real.basic

theorem ch1_1_14 (x y z : ℝ) : x > y → y > z → x*y + y*z > ((x+y)*(y+z))/2 := begin
intros h1 h2,
have : y - z > 0, linarith only [h2],
have : x*(y-z) > y*(y - z), exact (mul_lt_mul_right this).mpr h1,
linarith,
end