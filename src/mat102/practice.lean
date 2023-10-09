import data.real.sqrt
noncomputable def f : ℝ → ℝ := λ x : ℝ, x^2 / (x^2 + 1) 
#check (set.Icc (0:ℝ) 3)
#check (f '' set.univ) 

example : (f '' set.univ) = {x : ℝ | 0 ≤ x ∧ x < 1} := begin
ext y,
simp,
split,
-- first inclusion
{
intro h,
cases h with x hx,
rw f at hx, simp at hx,
rw ← hx, 
split,
have div_nonneg_pos : ∀ a b : ℝ, a ≥ 0 → b > 0 → a / b ≥ 0, intros a b ha hb,
{
  cases gt_or_eq_of_le ha, 
  {
    have := div_pos h hb,
    exact le_of_lt this,
  },
  {
    rw h,
    simp only [zero_div, ge_iff_le],
  },
},
apply div_nonneg_pos,
exact sq_nonneg x,
linarith [sq_nonneg x],

have l : x^2 + 1 > 0,
linarith [sq_nonneg x],
have r : 1 / (x^2 + 1) > 0, exact one_div_pos.mpr l,
have : x^2 < x^2 + 1, linarith,
have := (mul_lt_mul_right r).mpr this,
have w : x^2 +1 ≠ 0, exact ne_of_gt l,
field_simp at this,
exact this,
},
{
  intro h,
  cases h with l r,
  have w : 1 - y > 0, linarith,
  have div_nonneg_pos : ∀ a b : ℝ, a ≥ 0 → b > 0 → a / b ≥ 0, intros a b ha hb,
  {
    cases gt_or_eq_of_le ha, 
    {
      have := div_pos h hb,
      exact le_of_lt this,
    },
    {
      rw h,
      simp only [zero_div, ge_iff_le],
    },
  },
  have := div_nonneg_pos y (1 - y) l w,
  use (y / (1 - y)).sqrt,
  
  field_simp [f, real.sq_sqrt this, ne_of_gt w],
},
end 