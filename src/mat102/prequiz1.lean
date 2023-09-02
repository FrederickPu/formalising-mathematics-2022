import data.real.sqrt

section question5

-- pick any x > 1 and y < -1
theorem option1_false : ¬ (∀ (x y : ℝ), x > 1 ∧ y ≠ 0 → x*y > y) := begin
intro h,
specialize h 2 (-2),
norm_num at h,
end

theorem option2_true (x y : ℝ) : 0 < x ∧ x < y → x.sqrt < y.sqrt := begin
rintros ⟨h1, h2⟩,
have hx : x ≥ 0 := le_of_lt h1,
have hy : y ≥ 0 := by linarith,
have p := (real.sq_sqrt hx).symm,
have q := (real.sq_sqrt hy).symm,
rw [p, q] at h2,

exact lt_of_pow_lt_pow 2 (real.sqrt_nonneg y) h2,
end 

theorem option3_true (x y : ℝ) : x < y → -4*x-10 > -4*y-10 := begin
intro h,
linarith,
end

-- theorem unprovable only true for (x - y)(x+y) ≥ 0, ie x ≥ y ≥ -x
-- so y ≥ -x must be true in addition to x ≥ y
example (x y : ℝ) : x ≥ y → x^2 ≥ y^2 := begin
intro h,
suffices : y ≥ -x, -- thus y ≥ -x is a sufficient additional condition
{
  suffices : x^2 - y^2 ≥ 0,
    linarith,
  suffices : (x - y)*(x+y) ≥ 0,
    linarith,
  suffices p : (x - y) ≥ 0,
  suffices  q: (x + y) ≥ 0,
  exact mul_nonneg p q,
  linarith only [this],
  linarith only [h],
},
-- we haven't proved y ≥ -x is necessary
end

-- findiing counter example to the above statement
-- we pick x, y such that x ≥ y but y < -x and hence x^2 < y^2
theorem option4_false : ¬ (∀ (x y : ℝ), x ≥ y → x^2 ≥ y^2) := begin
intro h,
specialize h 1 (-2),
norm_num at h,
end

theorem option5_true (x y : ℝ) : x ≥ y → x^3 ≥ y*x^2 := begin
intro h,
have r : x^2 ≥ 0 := sq_nonneg x,
have l : x^3 = x*x^2, ring,
rw [l],
exact mul_mono_nonneg r h,
end

-- in summary options 1 and 4 are false due to reasons related to *absolute value* and **sign change property** of multiplication and squaring.
end question5
