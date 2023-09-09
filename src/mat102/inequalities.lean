import data.real.sqrt

theorem AGM_1 (x y : ℝ) : x * y ≤ ((x + y)/2)^2 := begin
suffices : x*y ≤ (x^2 + 2*x*y + y^2)/(4:ℝ),
ring,
linarith,
suffices : 0 ≤ x^2-2*x*y+y^2,
linarith,
suffices : 0 ≤ (x - y)^2,
linarith,

exact sq_nonneg (x - y),
end
theorem AGM_1' (x y : ℝ) : x ≥ 0 → y ≥ 0 → (x*y).sqrt ≤ (x + y) / 2 := begin
intros hx hy,
have := AGM_1 x y,
rw ← @real.sqrt_sq ((x + y)/2) (by linarith),
exact real.sqrt_le_sqrt this,
end

theorem AGM_2 (x y : ℝ) : (x = y) →  x * y = ((x + y)/2)^2 := begin
intro h,
rw h,
ring,
end

theorem AGM_2' (x y : ℝ) : x ≥ 0 → y ≥ 0 → (x = y) → (x*y).sqrt = (x + y) / 2  := begin
intros hx hy,
intro h,
rw h,
ring,
exact real.sqrt_sq hy,
end

theorem AGM_3 (x y : ℝ) : x * y = ((x + y)/2)^2 → (x = y) := begin
intro h,
have h : x*y = (x^2+2*x*y+y^2)/4,
rw [h],
ring,
have h : 0 = (x - y)^2,
linarith,
suffices : x - y = 0,
linarith,
exact pow_eq_zero (eq.symm h),
end

theorem AGM_3' (x y : ℝ) : x ≥ 0 → y ≥ 0 → (x*y).sqrt = (x + y) / 2 → x = y := begin
intros hx hy,
intro h,
apply AGM_3 x y,
rw ← @real.sq_sqrt (x*y) (mul_nonneg hx hy),
exact congr_fun (congr_arg pow h) 2,
end

example (a b : ℝ) (h : a + 2*b = 50) : a * b ≤ 25^2/2 ∧ ∃ a1 b1 :ℝ, a1*b1 = 25^2/2 := begin
have := AGM_1 a (2*b),
rw [h] at this,
split,
norm_num at this,
norm_num,
linarith,

-- we need a = 2*b and a + 2*b = 50
-- a + a = 50 
-- a = 25, b = 25/2
use 25, use 25/2,
ring,
end 


theorem triangle (a b : ℝ) : |a + b| ≤ |a| + |b| := begin
have lol : ∀ x y : ℝ, x^2 ≤ y^2 → x ≥ 0 → y ≥ 0 → x ≤ y, intros x y, intros j p q,
  have : x*x ≤ y*y, simp [(sq _).symm], exact j,
  exact (mul_self_le_mul_self_iff p q).mpr this,
apply lol,
rw sq_abs (a + b),
suffices : (a+b)^2 ≤ |a|^2 +2*|a|*|b|+|b|^2,
linarith,
simp only [sq_abs],
have : (a+b)^2 = a^2+2*a*b+b^2,
ring,
rw this,
suffices : a*b ≤ |a|*|b|,
linarith,

rw ← abs_mul,
exact le_abs_self (a * b),


exact abs_nonneg (a + b),
linarith [abs_nonneg a, abs_nonneg b],
end

theorem pow_odd_le_pow_of_le_left {a b : ℝ} (hab : a ≤ b) : ∀ i : ℕ, odd i → a^i ≤ b^i := begin
intros i hi,
have pow_odd : ∀ x : ℝ, (-x) ^ i = -(x)^i, 
{
  cases hi with k hk,
  rw [hk],
  intro x,
  repeat {rw pow_succ'},
  rw [pow_mul (-x) 2 k, neg_sq x, ← pow_mul],
  norm_num,
},
cases le_or_lt 0 a,
exact pow_le_pow_of_le_left h hab i,

cases le_or_lt 0 b,
have : a = -(-a) := (neg_neg a).symm,
rw [this,pow_odd],
have : -a > 0, exact neg_pos.mpr h,
have : (-a)^i  > 0, exact pow_pos this i,
have : b^i ≥ 0, exact pow_nonneg h_1 i,
linarith,

have p := neg_pos.mpr h, have q := neg_pos.mpr h_1,
have := pow_pos p i, have := pow_pos q i,
rw [← neg_neg a, pow_odd, ← neg_neg b, pow_odd (-b)],
have := @pow_le_pow_of_le_left ℝ _ (-b) (-a) (le_of_lt q) (by linarith) i,
linarith,
end

-- TODO figure out why lean thinks this is noncomputable but pow_odd_le_pow_of_le_left computable.
noncomputable example : subtype (λ (M : ℝ), ∀ x:ℝ, |x| ≤ 2 →  |x^5 + -2*x+5| ≤ M) := begin
apply subtype.mk (|(2:ℝ)^5| + |(-2*2)|+|5|),
intros x hx,
have := abs_add_three (x ^ 5) ((-2) * x) 5,
apply le_trans this,
apply add_le_add_three,
simp only [← pow_abs],
have : |(2:ℝ)| = 2 := abs_eq_self.mpr (by linarith),
rw this,
have:  ∀ (a b : ℝ) (n : ℕ),  a ≥ 0 → b ≥ 0 → a ≤ b → a^n ≤ b^n,
intros,
exact pow_le_pow_of_le_left ᾰ ᾰ_2 n,
apply pow_odd_le_pow_of_le_left hx,
norm_num,

simp only [abs_mul],
have : |(-(2:ℝ))| = 2, norm_num,
rw this,
have : |(2:ℝ)| = 2, norm_num,
rw this,
linarith [hx],
norm_num,
end

#check quad