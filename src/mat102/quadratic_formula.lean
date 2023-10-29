import data.real.sqrt

example (a b c : ℝ) (ha : a ≠ 0) (h : b^2 - 4*a*c ≥ 0): ∀ x : ℝ, a*x^2+b*x+c = 0 → x = (-b + (b^2 - 4*a*c).sqrt)/(2*a) ∨ x =  (-b - (b^2 - 4*a*c).sqrt)/(2*a) := begin
intro x,
intro h,
have h : x^2 + b/a*x + c/a = 0,
{
  have wow : (a * x ^ 2 + b * x + c)/a = 0, norm_num [ha, h],
  rw ← wow,
  field_simp, ring,
},
have h :   x^2 + 2 * x * (b / (2 * a)) + (b^2 / (4 * a^2)) - (b^2 / (4 * a^2)) + (c / a) = 0,
rw ← h, field_simp, ring,
have h : (x + (b / (2 * a)))^2 = ((b^2) / (4 * (a^2))) - (c / a),
{
  suffices : (x + (b / (2 * a)))^2 - (((b^2) / (4 * (a^2))) - (c / a)) = 0,
  linarith,

  rw [← h],
  ring, field_simp, ring,
},
have h : (x + (b / (2 * a)))^2 = (b^2 - 4 * a * c) / (4 * a^2),
rw h, field_simp, ring,
rw ← @real.sq_sqrt ((b^2 - 4 * a * c) / (4 * a^2)) _ at h,
have := eq_or_eq_neg_of_sq_eq_sq _ _ h,

end

#check prod.dv