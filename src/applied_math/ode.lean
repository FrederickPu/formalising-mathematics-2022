import analysis.special_functions.trigonometric.complex_deriv
import analysis.special_functions.exp_deriv
import analysis.ODE.picard_lindelof
import analysis.ODE.gronwall
#check deriv

-- playing around with picard's theorem
open complex picard_lindelof

example : deriv sin = cos :=
begin
simp,
end

example : deriv (λ x, exp x + sin x) = λ x, exp x + cos x :=
begin
ext, simp, simp,
end

#check ODE_solution_unique
#check has_edist ℂ

structure interval (a b : ℝ) :=
(x : ℝ)
(hx : a ≤ x ∧ x ≤ b)

example : interval 2 4 := ⟨3, by norm_num⟩

#check has_dist ℝ

variables (a b : ℝ)
noncomputable instance : has_dist (interval a b) :=
{
  dist := λ c, λ d,  has_dist.dist c.x d.x,
}
noncomputable instance : pseudo_metric_space (interval a b) :=
{
  dist_self := λ x, by simp [dist],
  dist_comm := λ x,λ y, by {simp [dist], exact abs_sub_comm x.x y.x},
  dist_triangle := λ x, λ y, λ z, by {simp [dist], exact abs_sub_le x.x y.x z.x,},
}

def duh : lipschitz_with 3 (λ x :interval 0 3,x) :=
begin
rw lipschitz_with,
simp [edist, pseudo_metric_space.edist],
intros x y,

end

example (x y : ℂ) : sin (x + y) = sin x * cos y + cos x * sin y :=
begin
exact sin_add x y,
end

lemma diff_sin (A B : ℂ) : sin A - sin B = 2 *cos (1/2* (A + B)) * sin (1/2* (A - B)) :=
begin
have h1 := sin_add ((A + B)/2) ((A - B)/2),
ring_nf at h1,
have h2 := sin_sub ((A + B)/2) ((A - B)/2),
ring_nf at h2,

rw [h1, h2],
field_simp,
ring,
end

example (a b c : ℂ)  : dist a b = abs (a - b):=
begin
exact dist_eq a b,
end

noncomputable def f := λ x, sin x

-- linear approx of f at t
noncomputable def v := λ (t:ℝ), (λ (x:ℂ), ((deriv f) t))

lemma hv : ∀ (t : ℝ), lipschitz_with 1 (v t) :=
begin
intro t,

apply lipschitz_with.of_dist_le_mul,
simp only [dist_eq, v],
ring,

intros x y,
simp only [mul_one, nonneg.coe_one, complex.abs_zero],
exact abs_nonneg (x-y),
end

example : 2 + 2 = 4 :=
begin
have : ODE_solution_unique hv,
end