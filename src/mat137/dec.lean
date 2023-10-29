import data.real.basic

def dec (f : ℝ → ℝ) (D : set ℝ):= ∀ x1 x2 ∈ D, x1 < x2 → f x1 > f x2
noncomputable def aroc (f : ℝ → ℝ) (a b : ℝ) : ℝ := (f b - f a) / (b - a)

#check set.Icc
example (f : ℝ → ℝ): (∀ x1 x2 ∈ set.Icc (1 : ℝ) (2:ℝ), x1 < x2 → (aroc f x1 x2) < 0) → dec f (set.Icc (1 : ℝ) (2:ℝ)) := begin
intro h,
intros x1 hx1 x2 hx2,
intro hxs,
specialize h x1 hx1 x2 hx2,
specialize h hxs,

rw aroc at h,
have w : x2 - x1 > 0,
linarith,

have : (x2 - x1) * ((f x2 - f x1) / (x2 - x1)) < (x2 - x1) * 0,
exact (mul_lt_mul_left w).mpr h,
have : (x2 - x1) * ((f x2 - f x1) / (x2 - x1)) = f x2  - f x1, field_simp [ne_of_gt w], ring,

linarith,
end

/-
set.Icc : ?M_1 → ?M_1 → set ?M_1
-/

