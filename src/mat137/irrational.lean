import data.real.irrational

#check exists_irrational_btwn
#check exists_rat_btwn
-- lim_{x → a} f(x) = L
def limit (f : ℝ → ℝ) (a : ℝ) (L : ℝ) :=
 ∀ ε > 0, ∃ δ > 0,
   ∀ x : ℝ, 0 < |x - a| ∧ |x - a| < δ → |f x - L| < ε

example (f : ℝ → ℝ) (h1 : ∀ x : ℝ, irrational x → f x = x^2) (h2 : ∀ x : ℝ, ¬ irrational x → f x = x) : 
limit f 1 1 := begin
intros ε he,
use min 1 (ε/3), 
use lt_min_iff.mpr ⟨zero_lt_one, div_pos he (zero_lt_three)⟩,
intro x,
rintro ⟨h, hx⟩,
have := min_le_left 1 (ε / 3),
have := min_le_right 1 (ε / 3),
cases em (irrational x) with l r,
{
  specialize h1 x l,
  rw h1,
  have : |x - 1| * |x + 1| = |x^2 - 1|, 
    rw ← abs_mul,
    ring,
  rw ← this,
  have p : |x - 1| < ε/3, linarith,
  have := abs_add (x - 1) 2,
  ring_nf at this, norm_num at this,
  have q : |x + 1| < 3, linarith,
  have := mul_lt_mul'' p q (abs_nonneg (x - 1)) (abs_nonneg (x + 1)),
  linarith only [this],
},
{
  specialize h2 x r,
  rw h2,
  linarith,
},
end


example (f : ℝ → ℝ) (h1 : ∀ x : ℝ, irrational x → f x = x^2) (h2 : ∀ x : ℝ, ¬ irrational x → f x = x) : 
¬ ∃ L, limit f 2 L := begin
intro h,
cases h with L h,
specialize h 1 (zero_lt_one),
rcases h with ⟨δ, ⟨Hd, h⟩⟩,
suffices : ∃ x1 x2 ∈ {x | 0 < |x - 2| ∧ |x - 2| < δ}, |f x1 - f x2| ≥  2,
{
  rcases this with ⟨x1, hx1, x2, hx2, hx⟩,
  simp only [set.mem_set_of_eq] at *, -- hx1 and hx2
  have h1 := h x1 hx1,
  have h2 := h x2 hx2,
  have := add_lt_add h1 h2,
  norm_num at this,
  have := abs_add (f x1 - L) (- (f x2 - L)),
  rw abs_neg at this,
  norm_num at this,

  linarith,
},

-- intuitively (or morally as ivan says), we want to pick f(x1) < 2 and f(x2) > 4
-- this would give : f(x1) - f(x2) ≥ 2 and x1 
-- pick x1 from the open interval (2 - δ, 2)
have H1 : 2 - δ < 2, linarith,
cases exists_rat_btwn H1 with q hq,
have H2 : (2:ℝ) < 2 + (min δ (1 / 5)),
{
  suffices : 0 < min δ (1/5), linarith,
  apply lt_min_iff.mpr,
  exact ⟨Hd, by norm_num⟩,
},
rcases exists_irrational_btwn H2 with ⟨r, ⟨hr1, hr2, hr3⟩⟩,
use q, 
split,
-- 0 < |x1 - 2| < δ 
{
  simp only [set.mem_set_of_eq],
  split,
  rw abs_pos,
  linarith,
  rw abs_lt,
  split;
  linarith,
},
use r,
split,
{
  simp only [set.mem_set_of_eq],
  split,
  rw abs_pos,
  linarith,
  rw abs_lt,
  split,
  linarith,
  have := min_le_left δ (1/5),
  linarith,
},
-- prove a tear is created (|f(x1) - f(x2)| ≥ 2)
suffices : f q < 2 ∧ 4 < f r,
{
  apply le_abs.mpr,
  right,
  linarith only [this.left, this.right],
},

split,
rw h2 q (rat.not_irrational q),
exact hq.right,

rw h1 r hr1,
suffices : (r - 2)*(r+2) > 0, linarith,
apply mul_pos,
linarith,
linarith,
end

example (f : ℝ → ℝ) (L : ℝ): ∀ c > 0, (limit f 0 L) → (limit (λ x, 7 * f (c*x)) 0 (7*L)) := begin
intros c hc,
intro h,

intros ε he,
specialize h (ε / 7) (by linarith),
rcases h with ⟨δ1, Hd, h⟩,
use (δ1/c), use div_pos Hd hc, 
intros x hx,
specialize h (c*x),
have h := h _,
simp,
have : 7* f (c * x) - 7 * L = 7*(f (c*x) - L), ring,
rw this,
rw abs_mul,
have w : (7:ℝ) > 0, linarith,
rw abs_of_pos w,
linarith,

{
  ring_nf at hx,
  split,
  ring_nf,
  rw abs_mul,
  apply mul_pos,
  exact hx.left,
  exact abs_pos_of_pos hc,

  have := (mul_lt_mul_right hc).mpr hx.right,
  have l := norm_num.ne_zero_of_pos c hc,
  field_simp at this,
  ring_nf,
  rw [abs_mul, abs_of_pos hc],
  exact this,
},
end

example : ∃ f : ℝ → ℝ, ¬(∀ c ≠ (1 : ℝ), ∀ L : ℝ, (limit f 1 L) → (limit (λ x, 7 * f (c*x)) 1 (7*L))) := begin
use λ x, x,
simp only [not_forall, exists_prop],
use 2, use (by linarith),
use 1, -- L = 1
split,
{ -- limit exists
  intros ε he,
  use ε, use he,
  intros x hx,
  simp,
  exact hx.right,  
}, 
{ -- other limit is false
  rw limit,
  simp only [not_forall, not_exists],
  use (1/2), use (by linarith),
  intros δ hd,
  use (1 + min (1/2) (δ/2)),
  split,
  split, { -- 0 <
    cases min_cases (1/2) (δ/2),
    rw h.left, norm_num,
    rw h.left,
    rw abs_pos,
    linarith,
  },
  { -- < δ 
    ring,
    rw abs_of_pos,
    rw min_lt_iff,
    right,
    linarith,

    rw lt_min_iff,
    split,
    linarith,
    linarith,
  },
  { -- ≥ ε
    have : 0 < min (1 / 2) (δ/2),
      rw lt_min_iff,
      exact ⟨by linarith, by linarith⟩,
    rw abs_of_pos,
    linarith,

    linarith,
  },
}
end

#check finset