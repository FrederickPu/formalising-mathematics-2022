import data.real.basic

#check ℝ

-- limit as x -> a from the right of f(x) = b
def Rlimit (a : ℝ) (f: ℝ → ℝ) (b : ℝ) := 
∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, a < x ∧ x < a + δ  → |b - f x| < ε

def Llimit (a : ℝ) (f: ℝ → ℝ) (b : ℝ) := 
∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, a - δ < x ∧ x < a  → |b - f x| < ε

def limit (a : ℝ) (f : ℝ → ℝ) (b : ℝ) := 
∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, |x - a| < δ → |b - f x| < ε

theorem RL_imp (a : ℝ) (f : ℝ → ℝ) (b : ℝ) :
Rlimit a f b → Llimit a f b → f a = b → limit a f b :=
begin
intros h1 h2 h3,
intros ε he,
rcases h1 ε he with ⟨δ1, ⟨Hd1, h1_h⟩⟩,
rcases h2 ε he with ⟨δ2, ⟨Hd2, h2_h⟩⟩,
use min δ1 δ2,
split,
{
  cases min_choice δ1 δ2,
  rw h, exact Hd1,
  rw h, exact Hd2,
},

intro x,
specialize h1_h x, specialize h2_h x,
cases lt_or_ge x a, 
{
  rw abs_of_neg (sub_neg.mpr h),
  intro h,
  have := min_le_right δ1 δ2,
  exact h2_h ⟨by linarith, by linarith⟩,
},
{
  cases le_iff_lt_or_eq.mp h,
  {
    rw abs_of_pos (sub_pos.mpr h_1),
    have := min_le_left δ1 δ2,
    intro l,
    exact h1_h ⟨by linarith, by linarith⟩,
  },
  {
    rw h_1,
    intros,
    simp only [abs_zero, sub_self, h3.symm, h_1],
    exact he,
  },
},
end


theorem Roberton'sLemma :
¬ (∀ a f b, Rlimit a f b → Llimit a f b → limit a f b) :=
begin
intro p,
specialize p 0 (λ x, x/x) 1,
suffices : limit 0 (λ (x : ℝ), x / x) 1,
{
  simp [limit] at this,
  specialize this (1/(2:ℝ)) one_half_pos,
  cases this with δ,
  cases this_h with H h,
  specialize h 0,
  rw abs_zero at h,
  specialize h H,
  simp only [div_zero, sub_zero, abs_one] at h,
  linarith,
},

apply p,
{
  intros ε he,
  use 1,
  split,
  linarith,
  intro x,
  simp,
  intros h1 h2,
  rw div_self (ne_of_gt h1),
  simp only [abs_zero, sub_self],
  exact he,
},

{
  intros ε he,
  use 1,
  split,
  linarith,
  intro x,
  simp,
  intros h1 h2,
  rw div_self (ne_of_lt h2),
  simp only [abs_zero, sub_self],
  exact he,
},
end

-- math rocks!