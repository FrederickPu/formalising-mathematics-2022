import tactic
import data.real.basic

-- 2011 Philippine Mathematics Olympiad.
-- https://www.youtube.com/watch?v=jb1J7Dcmu3Y
lemma Philippines : ¬ (∃ (f : ℝ → ℝ), ∀ x, f(f(x)) + x*f(x)= 1) :=
begin
intro p,
cases p with f p,
have h1 := p 0, simp at h1,
have h2 := p (f 0), rw h1 at h2, simp at h2,
have h4 : f 0 = f (f 1),
  {
  have h3 := p 1,
  have h4 := eq.trans h2 h3.symm,
  simp at h4,
  linarith,
  },
have h5 := by {
  have q:= p (f 1),
  rw ← h4 at q,
  rw h1 at q,
  have : (f 1) * (f 0) = 0, linarith,
  exact this,
  },
have q := zero_eq_mul.mp (eq.symm h5),
cases q with l r,
{
  rw l at h2, simp at h2,
  rw h2 at h1,
  linarith,
},
{
  rw r at h1,
  linarith,
},
end