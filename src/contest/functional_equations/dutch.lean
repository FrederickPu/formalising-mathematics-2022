import tactic
import data.real.basic

-- 2021 Dutch math olympiad: https://www.youtube.com/watch?v=qsC_KENh8Lw
constant f : ℝ → ℝ
constant q : ∀ x y : ℝ, f (x+y) = f x + f y + x*y
constant p : f 4 = 10

lemma h0 : f 1 = 1 :=
begin
have u := q 2 2, 
ring_nf at u, 
rw p at u,

have u1 := q 1 1,
simp at u1, ring_nf at u1,

linarith,
end

lemma h (a : ℝ) : f (a+1) = (f a) + a+ 1 :=
begin
have := q a 1,
ring_nf at this,
rw h0 at this,
linarith,
end

@[simp]
lemma hoo (k : ℕ) : k.succ = k + 1 := rfl

lemma h1 (n : ℕ) (l : n ≥ 1): f n = (n+1)*n / 2 :=
begin
induction n with k,
linarith,

cases k,
simp, exact h0,

have w : k.succ ≥ 1,
simp,
have kh := n_ih w,
push_cast,
rw h (k + 1),
push_cast at kh,
rw kh,
ring,
end

lemma duh (n : ℕ) : f n = f (n : ℝ) :=
begin
refl,
end

lemma final : f(2001) = 1001 * 2001 :=
begin
have q1 : 2001 ≥ 1, linarith,
have := h1 2001 q1,
simp at this,
rw this, 
ring,
end