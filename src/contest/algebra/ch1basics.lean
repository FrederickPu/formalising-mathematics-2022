import tactic
import data.real.basic

import data.finset
open_locale big_operators
open finset

variables (x y z: ℝ)
variables (a b c d: ℝ)
noncomputable theory

-- 1.1
example : 2*x + 3 ≥ 17 → x ≥ 7 :=
begin
  intro, linarith,
end

-- 1.2

-- attainable minimum given a condition
def min_val (f : ℝ → ℝ) (P : ℝ → Prop) (a : ℝ)  := 
(∀ (x : ℝ), P x →  f(x) ≥ a) ∧ ∃ (y : ℝ), P y ∧  f(y) = a

example : min_val (λ x, 9*x + 4) (λ x, x ≥ 2) 22 :=
begin
  rw min_val,
  split,
    {rintros, linarith,},
    {
    use 2, 
    split, 
      linarith, norm_num,
    },
end

-- 1.3
example : a > b → -b > -a :=
begin
  exact neg_lt_neg,
end

-- 1.4
example (h : a > b ∧ b > 0): 1/a < 1/b :=
begin
  exact one_div_lt_one_div_of_lt h.right h.left,
end

-- 1.5
example (h : a > b) (h1 : c > d): a + c > b + d :=
begin
  exact add_lt_add h h1,
end

-- 1.6 (basically same as 1.4)

theorem trivial_inequality : x^2 ≥ 0 :=
begin
exact sq_nonneg x,
end

-- 1.7
lemma l17 : (a+b)^2 ≥ 4*a*b :=
begin
  suffices : (a+b)^2 - 4*a*b ≥ 0,
  exact sub_nonneg.mp this,

  suffices : (a-b)^2 ≥ 0,
  linarith,
  exact sq_nonneg (a-b),
end

-- 1.8
example : a^2 + 4*b^2 ≥ 4*a*b :=
begin
  have := l17 a (2*b),
  linarith,
end

-- 1.9
lemma l19 : a^2 + b^2 + c^2 ≥ a*b + b*c + c*a :=
begin
  suffices : (a-b)^2 + (b-c)^2 + (c-a)^2 ≥ 0,
  linarith,
  exact add_nonneg (add_nonneg (sq_nonneg (a-b)) (sq_nonneg (b-c))) (sq_nonneg (c - a)),
end

-- 1.10
lemma l110 : 3*(a^2+b^2+c^2) ≥ (a + b + c)^2 ∧ 
(a+b+c)^2≥ 3*(a*b+b*c+c*a) :=
begin
  split,
    repeat {
      suffices : a^2 + b^2 + c^2 ≥ a*b + b*c + c*a,
      linarith,
      exact l19 a b c,
    },
end

-- 1.11
lemma l1111 (ha : a > 0): a*(b^2 + c^2) ≥ 2*a*b*c :=
begin
  have := two_mul_le_add_sq b c,
  have := (mul_le_mul_left ha).mpr this,
  linarith,
end

lemma l1_11 (ha : a > 0) (hb : b > 0) (hc : c > 0) : 
a*(b^2+c^2) + b*(c^2+a^2) + c*(a^2 + b^2) ≥ 6 *a*b*c :=
begin
  have p := l1111 a b c ha,
  have q := l1111 b c a hb,
  have r := l1111 c a b hc,
  linarith,
end

-- 1.12
lemma l1_12 (ha : a > 0) (hb : b > 0) (hc : c > 0) :
(a+b)*(b+c)*(c+a) ≥ 8 *a*b*c :=
begin
have := l1_11 a b c ha hb hc,
linarith,
end

-- 1.13
lemma sum_range_start (a : ℕ → ℝ) (n : ℕ) :
∑ (i : ℕ) in range (n + 1), a i = a 0 + ∑ (i : ℕ) in range n, a (i+1) :=
begin
  induction n with k,
  norm_num,
  rw sum_range_succ(λ (x : ℕ), a x) (k+1),
  rw sum_range_succ(λ (x : ℕ), a (x+1)) k,
  simp,
  rw n_ih,
  ring,
end
lemma cyc_sum_eq (n : ℕ) (a : ℕ → ℝ) : 
∑ i in range (n+1), a i  = ∑ i in range (n+1), a ((i+1)%(n+1)) :=
begin
  rw sum_range_succ (λ (x : ℕ), a ((x+1)%(n+1))) n,
  rw sum_range_start (λ (x : ℕ), a x) n,
  simp,

  suffices : ∑ (i : ℕ) in range n, a (i + 1) = ∑ (x : ℕ) in range n, a ((x + 1) % (n + 1)),
    linarith,
  apply sum_congr, refl,
  intros,
  {
    rw nat.mod_eq_of_lt,
    exact by { have := mem_range.mp H, linarith,},
  },
end
example (n : ℕ) (a : ℕ → ℝ) (b : ℕ → ℝ):
∑ i in range n, a i + ∑ i in range n, b i  = ∑ i in range n, (a i+b i) :=
begin
  exact sum_add_distrib.symm,
end
lemma mul_distrib_sum (n : ℕ) (a : ℕ → ℝ) :
b *∑ i in range n, a i = ∑ i in range n, b*a i :=
begin
  induction n with k h,
  norm_num,
  simp only [sum_range_succ _ k],
  rw ← h, ring,
end

example (n : ℕ) (a : ℕ → ℝ):
∑ i in range n, (a i)^2 ≥ ∑ i in range n, (a i)*(a ((i+1)%n))
:=
begin
  have l1 : ∑ (i : ℕ) in range n, a i ^ 2 = ∑ (i : ℕ) in range n, (a ((i+1)%n)) ^ 2,
  {
    cases n,
    norm_num,
    exact cyc_sum_eq n (λ (i : ℕ), a i ^ 2),
  },
  suffices : 2*∑ (i : ℕ) in range n, a i ^ 2 ≥ 2*∑ (i : ℕ) in range n, a i * a ((i + 1) % n),
  linarith,
  have l2 : 2*∑ (i : ℕ) in range n, a i ^ 2 = ∑ (i : ℕ) in range n, a i ^ 2 + ∑ (i : ℕ) in range n, a ((i+1)%n) ^ 2,
    {rw l1, ring,},
  
  rw l2,
  rw sum_add_distrib.symm,
  apply sub_nonneg.mp,
  rw mul_distrib_sum,
  rw sum_sub_distrib.symm,
  apply sum_nonneg,
  {
    intros,
    suffices : (a (i) - a ((i + 1) % n)) ^ 2 ≥ 0,
    linarith,
    exact sq_nonneg _,
  },
  apply_instance,
end


-- 1.14
lemma l1_14 (ha : a > 0) (hb : b > 0) (hc : c > 0) :
a^4+b^4+c^4 ≥ a*b*c*(a+b+c) :=
begin
  have := l19 (a^2) (b^2) (c^2),
  ring_nf at this,
  have := l19 (a*b) (b*c) (c*a),
  linarith,
end