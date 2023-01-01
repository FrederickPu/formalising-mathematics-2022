-- waterloo problem of the month (november)
-- https://www.cemc.uwaterloo.ca/resources/potm/2022-23/POTM-22-2-NOV-P.pdf

import tactic
import data.real.sqrt
import data.finset


open_locale big_operators

open finset

#check real.sqrt (2:ℝ)

noncomputable def φ : ℝ:= (1 + real.sqrt 5)/2

-- defining what a base expansion is
-- a m = d_(m-r)
noncomputable def base (r : ℕ) (k : ℕ) (a : ℕ → ℕ) (x : ℝ) : ℝ := 
∑ i in range (k+r+1), a (i) * x ^ ((i:ℤ) -r)

#eval nat.div 5 2
#eval nat.floor 2.5
#eval 2 % 10

-- binary number to binary sequence representation
-- 1011 → [1, 1, 0, 1]
def bin_to_fun (n : ℕ) : ℕ → ℕ :=
λ x, (n / (10^x)) % 10

def f := bin_to_fun 101011
#eval f 5

def g := bin_to_fun 1101

theorem n1 : base 0 3 (bin_to_fun 1101) φ = 1 + φ^2 + φ^3 :=
begin
  rw [base],
  repeat {rw sum_range_succ},
  rw sum_range_zero,
  simp,
  rw bin_to_fun, simp,
  norm_num,
  refl,
end

example : φ^2  = (3 + real.sqrt 5) / 2:=
begin
  rw φ,
  ring_exp,
  have : real.sqrt 5 ^ 2  = 5,
  {apply real.sq_sqrt, norm_num,},
  rw this, ring,
end

theorem n2 : 1 + φ^2 + φ^3 = 1/2 *(9 + 3* real.sqrt(5)) :=
begin
  rw φ,
  ring_exp,
  have : real.sqrt 5 ^ 2  = 5,
  {apply real.sq_sqrt, norm_num,},
  rw this,
  ring,
  rw this, ring,
end

theorem n3 : base 0 3 (bin_to_fun 1101) φ = 1/2 *(9 + 3* real.sqrt(5)) :=
begin
rw [n1, n2],
end

-- shift over by r (the -r bottom limit)
def duh (r : ℕ) (n : ℕ): ℕ := n

example (n m : ℝ)(h : n≠ 0): m* n/n = m :=
begin
exact (div_eq_iff h).mpr rfl,
end

theorem lol : φ ≠ 0 :=
begin
  rw φ,
  have h := real.sqrt_nonneg 5,
  linarith,
end

example (n : ℕ) (h : n ≠ 0) : n^2 ≠ 0:=
by library_search

theorem hi (n m : ℕ) (x : ℝ) (h : x ≠ 0) : x^(n+m) / x^m = x^n :=
begin
  have w := pow_ne_zero m h,
  have : x^(n+m) = x^n * x^m, ring_exp,
  rw this,
  exact (div_eq_iff w).mpr rfl,
end

theorem hi2 (n m : ℕ) (x : ℝ) (h : x ≠ 0) : x^m / x^(m+n) = 1/x^n :=
begin
  have w := pow_ne_zero m h,
  have : x^(m+n) = x^m * x^n, ring_exp,
  rw this,
  have :  (1/x^n)*x^m /x^m = (1/x^n),
  exact (div_eq_iff w).mpr rfl,
  library_search,
end

def b (n : ℕ): ℚ :=
((λ (p : ℚ × ℚ), (p.snd, p.fst + p.snd))^[n] (0, 1)).fst
def a (n : ℕ): ℚ :=
((λ (p : ℚ × ℚ), (p.snd, p.fst + p.snd))^[n] (2, 1)).fst


theorem a_add (n : ℕ) : a (n+2) = a n + a (n + 1) := 
begin
simp only [a, function.iterate_succ'],
end

theorem b_add (n : ℕ) : b (n+2) = b n + b (n + 1) := 
begin
simp only [b, function.iterate_succ'],
end

-- a n = a (n-1) + b (n-1)
theorem ab_fib (n : ℕ) : 
(a (n+2) : ℚ) = (a (n+1)   + 5* b (n+1) )/2
∧ (b (n+2):ℚ)  = (a (n+1) + b (n+1) : ℚ)/2 := 
begin
  induction n with d dh,
  {
    split,
    simp [a,b], norm_num,
    simp [a, b],
  },

  have t : d.succ + 2 = (d + 2) + 1, ring,
  have u : d.succ + 1 = (d + 1) + 1, ring,

  split,
  {  
    cases dh with l r,
    rw [t, u],
    rw l, rw r,
    rw a_add,
    suffices : (a (d + 1) + a (d + 1 + 1)) = (3*a (d+1) + 5 * b (d+1)) / 2, 
      rw this,
      ring, 
    suffices : a (d + 1) + (a (d+1) + 5 * b (d+1))/2 = (3 * a (d + 1) + 5 * b (d + 1)) / 2,
      rw ← this, rw l, ring,
  }, 
  {
    cases dh with l r,
    rw [t, u], rw b_add,
    rw l, rw r, ring,
  },
end

theorem phi_fib (n : ℕ): φ^(n+2) = φ^(n+1)+ φ^n :=
begin
  suffices : φ^n *(φ^2) = φ^n *(φ + 1),
  ring_exp, ring_exp at this, 
  rw this,

  suffices : φ^2 = φ + 1,
  exact congr_arg (has_mul.mul (φ ^ n)) this,
  rw φ, ring_exp,
  rw real.sq_sqrt, ring,
  norm_num,
end

-- for n ≥ 1, coffecients of φ^n are 'fibannaci'
theorem phi_pow_eq_fib (n : ℕ) :
 φ^(n+1)= ((a (n+1)) + (b (n+1)) * real.sqrt 5) /2 :=
begin
  induction n with d, 
  rw [a, b], rw φ,
  simp,

  rw pow_succ',
  rw n_ih,
  have t := ab_fib d,
  cases t with l r,
  rw l, rw r,
  rw φ, ring_exp, rw real.sq_sqrt,
  field_simp, ring, linarith,
end

theorem phi3 : φ^3 = ((a (3)) + (b (3)) * real.sqrt 5) /2 :=
begin
  have : 3 = 2+1, refl,
  rw this,
  rw phi_pow_eq_fib,
end

theorem powa (n : ℕ): φ^n = φ^(n : ℤ) :=
begin
refl,
end

theorem m1 : base 3 3 (bin_to_fun 1101011) φ = 4 + 2 * real.sqrt 5 :=
begin
  rw [base, bin_to_fun],
  repeat {rw sum_range_succ},
  simp,
  norm_num,
  have : φ^3 = φ^(3 : ℤ), refl,
  rw phi3 at this, rw ← this, rw a, simp,
end

-- outputs a function f such that:
-- f(x) = 1 when x > n
-- f(x) = 0 otherwise
def ge_switch (n : ℕ): ℕ → ℕ :=
λ x, (x - n) / (x - n)
def notl (f : ℕ → ℕ): ℕ → ℕ :=
λ x, (f x + 1) % 2
lemma not0 (f : ℕ → ℕ) (x : ℕ): f x = 0 → notl f x = 1 :=
begin
  intro p,
  simp [notl], rw p, refl,
end
lemma not1 (f : ℕ → ℕ) (x : ℕ): f x = 1 → notl f x = 0 :=
begin
  intro p,
  simp [notl], rw p, refl,
end

-- outputs 1 iff x = n
def eq_switch (n : ℕ) : ℕ → ℕ :=
(notl (ge_switch n)) * ge_switch (n-1)

lemma eqs1 (n x : ℕ) (h : n≠ 0) : 
x = n → eq_switch n x = 1 := 
begin
  intro p, rw p,
  simp [eq_switch, notl, ge_switch],
  have : n - (n-1) = 1,
  {
    induction n, tauto,
    norm_num,
    have : n_n.succ = n_n + 1:= by refl,
    rw this, norm_num,
  },
  rw this, refl,
end

lemma eqs2 (n x : ℕ) (h : n≠ 0) : 
x ≠ n → eq_switch n x = 0 := 
begin
  intro p,
  simp [eq_switch, notl, ge_switch],
  have : x < n ∨ x > n := by exact ne.lt_or_lt p,
  cases this with l r,
  {
    right,
    have : x ≤ n-1, exact nat.le_pred_of_lt l,
    have : x - (n-1) = 0, exact tsub_eq_zero_of_le this,
    rw this, refl,
  },
  {
    left,
    have : x - n > 0, exact tsub_pos_of_lt r,
    have : (x - n) / (x - n) = 1, exact nat.div_self this,
    rw this, refl,
  },
end

-- outputs function g such that:
-- g(n+2) = 1
-- g(n+1) = 0
-- g(n) = 0
-- g(x) = f(x) otherwise
-- single fib convolution
def fibl (f : ℕ → ℕ) (n : ℕ) : ℕ → ℕ :=
λ x, 
(eq_switch (n+2) x) * 1 
+ (eq_switch (n+1) x) * 0 
+ (eq_switch n x) * 0
+ (notl (eq_switch n)*notl (eq_switch (n+1)) * notl (eq_switch (n+2))) x * f x
lemma fibl0 (x n : ℕ) (f : ℕ → ℕ) (h : n ≠ 0): (x = n ∨ x = n+1) → fibl f n x = 0 :=
begin
  intro p,
  rw [fibl], simp,
  split,
  {
    apply eqs2 (n+2) x,
    exact (n + 1).succ_ne_zero,
    cases p with l r,
    linarith, linarith,
  },
  {
    left, left,
    cases p with l r,
    {
      left,
      apply not1,
      apply eqs1, exact h, exact l,
    },
    {
      right,
      apply not1, apply eqs1,
      linarith, exact r,
    },
  },
end
lemma fibl1 (x n : ℕ) (f : ℕ → ℕ) (h : n ≠ 0): x = n+2 → fibl f n x = 1 :=
begin
  intro p,
  rw [fibl], simp,
  have : n+2 ≠ 0, linarith,
  simp [eqs1 (n+2) x this p],

  left, right,
  apply not1, apply eqs1,
  linarith, exact p,
end
lemma fiblx (x n : ℕ) (f : ℕ → ℕ) (h : n ≠ 0): x ≠ n ∧ x ≠ n+1 ∧ x ≠ n+2 → fibl f n x = f x :=
begin
  intro p,
  rcases p with ⟨l, m, r⟩,
  simp [fibl],
  rw eqs2 (n+2) x, simp,
  {
    rw not0 (eq_switch n) x (eqs2 n x h l), simp,
    have : n+1 ≠ 0, linarith,
    rw not0 (eq_switch (n+1)) x (eqs2 (n+1) x this m), simp,
    have : n+2 ≠ 0, linarith,
    rw not0 (eq_switch (n+2)) x (eqs2 (n+2) x this r), simp,
  },
  linarith, exact r,
end
-- 1 if x == 1, 0 otherwise
def eq_one : ℕ → ℕ :=
λ x, x

#eval eq_one 0

-- does fib convolution iff g(n) = g(n+1) = 1
-- single conditional fib convolution
def fiblc (f : ℕ → ℕ) (n : ℕ) : ℕ → ℕ :=
λ x, 
(fibl f n) x + f x * (f n * f (n+1))

def bin (f : nat → nat) := ∀ x, f x = 0 ∨ f x = 1
lemma bin_mul (f g : nat → nat) (hf : bin f) (hg : bin g): bin (f * g) :=
begin
  rw bin, rw bin at hf, rw bin at hg,
  intro x,

  simp,
  specialize hf x, specialize hg x,
  cases hf,
  {
    left, left, exact hf,
  },
  {
    cases hg,
      left, right, exact hg,
      simp only [hf, hg, nat.one_ne_zero, mul_one, false_or],
  },
end

def br : ℕ → ℕ := λ x, x

def convolute (g : (ℕ → ℕ) → ℕ → (ℕ → ℕ)) (f : ℕ → ℕ)
(a : ℕ) : ℕ → (ℕ → ℕ)
| nat.zero := g f a 
| (nat.succ n) := g (convolute n) (a - nat.succ n)

-- we call a numbering sparse if it's no two digits are both 1
def sparse (f : ℕ → ℕ) :=
¬(∃ x : ℕ,  f x = 1 ∧ f (x + 1) = 1 )
def sparse' (f : ℕ → ℕ) (a n : ℕ) :=
∀  x : ℕ, (x ≤ a ∧ x ≥ (a - n)) →  ¬ (f x = 1 ∧ f (x + 1) = 1)

example (a n : ℕ) (h : n ≤ a) (f : ℕ → ℕ)
: sparse' (convolute fiblc f a n) a n :=
begin
induction n with k,
simp only [sparse'],
rw convolute,
intros x h1,

end


#check nat
-- #eval (fibl br 5) 4
-- #eval (fibl br 5) 5
-- #eval (fibl br 5) 6
-- #eval (fibl br 5) 7
-- #eval (fibl br 5) 8

