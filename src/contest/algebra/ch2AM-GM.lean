import .ch1basics
import analysis.mean_inequalities

import tactic.monotonicity
import data.finset
open_locale classical big_operators nnreal ennreal
noncomputable theory

open finset

#check prod_pow
#check mul_sum
-- AM-GM proof projection to nonweighted exponents
lemma prod_ge_zero (n : ℕ) (a : ℕ → ℝ) (h : ∀ i : ℕ, a i ≥ 0) :
∏ i in range n, (a i) ≥ 0:=
begin
  induction n with d dh,
  norm_num,
  rw prod_range_succ,
  exact mul_nonneg dh (h d),
end
lemma rprod_pow (n : ℕ) (a : ℕ → ℝ) (b : ℝ) (h : ∀ i : ℕ, a i ≥ 0)
: ∏ i in range n, (a i)^b = (∏ i in range n, (a i))^b :=
begin
  induction n with d dh,
  norm_num,

  simp only [prod_range_succ, dh],
  rw real.mul_rpow,
    exact prod_ge_zero d a h,
    exact h d,
end
lemma curry3 (A B C D : Prop): ((A ∧ B ∧ C) → D) ↔ (A → B → C → D) :=
begin
tauto,
end
theorem AMGM (n : ℕ) (hn : n ≠ 0) (a : ℕ → ℝ) (h : ∀ i:ℕ, a i ≥ 0):
(∑ i in range n, a i)/ n ≥ ( ∏ i in range n, a i)^(1/(n:ℝ)) :=
begin
suffices p : ∏ (i : ℕ) in range n, a i ^ (λ (x : ℕ), 1 / (n:ℝ)) i ≤ ∑ (i : ℕ) in range n, (λ (x : ℕ), 1 / (n:ℝ)) i * a i
,
{
  simp at p,
  rw rprod_pow n a ((↑n)⁻¹) h at p,
  rw ← mul_sum at p,
  have : (↑n)⁻¹ = 1/(n:ℝ), field_simp,
  rw this at p, field_simp at p,
  linarith,
},
have := real.geom_mean_le_arith_mean_weighted (range n : finset ℕ)
  (λ x, 1/n) a,
rw ← curry3 at this,
apply this,

split,
 
{
  intros,
  exact one_div_nonneg.mpr (nat.cast_nonneg n),
},
{
  simp, have : (n : ℝ) ≠ 0 := by exact nat.cast_ne_zero.mpr hn,
  field_simp,
  intros,
  exact h i,
},
end

-- 2.4

-- finite functions using matrix notation
def f : fin 3 → ℚ := ![3, 2, 1]

-- convert finite function to 'total' (takes any natural number input)
def to_total {n : ℕ} {α : Type} [inhabited α] (f : fin n → α) : ℕ → α := 
λ (m : ℕ), dite (m < n) (λ p : m < n, f ⟨m, p⟩) (λ p : ¬m < n, inhabited.default α)

-- example conversion
def f' := to_total f

def min_val' (f : ℝ → ℝ) (a : nnreal) := ∀ (x:nnreal), f x ≥ f a 
example : ℚ → (fin 3 → ℚ):=
begin
intro x,
exact ![x, x, x],
end

#check real.exp_sum
#check real.exp_mul
#check real.rpow_def_of_pos
#check nnreal.div_rpow
#check nnreal.mul_rpow
#check dite_eq_iff

lemma noice (x : ℝ) (h : 0 < x) : 
x ^ (1 / 2 : ℝ) * ((1:ℝ) / x) ^ (1 / 2 : ℝ) ≤ (x + 2 / (2 * x)) / 2 :=
begin
  have h := to_total (![x, 1/x]),
  have := real.geom_mean_le_arith_mean_weighted ({0, 1} : finset ℕ)
  (λ x, 1/2) (to_total (![x, 1/x])),
  norm_num at this,
  simp [to_total] at this,
  have l : 0 ≤ x, linarith,
  have := this l l,
  field_simp at this,
  refine this,
end

example (x : ℝ) (h : 0 < x) : x+ 1/x ≥  1 :=
begin
  have n := noice x h,
  have h1 : 1/x > 0, exact one_div_pos.mpr h,

  have : x ≠ 0, linarith,
  have : 1/x ≠ 0, linarith,
  have : x ^ (1 / 2:ℝ) * (1 / x) ^ (1 / 2:ℝ) = 1,
  { 
    rw ← real.mul_rpow _ _,
    field_simp, 
    linarith, linarith,
  },
  rw this at n,
  have : x + 2 / (2 * x :ℝ) = x + 1/x,
  {
    field_simp, ring_nf,
  },
  rw this at n,
  linarith,
end

lemma tototal_nonneg (n : ℕ) (f : fin n → ℝ) : 
(∀ (k : ℕ), k ∈ range n → to_total f k ≥ 0) → ∀ i : ℕ, (to_total f) i ≥ 0 :=
begin
intros p i,
cases em (i < n),
{
  have : i ∈ range n := mem_range.mpr h,
  exact p i this,
},
{
  have :  to_total f i = 0,
    rw [to_total, dite_eq_iff], right,
    use h, refl,
  linarith,
},
end

theorem AMGM' (n : ℕ) (hn : n ≠ 0) (a : fin n → ℝ) (h : ∀ (k : ℕ), k ∈ range n → to_total a k ≥ 0):
(∑ i in range n, to_total a i)/ n ≥ ( ∏ i in range n, to_total a i)^(1/(n:ℝ)) :=
begin
  exact AMGM n hn (to_total a) (tototal_nonneg n a h),
end

example (a b : ℝ) (h : a < b) : a ≤ b :=
begin
exact le_of_lt h,
end

example (x : ℝ) (h : 0 < x) : x+ 1/x ≥  2 :=
begin
have : x ≠ 0, linarith,
have : ∀ (k : ℕ), k ∈ range 2 → to_total ![x, 1 / x] k ≥ 0, {
  intro k,
  norm_num [range],
  intro p, rcases p,
  rw p, 
  exact le_of_lt (one_div_pos.mpr h),
  rw p, exact le_of_lt h,
},
have l1 := AMGM 2 two_ne_zero (to_total ![x, 1/x]) (tototal_nonneg 2 (![x, 1/x]) this),
norm_num [range, to_total] at l1,
field_simp at l1,
have : (1 + x * x) / (x * 2) = (x + 1/x)/2, field_simp, ring_nf,
rw this at l1,
linarith,
end

meta def bruhlol : tactic unit :=
do { 
  `[intro k],
  `[norm_num [range]],
  `[intro p],
  `[repeat {any_goals {cases p}}],
  `[skip]
} <|> tactic.fail "failed to simplify range expression"

example (x : ℝ) (h : 0 < x) : x+ 1/x ≥  2 :=
begin
have l1 : (∀ (k : ℕ), k ∈ range 2 → to_total ![x, 1 / x] k ≥ 0),
  bruhlol,
  exact le_of_lt (one_div_pos.mpr h),
  exact le_of_lt h,

  have l2 := AMGM' 2 two_ne_zero (![x, 1/x]) l1,
  norm_num [range, to_total] at l2,
  
  have := ne_of_gt h,
  field_simp at l2,
  have : (1 + x * x) / (x * 2) = (x + 1/x)/2 := by {field_simp, ring_nf}, 
  rw this at l2,

  linarith,
end

-- 2.6
example (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0): 
(a+b)/c + (b+c)/a + (c+a)/b ≥ 6 :=
begin
-- have : 3 ≠ 0, library_search,
-- have := AMGM' 6 (nat.succ_ne_zero 5) (![a/b, b/c, b/a, c/a, c/b, a/b]),
have : (∀ (k : ℕ), k ∈ range 6 → to_total ![a / c, b / c, b / a, c / a, c / b, a / b] k ≥ 0),
bruhlol,
norm_num [to_total],
exact le_of_lt (div_pos ha hb), -- to be automated by tactic
exact le_of_lt (div_pos hc hb), -- to be automated by tactic
exact le_of_lt (div_pos hc ha), -- to be automated by tactic
exact le_of_lt (div_pos hb ha), -- to be automated by tactic
exact le_of_lt (div_pos hb hc), -- to be automated by tactic
exact le_of_lt (div_pos ha hc), -- to be automated by tactic

have := AMGM' 6 (nat.succ_ne_zero 5) (![a/c, b/c, b/a, c/a, c/b, a/b]) this,
norm_num [range] at this,
simp [to_total] at this,
have na:= ne_of_gt ha, -- to be automated by tactic
have nc:= ne_of_gt hc, -- to be automated by tactic 
have nb:= ne_of_gt hb, -- to be automated by tactic
have l :  (a / b * (c / b * (c / a * (b / a * (b / c * (a / c)))))) = 1,
field_simp, ring,
rw l at this,
norm_num at this,
have : (a / b + (c / b + (c / a + (b / a + (b / c + a / c))))) = (a+b)/c + (b+c)/a + (c+a)/b,
ring,
rw ← this,
linarith,
end

-- 2.7

#check real.mul_rpow
#check real.rpow_mul
example (a : ℕ) (ha : a > 0) : a^3 > 0 :=
begin
library_search,
end
lemma duh {a b c d: ℝ} (h : c ≥ d) : a = c → b=d → a ≥ b :=
begin
intros h1 h2,
rw [h1, h2], exact h,
end
lemma l271 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0): 
(a^(3:ℝ) + a^(3:ℝ) + b^(3:ℝ))/3 ≥ a^(2:ℝ)*b:=
begin
have l : (∀ (k : ℕ), k ∈ range 3 → to_total ![a ^ (3:ℝ), a ^ (3:ℝ), b ^ (3:ℝ)] k ≥ 0),
bruhlol,
exact le_of_lt (real.rpow_pos_of_pos hb 3),
exact le_of_lt (real.rpow_pos_of_pos ha 3),
exact le_of_lt (real.rpow_pos_of_pos ha 3),

have := AMGM' 3 (nat.succ_ne_zero 2) (![a^(3:ℝ), a^(3:ℝ), b^(3:ℝ)]) l,
norm_num [range, to_total] at this,
ring_exp at this,
rw real.mul_rpow at this,
rw ← real.rpow_mul (le_of_lt hb) (3:ℝ) (1/(3:ℝ)) at this,
rw ← real.rpow_nat_cast (a^(3:ℝ)) 2 at this,
rw ← real.rpow_mul (le_of_lt ha) (3:ℝ) (2:ℕ) at this,
rw ← real.rpow_mul (le_of_lt ha) ((3:ℝ)*(2:ℕ)) (1/(3:ℝ)) at this,
norm_num at this,
apply duh this,
ring, ring_nf,
exact le_of_lt (real.rpow_pos_of_pos hb 3),
have := le_of_lt (real.rpow_pos_of_pos ha 3),
exact sq_nonneg (a ^ 3),
end

-- note: ↑3 is the coercion of the **natural number** 3 to the real numbers
-- (3:ℝ) is the **real number** 3
-- these two things are definitionally equal but not syntactically equal
lemma imp_trans {P Q R: Prop} (h : P → Q) (h' : P) (h1: Q → R) : R :=
begin
exact h1 (h h'),
end
example (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0): 
a^3 + b^3 + c^3 ≥ a^2*b + b^2*c + c^2*a:=
begin
have := l271 ha hb hc,
have := l271 hc ha hb,
have := l271 hb hc ha,

 -- converts exponents from nats, to coexerced nats, to real numbers
simp only [← real.rpow_nat_cast], norm_num,
linarith,
end

-- 2.8
lemma AMGM2 (a b : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) :
(a+b)/2 ≥ (a*b)^(1/(2:ℝ)):=
begin
have := AMGM' 2 (nat.succ_ne_zero 1) (![a,b]),
apply imp_trans this,
bruhlol,
exact hb,
exact ha,
intro p,
norm_num [range] at p,
simp [to_total] at p,
apply duh p,
ring,
ring,
end
lemma AMGM3 (a b c: ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) :
(a+b+c)/3 ≥ (a*b*c)^(1/(3:ℝ)):=
begin
have := AMGM' 3 (nat.succ_ne_zero 2) (![a,b,c]),
apply imp_trans this,
bruhlol,
exact hc,
exact hb,
exact ha,
intro p,
norm_num [range] at p,
simp [to_total] at p,
apply duh p,
ring,
ring,
end
lemma AMGM4 (a b c d : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hd : d ≥ 0):
(a+b+c+d)/4 ≥ (a*b*c*d)^(1/(4:ℝ)):=
begin
have := AMGM' 4 (nat.succ_ne_zero 3) (![a,b,c,d]),
apply imp_trans this,
bruhlol,
exact hd,
exact hc,
exact hb,
exact ha,
intro p,
norm_num [range] at p,
simp [to_total] at p,
apply duh p,
ring,
ring,
end

lemma AMGM5 (a b c d e : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hd : d ≥ 0) (he : e ≥ 0):
(a+b+c+d+e)/5 ≥ (a*b*c*d*e)^(1/(5:ℝ)):=
begin
have := AMGM' 5 (nat.succ_ne_zero 4) (![a,b,c,d, e]),
apply imp_trans this,
bruhlol,
exact he,
exact hd,
exact hc,
exact hb,
exact ha,
intro p,
norm_num [range] at p,
simp [to_total] at p,
apply duh p,
ring,
ring,
end

lemma l281 {a : ℝ} (ha : a > 0) : (a^(1/(5:ℝ)))^5 = a :=
begin
rw ← real.rpow_nat_cast _ 5,
rw ← real.rpow_mul,
norm_num,
exact le_of_lt ha,
end
example (a b c d : ℝ) : a ≤ b → c ≤ d → a + c ≤ b + d :=
begin
intro p,
exact add_le_add p,
end
#check le_of_pow_le_pow
#check pow_le_pow_of_le_left'
example (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a + b = 1): 
a^2*b^3 ≤ (108:ℚ)/3125:=
begin
have l1 := le_of_lt (half_pos ha),
have : b/3 > 0, linarith,
have l2 := le_of_lt this,
have l := AMGM5 (a/2) (a/2) (b/3) (b/3) (b/3) l1 l1 l2 l2 l2,
ring, ring_nf at l,
have : 1 / 5 * a + 1 / 5 * b = 1/5, linarith,
rw this at l,

have p1 :=  mul_pos (pow_pos hb 3) (pow_pos ha 2),
have p : (1 / 108 * b ^ 3 * a ^ 2)^(1/(5:ℝ)) > 0, 
{
  have p1: b^3 > 0,  exact pow_pos hb 3,
  have p2 := pow_pos ha 2,
  have : b ^ 3*a^2 > 0, exact mul_pos p1 p2,
  have : 1 / 108 * b ^ 3 * a ^ 2 > 0, linarith,
  exact real.rpow_pos_of_pos this (1 / 5),
  
},
have q : 1 / (3125:ℝ) * (108:ℚ) >0, norm_num,
have p' := pow_le_pow_of_le_left (le_of_lt p) l 5,
norm_num at p', 
rw [← real.rpow_nat_cast, ← real.rpow_mul] at p',
norm_num at p',
norm_num, linarith,
linarith,
end

-- 2.9
example (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (h : x*y*z = 32):
x^2 + 4*x*y + 4*y^2+2*z^2 ≥ 96:=
begin
suffices : 4*x*y+4*x*y+2*z^2 ≥ 96,
have : x^2+4*x*y+4*y^2 ≥ 8*x*y,
suffices : (x-2*y)^2 ≥ 0, ring_nf at this, linarith,
exact sq_nonneg (x-2*y),
linarith,
have l := AMGM3 (4*x*y) (4*x*y) (2*z^2) _ _ _,
have :4 * x * y * (4 * x * y) * (2 * z ^ 2) = 32*(x*y*z)^2 := by ring,
rw [this, h] at l, 
have : (32:ℝ)*32^2 = 32^3 := by refl,
rw this at l,
rw ← real.rpow_nat_cast _ 3 at l, -- to be replaced by tactic
rw ← real.rpow_mul at l, -- to be replaced by tactic
norm_num at l, -- to be replaced by tactic
linarith,

norm_num,
linarith [le_of_lt (mul_pos hx hy)], 
linarith [le_of_lt (mul_pos hx hy)], 
linarith [sq_nonneg z], 
end

-- 2.10
example {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) :
a ≥ b → c/a ≤ c/b :=
begin
exact (div_le_div_left hc ha hb).mpr,
end
lemma l210 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) :
a /(a+2*(b*c)^(1/(2:ℝ))) ≥ a / (a+b+c) :=
begin
have := AMGM2 b c (le_of_lt hb) (le_of_lt hc),
have l: a + b + c ≥ a + 2*(b*c)^(1/(2:ℝ)),
linarith,

have : b*c > 0 := by exact mul_pos hb hc,
have : (b*c)^(1/(2:ℝ)) > 0, exact real.rpow_pos_of_pos this (1 / 2), 
have l1 : a+2*(b*c)^(1/(2:ℝ)) > 0 := by linarith,
have l2 : a+b+c > 0 := by linarith,
exact (div_le_div_left ha l2 l1).mpr l,
end

example (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) :
a /(a+2*(b*c)^(1/(2:ℝ))) + b /(b+2*(c*a)^(1/(2:ℝ))) + c /(c+2*(a*b)^(1/(2:ℝ))) ≥ 1 :=
begin
have pc: a + b + c = c + a + b, linarith, -- to be automated by tactic
have pb: a + b + c = b + c + a, linarith, -- to be automated by tactic

have l1:= l210 ha hb hc,
have l2:= l210 hc ha hb,
rw ← pc at l2, -- to be automated by tactic
have l3:= l210 hb hc ha,
rw ← pb at l3, -- to be automated by tactic

have l : a /(a+2*(b*c)^(1/(2:ℝ))) + b /(b+2*(c*a)^(1/(2:ℝ))) +c /(c+2*(a*b)^(1/(2:ℝ))) 
≥ a/(a+b+c)+b/(a+b+c)+c/(a+b+c),
linarith,

have : a / (a + b + c) + b / (a + b + c) + c / (a + b + c) = (a+b+c)/(a+b+c) := by ring,
rw this at l,
have : a+b+c > 0 := by linarith, have : a+b+c ≠ 0, exact ne_of_gt this,
field_simp at l,
exact l,
end

-- 2.11
lemma l21105 {a : ℝ} (ha : a ≥ 1) : 3*a^2+1 ≠ 0 :=
begin
have : a^2 ≥ 1, exact one_le_pow_of_one_le ha 2,
linarith,
end

lemma div_ge_zero {a b : ℝ} (ha : a > 0) : b ≥ 0 → b/a ≥ 0 :=
begin
intro,
have : 1/a > 0, exact one_div_pos.mpr ha,
have : 1/a ≥ 0, linarith,
have : (1/a)*b ≥ 0, exact mul_nonneg this ᾰ,
apply duh this, ring, refl,
end

-- to be automated by tactic that proves inequalities over monotomic Functions
-- by substituting lower bound points
lemma l211divcyc {a b c : ℝ} (ha : a ≥ 1) (hb : b ≥ 1) (hc : c ≥ 1):
(a * (b ^ 2 + 3)) / (3 * c ^ 2 + 1) ≥ 0 :=
begin
  have : b^2 ≥ 1, exact one_le_pow_of_one_le hb 2,
  have l :  b^ 2 + 3 ≥ 0, linarith,

  have : c^2 ≥ 1, exact one_le_pow_of_one_le hc 2,
  have :  3*c^ 2 + 1 > 0, linarith,
  apply div_ge_zero this,

  have : a ≥ 0, linarith,
  exact mul_nonneg this l,
  end
  lemma l2111 {a b c : ℝ} (ha : a ≥ 1) (hb : b ≥ 1) (hc : c ≥ 1):
  a*(a^2+3)/(3*a^2+1) ≥ 1 :=
  begin
  have : a^2 ≥ 1, exact one_le_pow_of_one_le ha 2,
  have l : 3*a^2 + 1 > 0, linarith,

  suffices : a * (a ^ 2 + 3) ≥ (3 * a ^ 2 + 1),
  exact (one_le_div l).mpr this,

  suffices : (a-1)^3 ≥ 0,
  linarith,

  have : a - 1 ≥ 0 := sub_nonneg.mpr ha,
  exact pow_nonneg this 3,
end

#check real.le_rpow_of_log_le
lemma l2112 (a : ℝ) : a ≥ 1 → a^(1/(3:ℝ)) ≥ 1 :=
begin
intro p,
apply real.le_rpow_of_log_le,
linarith, linarith,
simp,
have : real.log a ≥ 0, exact real.log_nonneg p,
norm_num, exact this,
end

example (a b c : ℝ) (ha : a ≥ 1) (hb : b ≥ 1) (hc : c ≥ 1):
a*(b^2+3)/(3*c^2+1)+c*(a^2+3)/(3*b^2+1)+b*(c^2+3)/(3*a^2+1) ≥ 3 :=
begin
have p := AMGM3 (a*(b^2+3)/(3*c^2+1)) (c*(a^2+3)/(3*b^2+1)) (b*(c^2+3)/(3*a^2+1)) _ _ _,
suffices : (a * (b ^ 2 + 3) / (3 * c ^ 2 + 1) * (c * (a ^ 2 + 3) / (3 * b ^ 2 + 1)) * (b * (c ^ 2 + 3) / (3 * a ^ 2 + 1))) ^ (1 / (3:ℝ)) ≥ 1,
linarith,

suffices : (a * (b ^ 2 + 3) / (3 * c ^ 2 + 1) * (c * (a ^ 2 + 3) / (3 * b ^ 2 + 1)) * (b * (c ^ 2 + 3) / (3 * a ^ 2 + 1))) ≥ 1,
exact l2112 (a * (b ^ 2 + 3) / (3 * c ^ 2 + 1) * (c * (a ^ 2 + 3) / (3 * b ^ 2 + 1)) * (b * (c ^ 2 + 3) / (3 * a ^ 2 + 1)))
  this,

have la := l2111 ha hb hc,
have lc := l2111 hc ha hb,
have lb := l2111 hb hc ha,

have lac := one_le_mul_of_one_le_of_one_le la lc,
have lacb := one_le_mul_of_one_le_of_one_le lac lb,
apply duh lacb,

have := l21105 ha, have := l21105 hb, have := l21105 hc,
field_simp, ring,

refl,
exact l211divcyc ha hb hc,
exact l211divcyc hc ha hb,
exact l211divcyc hb hc ha,
end


-- monotonicity related tactics (ac_mono, mono) can be used to prove "obvious" inequalities
#check monotone (^)
example (x y z k m n : ℕ)
  (h₀ : z ≥ 0)
  (h₁ : x ≤ y) :
  (m + x + n) * z + k ≤ z * (y + n + m) + k :=
begin
ac_mono,
ac_mono,
ac_mono,
end

example (x y z k m n : ℕ)
  (h₀ : z ≥ 0)
  (h₁ : x ≤ y) :
  x^z ≤ y^z :=
begin
ac_mono,
end

-- simpler proof of lemma l1211divcyc using monotonicity
example {a b c : ℝ} (ha : a ≥ 1) (hb : b ≥ 1) (hc : c ≥ 1):
0 ≤ (a * (b ^ 2 + 3)) / (3 * c ^ 2 + 1) :=
begin
have : a*0/ (3 * c ^ 2 + 1) ≤ a * (b ^ 2 + 3) / (3 * c ^ 2 + 1) ,
mono,
{
  have : 1^2 ≤ c^2, mono, norm_num,
  linarith,
},
{
  mono,
  have : 1^2 ≤ b^2, mono, norm_num,
  linarith,
  linarith,
},
norm_num at this,
exact this,
end

-- 2.12
#check real.rpow_pos_of_pos
#check real.rpow_nonneg_of_nonneg
example (a : ℝ) (h : a ≥ 0) : a^(1/(3:ℝ)) ≥ 0 :=
begin
library_search,
end
lemma pow3_explode {a : ℝ} (ha : a ≥ 0) : (a^(1/(3:ℝ)))^3 = a :=
begin
rw ← real.rpow_nat_cast _ 3,
rw ← real.rpow_mul,
norm_num,
exact ha,
end
example (a b:ℝ) : a ≥ b → b ≤ a :=
begin
exact ge.le,
end

lemma l2121 {a b c : ℝ} (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) :
27*(a^2+b^2+c^2)*(a*b+b*c+c*a)^2 ≤ (a+b+c)^6 :=
begin
  have p := AMGM3 (a^2+b^2+c^2) (a*b+b*c+c*a) (a*b+b*c+c*a) _ _ _,
  have l :  (a^2+b^2+c^2) + (a * b + b * c + c * a) + (a * b + b * c + c * a) = (a+b+c)^2,
  ring,
  rw l at p,
  have crux : (a ^ 2 + b ^ 2 + c ^ 2) * (a * b + b * c + c * a) ^ 2 ≥ 0,
  {
    have u1:= sq_nonneg (a * b + b * c + c * a),
    have u2: a^2+b^2+c^2 ≥ 0, linarith [sq_nonneg a, sq_nonneg b, sq_nonneg c],
    exact mul_nonneg u2 u1,
  },
  have : (((a ^ 2 + b ^ 2 + c ^ 2) * (a * b + b * c + c * a) * (a * b + b * c + c * a)) ^ (1 / (3:ℝ)))^3 ≤ ((a + b + c) ^ 2 / (3:ℝ))^3,
    mono,
    {
      have : (a * b + b * c + c * a) * (a * b + b * c + c * a) =(a * b + b * c + c * a)^2,
      ring,
      rw [mul_assoc, this],
      exact real.rpow_nonneg_of_nonneg crux _,
    },

  have : (a + b + c) ^ 6 = ((a + b + c) ^ 2)^3 := by ring,
  rw this,
  have : 27 * (a ^ 2 + b ^ 2 + c ^ 2) * (a * b + b * c + c * a) ^ 2 ≥ 0,
  linarith,
  rw ← pow3_explode this,

  mono with [0 ≤ 3],
    norm_num,
    exact real.rpow_nonneg_of_nonneg this (1/(3:ℝ)),
  rw [mul_assoc,real.mul_rpow],
  norm_num,
  have : (27:ℝ) = 3^3, norm_num,
  rw this,
  rw [←  real.rpow_nat_cast, ← real.rpow_mul],
  norm_num,
  have : (a * b + b * c + c * a) * (a * b + b * c + c * a) = (a * b + b * c + c * a)^2,
  ring,
  rw [mul_assoc,this] at p,
  linarith,

  norm_num, norm_num,
  exact crux,
  linarith [sq_nonneg a, sq_nonneg b, sq_nonneg c],

  repeat {
    linarith [mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg hc ha],
  },
end

example {a b c : ℝ} (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) :
81*a*b*c*(a+b+c)*(a^2+b^2+c^2) ≤ (a+b+c)^6 :=
begin
  have := l2121 ha hb hc,
  apply le_trans _ this,
  have : 27*(a ^ 2 + b ^ 2 + c ^ 2) * (a * b + b * c + c * a) ^ 2 = 27*(a * b + b * c + c * a) ^ 2*(a ^ 2 + b ^ 2 + c ^ 2),
  ring,
  rw this,
  mono with [(a ^ 2 + b ^ 2 + c ^ 2) ≥ 0],

  linarith [sq_nonneg a, sq_nonneg b, sq_nonneg c],
  {
    suffices : 3 * a * b * c * (a + b + c) ≤ (a * b + b * c + c * a) ^ 2,
    linarith,

    suffices : (a*b - b*c)^2+(b*c-c*a)^2+(a*b-c*a)^2 ≥ 0,
    linarith,
    linarith [sq_nonneg (a*b - b*c), sq_nonneg (b*c-c*a), sq_nonneg (a*b-c*a)],
  },
end