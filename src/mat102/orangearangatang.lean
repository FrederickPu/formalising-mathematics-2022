import data.real.basic

namespace orange_1

theorem orange_b : ∀ a : ℕ, 3 ∣ a ∨ 3 ∣ (a + 1) ∨ 3 ∣ (a+2) := begin
intro a, 
induction a with d dh, -- prove via induction on a
simp, -- base case a = 0
-- induction hypothesis P(d) → P(d+1)
cases dh,
{
  right, right,
  exact nat.dvd_add_self_right.mpr dh,
},
cases dh,
left, exact dh,
right, left, exact dh,
end   
def g (n : ℕ) : ℚ := (((2*n^3 + 6*n^2 + 4*n) : ℕ) : ℚ)/(3:ℚ)

example : ∀ n : ℕ, ((g n) ∈ {x : ℚ | ∃ x' : ℕ, x = x'}) := begin
intro n,
simp,
rw g,
have : 2 * n ^ 3 + 6 * n ^ 2 + 4 * n = 2*n*(n+1)*(n+2),
ring,
rw this,
have : 3 ∣ n*(n+1)*(n+2),
{
  cases orange_b n,
  simp only [dvd_mul_of_dvd_left, h],
  cases h,
  simp only [dvd_mul_of_dvd_left, dvd_mul_of_dvd_right, h],
  simp only [dvd_mul_of_dvd_right, h],
},

have : 3 ∣ 2*(n * (n + 1) * (n + 2)),
simp only [dvd_mul_of_dvd_right, this],
have l : 2*n * (n + 1) * (n + 2) = 2*(n * (n + 1) * (n + 2)), ring,
rw ← l at this,
cases this with k hk,
rw hk,
rw mul_comm, simp, rw ← mul_div, rw div_self,
use k, ring,
norm_num,
end

def nat_set := {x : ℚ | ∃ n : ℕ, x = n}
notation `ℕₛ` := nat_set 

def g1 (n : ℚ) : ℚ := (((2*n^3 + 6*n^2 + 4*n)))/3

example (α : Type*) (A B : set α) : A = B ↔ ∀ x, x ∈ A ↔ x ∈ B := begin
refine set.ext_iff,
end 

example : g '' set.univ ≠ {x : ℚ | ∃ n : ℕ, x = n} := begin
rw [ne.def],
rw set.ext_iff,
simp only [not_forall],
suffices : ∃ x : ℚ, x ∈ ℕₛ ∧ ¬ (x ∈ g '' set.univ),
  cases this with x h,
  use x,
  tauto,
use 1,
split,
use 1, refl,
simp [g],
intros x,
have l : x ≥ 1 →  (2 * x ^ 3 + 6 * x ^ 2 + 4 * x : ℚ) / 3 > 1,
intro q,
have w : (x : ℚ) ≥ 1,exact nat.one_le_cast.mpr q,
have : (x:ℚ)^3 ≥ 1, exact one_le_pow_of_one_le w 3, 
have : (x:ℚ)^2 ≥ 1, exact one_le_pow_of_one_le w 2,
linarith,

cases x,
simp,
have : x.succ ≥ 1, exact le_add_self,
have := nat.one_le_cast.mpr this,
linarith [l this],
exact strict_ordered_semiring.to_char_zero,
end 

end orange_1

namespace orange_2
def g : ℕ × ℕ → ℝ := λ ⟨x,y⟩, |x - y|  
example : g '' {xy : ℕ × ℕ | xy.fst ≠ 0 ∧ xy.snd ≠ 0} = {x : ℝ | ∃ n : ℕ, x = n} := begin
ext,
split,
{
  rw g,
  simp only,
  intro h,
  simp only [set.mem_image] at h,
  cases h with x1 hx1,
  cases x1 with a b,
  simp only [ne.def, set.mem_set_of_eq, not_and] at hx1,
  cases hx1,
  simp [g] at hx1_right,
  have : ((|a - b|:ℤ):ℝ) = (|a - b| : ℝ), simp,
  rw ← this at hx1_right,
  have := abs_nonneg (a - b : ℤ),
  have : ∃ (n:ℕ), (n:ℤ) = (|a - b| : ℤ), exact can_lift.prf _ this,
  cases this with n hn,
  simp,
  use n, rw ← hx1_right, rw ← hn, refl,
},
{
  intro h,
  simp at h,
  cases h with n hn,
  simp [g],
  use (n + 1), use 1,
  simp [hn],
},
end

#check odd
end orange_2

namespace orange_4
def P (x : ℝ) := -1 ≤ x ∧ x ≤ 3
def Q (x : ℝ) := x^2 > x
def R (x : ℝ) := x = 1 / 2

example : ∃ x, P x → Q x := begin
use 2,
intro,
norm_num [Q],
end

example : ∀ x : ℝ, (P(x) → (Q(x)∨P(x))) := begin
intro x,
intro p,
right, exact p,
end

lemma lol : ¬ (∀ x : ℝ,(R(x) → (Q(x)∧P(x)))) := begin
simp only [not_forall, exists_prop],
use (1 / 2),
split,
simp [R],
suffices : ¬ (Q (1/2)),
tauto,
norm_num [Q],
end

#check false.elim
example : ¬ (∀ x : ℝ, (R(x) → (Q(x)∧P(x)))) := begin
intro h,
apply lol,
tauto,
end

example : ∀ x : ℝ,(¬Q(x) → P(x)) := begin
intro x,
simp only [Q, P],
intro hQ,
simp at hQ,
have : x*(x - 1) ≤ 0, linarith,
have h := mul_nonpos_iff.mp this,
cases h,
split;
linarith,

apply false.elim,
linarith,
end

example : (∃ x : ℝ,(¬R(x) ↔ Q(x))) := begin
use 2,
norm_num [R, Q],
end

def even (n : ℕ) := ∃ k : ℕ, n = 2*k
def odd (n : ℕ) := ∃ k : ℕ, n = 2*k+1

lemma even_or_odd (n : ℕ) : even n ∨ odd n := begin
induction n,
left, use 0, ring,

cases n_ih with l r,
{
right, cases l with k hk,
rw hk, use k, 
},
{
left,
cases r with k hk,
rw hk,
use k + 1,
ring,
},
end 

lemma even_sq (n : ℕ) : even n → even (n^2) := begin
rintro ⟨k, hk⟩,
rw hk,
use 2*k^2, ring,
end
lemma odd_sq (n : ℕ) : odd n → odd (n^2) := begin
rintro ⟨k, hk⟩,
rw hk,
use (2*k^2 + 2*k),
ring,
end 
lemma odd_plus_odd {n m : ℕ} : odd n → odd m → even (n + m) := begin
rintros ⟨k1, hk1⟩ ⟨k2, hk2⟩,
use k1 + k2 + 1,
linarith,
end
lemma even_plus_odd {n m : ℕ} : even n → odd m → odd (n + m) := begin
rintros ⟨k1, hk1⟩ ⟨k2, hk2⟩,
use k1 + k2,
linarith,
end
lemma not_even_and_odd {n : ℕ} : even n → odd n → false := begin
rintros ⟨k1, hk1⟩ ⟨k2, hk2⟩,
rw hk2 at hk1,
have : 2*(k1 - k2 : ℤ) = 1, linarith,
cases (k1 - k2 : ℤ) with m1 m2,
cases m1,
simp at this, exact this,
have l : int.of_nat (m1.succ) ≥ 1, linarith,
linarith,

have : int.neg_succ_of_nat m2 < 0,
exact int.neg_succ_lt_zero m2,
linarith,
end
#check pow_dvd_pow_of_dvd
lemma why : ∀ (a b c : ℕ ), a ≠ b → b ≠ c → a ≠ c → (∃ n1 : ℕ, a + b = 3^n1) → (∃ n2 : ℕ, a + c = 3^n2) → (∃ n3 : ℕ, b + c = 3^n3) → false := begin
intros a b c,
intros dab dbc dac,
rintros ⟨n1, h1⟩ ⟨n2, h2⟩ ⟨n3, h3⟩,
have w : 2*(a + b  + c) = 3^n1 + 3^n2 + 3^n3,
linarith,
have u : ∀ k : ℕ, odd (3^k),
{
  intro k,
  induction k,
  simp [odd],
  rw pow_succ,
  cases k_ih with q hq,
  rw hq,
  use (3*q + 1),
  ring,
},
have h1 := u n1,
have h2 := u n2,
have h3 := u n3,
have := odd_plus_odd h1 h2,
have l1 := even_plus_odd this h3,
have l2 : even (2*(a+b+c)), use (a + b+ c),
rw w at l2,
exact not_even_and_odd l2 l1,
end
example : ¬ (∃ (a b c : ℕ ), a ≠ b ∧  b ≠ c ∧ a ≠ c ∧ (∃ n1 : ℕ, a + b = 3^n1) ∧ (∃ n2 : ℕ, a + c = 3^n2) ∧ (∃ n3 : ℕ, b + c = 3^n3)) := begin
have :=  why,
intro h,
rcases h with ⟨a, b, c, h⟩,
specialize this a b c,
apply this;
tauto,
end

-- true
example : ∀ x : ℝ, (x^2 ≤ -1)→ ((x+1)^2=x^2+1) := begin
intros x hx,
apply false.elim,
linarith [sq_nonneg x],
end

-- neg
example :  ¬(∀ x : ℝ, (x^2 ≤ -1)→ ((x+1)^2=x^2+1)) ↔ ∃ x : ℝ, x^2 ≤ -1 := begin
have : ∀ x : ℝ, x^2 ≤ -1 → false,
intro x,
intro h,
linarith [sq_nonneg x],
have : (∃ (x : ℝ), x ^ 2 ≤ -1) ↔ (∃ (x : ℝ), x^2 ≤ -1 ∧ ¬ ((x + 1)^2 = x^2 +1)),
split,
tauto,
tauto,

rw this,
simp,
end

-- true
example : ∀ (x y : ℝ), (((x+y ≤ 7)∧(x*y = x)) → (x<7)) := begin
intros x y,
rintro ⟨h1, h2⟩,
have : x*(y - 1) = 0, linarith,
cases zero_eq_mul.mp (eq.symm this), 
linarith,
linarith,
end

example : ¬ (∀ (x y : ℝ), (((x+y ≤ 7)∧(x*y = x)) → (x<7))) ↔ ∃ (x y : ℝ), (x + y ≤ 7) ∧ (x*y = x) ∧ x ≥ 7 := begin
simp,  
end
end orange_4

#check (1,1) + (2,2)

#eval ((1 : (fin 2)), (1 : (fin 2))) * ( (0 : (fin 2)), (1  : (fin 2)))
namespace finite

instance bruh : has_mul ((fin 2) × (fin 2)) := {
  mul := λ ⟨a, b⟩, λ ⟨c, d⟩, (a*c - b*d, a*d + b*c)
}
#eval ((1 : (fin 2)), (1 : (fin 2))) * ( (0 : (fin 2)), (1  : (fin 2)))

end finite

#check exists_unique
lemma symmEx {α : Type*} {P : α → Prop} {f : α → α} : (∃! a, P a) → P ∘ f = P → (∀ a, P a → f a = a) := begin
intro hUnique, intro hSymm,
rcases hUnique with ⟨a1, ha1, a1Unique⟩,
intro a,
have : P (f a) = P a, exact congr_fun hSymm a,
intro h,
have h1 : P (f a), rw this, exact h,
exact eq.trans (a1Unique _ h1) (a1Unique _ h).symm,
end
#eval ((1 : (fin 2)), (1 : (fin 2))) * ( (0 : (fin 2)), (1  : (fin 2)))

example {α : Type*} {P : α → Prop} {f : α → α} (hUnique : ∃! a, P a) (hSymm : P ∘ f = P) (x : α) : (f x = x ∧ ∀ y, f y = y → y = x) → P x := begin
rintro ⟨hx, xUnique⟩,
have := symmEx hUnique hSymm,
rcases hUnique with ⟨x1, hx1, x1Unique⟩,
specialize this x1 hx1,
specialize xUnique x1 this,
rw xUnique at hx1,
exact hx1,
end

def f : ℝ× ℝ× ℝ → ℝ × ℝ × ℝ  := λ ⟨x, y, z⟩, (y, x, z)
example (P : ℝ × ℝ × ℝ → Prop) : (∃! xyz : ℝ × ℝ × ℝ, P xyz) → P ∘ f = P → (∀ xyz, P xyz → f xyz = xyz) := begin
intro h,
intro symm,
have := symmEx h symm,
intro xyz,
specialize this xyz, simp only at this,
exact this,
end
