import tactic -- imports all the Lean tactics
import data.real.sqrt -- the reals

-- Q1 a) TRUE
example : {xy : ℝ × ℝ | xy.fst - 1 = 0} ⊆ {xy : ℝ × ℝ | xy.fst * (xy.fst - 1) = 0}:= begin
intro x,
simp only [set.mem_set_of_eq],
intro h,
rw h,
ring,
end

-- Q1 b) FALSE
example : ¬ ({x : ℝ | ∃ y : ℤ , x = y}.prod (set.univ) ⊆ set.univ.prod ({x : ℝ | ∃ y : ℤ , x = y})) := begin
intro  h,
simp only [set.subset_def] at h,
specialize h (⟨(1:ℝ), (1/2:ℝ)⟩),
simp at h,
specialize h 1,
simp at h,

cases h with y hy,
have l : 0 < (2⁻¹:ℝ),
simp,
have r : (2⁻¹ : ℝ) < 1,
norm_num,

rw hy at l, rw hy at r,
simp at l,
rw ← int.cast_one at r,
have : y < 1 := int.cast_lt.mp r,

linarith,
end

-- Q2 a)
universes u v
example (A : Type u) (B : Type v) (f : A → B) (C D : set A) : f '' (C ∩ D) ⊆ (f '' C) ∩ (f '' D) := begin
intros a ha,
simp at ha,
split,
{
cases ha with x hx,
use x, tauto,
},
{
cases ha with x hx,
use x, tauto,
},
end

-- Q2 b)
example : ∃ (f : ℝ → ℝ), ∃ (C D : set ℝ), f '' (C ∩ D) ≠ (f '' C) ∩ (f '' D) := begin
use (λ x : ℝ, x^2),
use {(1:ℝ)}, use {(-1:ℝ)},
simp,
have : (1:ℝ)  ≠ -1, linarith,
have : {(1 : ℝ)} ∩ {(-1 : ℝ)} = {x : ℝ | false},
ext x,
simp,
intro h, linarith,
rw this,
simp,
intro h,
have := (set.eq_empty_iff_forall_not_mem.mp h.symm),
specialize this 1,
tauto,
end

-- Q3
example : (λ x:ℝ, (1 + x^2)/x^2) '' (set.univ \ {(0: ℝ)}) = {x : ℝ | 1 < x}  := begin
ext y,
simp,
split,
{
  intro h,
  cases h with x hx,
  cases hx,
  rw ← hx_right,
  have : x^2 ≠ 0, exact pow_ne_zero 2 hx_left,
  have : (1 + x^2)/x^2 = (1/(x^2)) + 1,
  {
    field_simp,
  },
  rw this,
  have : x^2 > 0, exact (sq_pos_iff x).mpr hx_left,
  have : 1/x^2 > 0, exact one_div_pos.mpr this,
  linarith,
},
{
  intro hy,
  use (1/(y-1).sqrt),
  split,
  have : y - 1 > 0, linarith,
  have : (y - 1).sqrt ≠ 0, exact real.sqrt_ne_zero'.mpr this,
  exact one_div_ne_zero this,

  have : y - 1 > 0, linarith,
  simp [real.sq_sqrt],
  rw [real.sq_sqrt],
  have : y - 1 ≠ 0, exact ne_of_gt this,
  field_simp,
  exact le_of_lt this,
},
end

#check list.all₂_iff_forall


theorem list.all_iff_all₂ {α : Type*} (l : list α) (p : α → bool) : (l.all p) = tt ↔ l.all₂ (λ x, p x) := begin
simp [list.all, list.all₂],
induction l,
simp,
rw [list.foldr_cons, list.all₂_cons],
rw ← l_ih,
simp,
end

theorem bruh (α : Type*) (p : α → Prop) [decidable_pred p]: (λ x, ((ite (p x) tt ff : bool) : Prop)) = λ x, p x := begin
ext x,
cases decidable.em (p x),
simp [h],
simp [h],
end
example : (![1, 2, 3, 0] : fin 4 → fin 4) = λ x : fin 4, (x + 1 : fin 4) := begin
suffices : (list.fin_range 4).all₂ (λ x, ((![1, 2, 3, 0] : fin 4 → fin 4) x) = (λ x : fin 4, (x + 1 : fin 4)) x),
have := list.all₂_iff_forall.mp this,
apply funext,
intro x,
specialize this x,
simp at this,
exact this,

-- simp [list.all₂],
have := list.all_iff_all₂ (list.fin_range 4) (λ x, if ((![1, 2, 3, 0] : fin 4 → fin 4) x = (λ x : fin 4, (x + 1 : fin 4)) x) then tt else ff),
simp [list.all, if_pos] at this,
rw bruh at this,
simp,
rw ← this,
refl,
end

example {n : ℕ} (β : Type v) [decidable_eq β] (f g : (fin n) → β):
(list.fin_range n).all (λ x, f x = g x) → f = g := begin
intro h,
suffices : (list.fin_range n).all₂ (λ x, f x = g x),
{
  have := list.all₂_iff_forall.mp this,
  ext x,
  specialize this x,
  simp at this,
  exact this,
},

have := list.all_iff_all₂ (list.fin_range n) (λ x, if (f x = g x) then tt else ff),
simp [list.all, if_pos] at this,
rw bruh at this,
rw ← this,

exact h, 
end

-- this mat137 induction stuff
example (n : ℕ) (x : ℝ) (hx : x > 0): (1 + x)^(n+2) > 1 + (n+2:ℕ)*x := begin
induction n with k hk,
simp,
suffices : x^2 > 0, linarith,
exact pow_pos hx 2,

have : k.succ + 2 = (k + 2) + 1, ring,
rw this,
let w := k + 2,
have l : w = k + 2, refl,
rw ← l, rw ← l at hk,

rw pow_add,
have u : 1 + x  > 0, linarith,
have := (mul_lt_mul_right u).mpr hk,
simp at this,
end
#check set.Icc

#check field
#check subfield

class MyField (F : Type u) extends has_zero F, has_one F, has_add F, has_mul F, has_inv F, has_neg F :=
(nontrivial : (0:F) ≠ 1)
(mul_assoc (a b c : F) : a * (b*c) = (a*b)*c)
(add_assoc (a b c : F) : a + (b + c) = (a + b) + c)
(mul_comm (a b : F) : a * b = b * a)
(add_comm (a b : F) : a + b = b + a)
(add_zero (a : F) : a + 0 = a)
(mul_one (a : F) : a * 1 = a)
(mul_inv (a : F) : a ≠ 0 → a * a⁻¹ = 1)
(add_neg (a : F) : a + (-a) = 0)
(distrib (a b c : F) : a*(b+c) = a*b + a*c)


variables {F : Type u} [MyField F]

namespace MyField

-- Q4
theorem mul_canc (a b c : F) : a ≠ 0 → a*b = a*c → b = c  := begin
intro ha,
intro h,
-- only rewrite LHS 
-- basically emulating the equation chain proofs mat102 likes so much
conv
{
  to_lhs,
  rw ← mul_one b,
  rw ← mul_inv a ha,
  rw mul_assoc,
  rw mul_comm b a,
  rw h,
  rw mul_comm _ a⁻¹,
  rw mul_assoc,
  rw mul_comm _ a,
  rw mul_inv _ ha,
  rw mul_comm,
  rw mul_one,
},
end

--Q5
lemma zero_unique (a b : F) :a + b = a → b = 0 := begin
intro h,
-- again another equality chain (left to right)
conv {
  to_lhs,
  rw ← add_zero b,
  rw ← add_neg a,
  rw add_assoc,
  rw add_comm b a,
  rw h,
  rw add_neg,
},
end
lemma neg_unique (a b : F) : a + b = 0 → b = -a := begin
intro h,
conv {
  to_lhs,
  rw ← add_zero b,
  rw ← add_neg a,
  rw add_assoc,
  rw add_comm b a,
  rw h,
  rw add_comm,
  rw add_zero, 
},
end
theorem one_mul_zero : (1:F) * 0 = 0 := begin
have : (1:F) + (1*0) = 1,
have : (1:F)*1 + (1*0) = 1 + (1*0), rw mul_one, 
rw ← this,
rw ← distrib,
rw add_zero,
rw mul_one,

apply zero_unique (1:F) (1*0),
exact this,
end

theorem zero_mul_zero : (0 : F) * 0 = 0  := begin
apply zero_unique (0*1:F),
conv {
  to_lhs,
  rw ← distrib,
  rw add_zero,
},
end

theorem mul_zero (a : F) : a * 0 = 0 := begin
have l : -a*0 = -(a*0),
apply neg_unique,
conv {
  to_lhs,
  rw mul_comm a 0, rw mul_comm (-a) 0,
  rw ← distrib,
  rw add_neg,
  rw zero_mul_zero,
},
rw ← add_zero (a*0),
have : a * 0 + 0 = a*0 + (a*0 + -(a*0)),
rw add_neg,

conv {
to_lhs,
rw this,
rw ← l,
rw add_assoc,
rw ← distrib,
rw add_zero,
rw [mul_comm a 0, mul_comm (-a) 0],
rw ← distrib,
rw add_neg,
rw zero_mul_zero,
},
end

-- 
example (x : F) : x*x = 1 → x ∈ ({(-1:F), (1:F)} : set F) := begin
intro h,
have h : x*x + (-1) = 1 + (-1),
rw h,
rw add_neg at h,
have : x * x + -1  = (x + 1)*(x + (-1)),
conv {
to_lhs,
rw ← add_zero (x*x),
rw ← mul_zero x,
rw ← add_neg (1:F),
rw distrib,
rw add_assoc,
rw ← distrib x,
rw ← add_assoc,
},
have : x*(-1) + (-1) = (-1)*x + (-1)*1,
rw mul_one, rw mul_comm,

conv {
  to_lhs,
  rw this,
  rw ← distrib,
  rw mul_comm (-1) (x+1),
  rw mul_comm x (x+1),
  rw ← distrib,
},

rw this at h,
suffices : x + 1 = 0 ∨ x + (-1) = 0,
cases this,
{
  have : x = -1,
  conv {
    to_lhs,
    rw ← add_zero x,
    rw ← add_neg (1:F),
    rw add_assoc,
    rw this_1,
    rw add_comm,
    rw add_zero,
  },
  rw this, simp,
},
{
  have : x = 1,
  conv {
    to_lhs,
    rw ← add_zero x,
     rw ←add_neg (1:F),
     rw add_comm (1:F) (-1),
     rw add_assoc,
     rw this_1,
     rw add_comm,
     rw add_zero,
  },
  rw this, simp,
},

cases em (x + 1 = 0),
{
  left, exact h_1,
},
{
  rw ← mul_zero (x + 1) at h,
  right,
  apply mul_canc (x+1),
  exact h_1,
  exact h,
},
end

inductive F5 
| zero : F5
| one : F5
| a : F5
| b : F5
| c : F5

namespace F5
instance : has_one F5 := ⟨one⟩
instance : has_zero F5 := ⟨zero⟩

def to_fin5 (x : F5) : fin 5 :=
x.cases_on 0 1 2 3 4
def to_F5 : fin 5 → F5 := ![zero, one, a, b, c]

instance : has_coe F5 (fin 5) := ⟨to_fin5⟩
instance : has_coe (fin 5) F5 := ⟨to_F5⟩
def my_add : fin 5 → fin 5 → fin 5 :=
![![0, 1, 2, 3, 4],
![1, 2, 3, 4, 0],
![2, 3, 4, 0, 1],
![3, 4, 0, 1, 2],
![4, 0, 1, 2, 3]]

def my_mul : fin 5 → fin 5 → fin 5 := 
![
![0, 0, 0, 0, 0],
![0, 1, 2, 3, 4],
![0, 2, 4, 1, 3],
![0, 3, 1, 4, 2],
![0, 4, 3, 2, 1]]

def add : F5 → F5 → F5 := λ x, λ y, my_add x y 
def mul : F5 → F5 → F5 := λ x, λ y, my_mul x y

instance : has_repr F5 := {
  repr := λ x, F5.cases_on x "0" "1" "a" "b" "c" 
}
instance : has_add F5 := ⟨add⟩ 
instance : has_mul F5 := ⟨mul⟩
instance : has_neg F5 := ⟨λ x, ![0, 4, 3, 2, 1] x⟩
instance : has_inv F5 := ⟨λ x, ![0, 1, 3, 2, 4] x⟩



#eval zero + -zero
instance : MyField F5 := {
  nontrivial := begin
    simp only [has_one.one, has_zero.zero],
    simp only [ne.def, not_false_iff],
  end,
  mul_assoc := begin
    intros a b c,
    induction a;
    {
      induction b; {
        induction c;
        refl,
      },
    },
  end,
  add_assoc := begin
    intros a b c,
      induction a;
      {
        induction b; {
          induction c;
          refl,
        },
      },
  end,
  mul_comm := begin
    intros a b,
    induction a; 
    {
      induction b;
      refl,
    },
  end,
  add_comm := begin
    intros a b,
    induction a; 
    {
      induction b;
      refl,
    },
  end,
  add_zero := begin
    intro a,
    induction a;
    refl,
  end,
  mul_one := begin
    intro a,
    induction a;
    refl,
  end,
  mul_inv := begin
    intro a,
    induction a,
    
  end,
  add_neg := begin
    intro a, 
    induction a;
    {
      refl,
    },
  end,
  distrib := begin
    intros a b c,
    induction a;
    {
      induction b;
      {
        induction c;
        refl,
      },
    },
  end
}
end F5
end MyField