import data.real.sqrt
-- HW

-- Q3
example (x y : ℝ) : x ≠ 0 → 2*y ≤ y^2/x^2 + x^2 := begin
intro h,
have := sq_nonneg (y/x - x),
have l : (y / x - x) ^ 2 = y^2/x^2 - 2*y + x^2, field_simp, ring,
rw l at this,
linarith,
end

-- Q4
lemma l1 (x y : ℝ) : x ≥ 0 → y ≥ 0 → x ≥ y → x.sqrt - y.sqrt ≤ (x - y).sqrt := begin
intros hx hy h,
have : y * y ≤ x*y, exact mul_mono_nonneg hy h,
ring_nf at this,
have : (y^2).sqrt ≤ (x*y).sqrt := real.sqrt_le_sqrt this,
rw real.sqrt_sq hy at this,
have : (x.sqrt)^2 - 2*(x*y).sqrt + (y.sqrt)^2 ≤ x - y, 
rw [real.sq_sqrt hx, real.sq_sqrt hy],
linarith,
rw [real.sqrt_mul' x hy, ← mul_assoc 2 x.sqrt y.sqrt] at this,
rw ← sub_sq _ _ at this,
exact real.le_sqrt_of_sq_le this,
end

#check abs_eq_neg_self
example (x y : ℝ) : x ≥ 0 → y ≥ 0 → abs (x.sqrt - y.sqrt) ≤ (abs (x-y)).sqrt := begin
intros hx hy,
cases le_total y x,
{
rw [abs_eq_self.mpr _, abs_eq_self.mpr _],
exact l1 x y hx hy h,

linarith,
linarith [real.sqrt_le_sqrt h],
},
{
  rw [abs_eq_neg_self.mpr _, abs_eq_neg_self.mpr _],
  ring_nf,
  norm_num,
  linarith [l1 y x hy hx h],

  linarith,
  linarith [real.sqrt_le_sqrt h],
},
end

def array 5 (array 5 (fin 5)):= ![![0, 0, 0, 0], 
 ![0, 1, 2, 3], 
 ![0, 2, 4, 2], 
 ![0, 3, 6, 4], 
 ![0, 4, 3, 2]]

def my_mul : fin 5 → fin 5 → fin 5 := 
![
![0, 0, 0, 0, 0],
![0, 1, 2, 3, 4],
![0, 2, 4, 1, 3],
![0, 3, 1, 4, 2],
![0, 4, 3, 2, 1]]

def my_add : fin 5 → fin 5 → fin 5 :=
![![0, 1, 2, 3, 4],
![1, 2, 3, 4, 0],
![2, 3, 4, 0, 1],
![3, 4, 0, 1, 2],
![4, 0, 1, 2, 3]]

def oops := (list.fin_range 5).map $ λ x, (list.fin_range 5).map $ λ y, (list.fin_range 5).map $ λz, my_mul x (my_add y z)
def whoops := (list.fin_range 5).map $ λ x, (list.fin_range 5).map $ λ y, (list.fin_range 5).map $ λ z, my_add (my_mul x y) (my_mul x z)

#eval if oops = whoops then tt else ff
#eval (list.fin_range 5).map (λ x, (list.fin_range 5).map (λ y, my_mul x y))

#eval (list.fin_range 5).map $ λ x, (list.fin_range 5).map $ λ y, (list.fin_range 5).map $ λ z, if (my_add (my_mul x y) (my_mul x z) = my_mul x (my_add y z)) then tt else ff
#eval (list.fin_range 5).map $ λ x, (list.fin_range 5).map $ λ y, if my_mul x y = my_mul y x then tt else ff
#eval (list.fin_range 5).map $ λ x, (list.fin_range 5).map $ λ y, if my_add x y = my_add y x then tt else ff

#eval (list.fin_range 5).map $ λ x, list.filter (λ y : fin 5, my_add x y = 0) (list.fin_range 5) 
#eval (list.fin_range 5).map $ λ x, list.filter (λ y : fin 5, my_mul x y = 1) (list.fin_range 5) 
#check list.filter

#check fintype.card

#check comm_group
