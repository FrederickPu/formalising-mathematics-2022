import data.real.sqrt
import analysis.special_functions.trigonometric.basic

#check real.pi

def Mfar (M : ℝ) (f g : ℝ → ℝ) := ∃ x : ℝ, ∀ y : ℝ, x < y → |f y - g y| ≥ M 
def Mfar' (M : ℝ) (f g : ℝ → ℝ) := ∃ x : ℝ, ∀ y : ℝ, y < x → |f y - g y| ≥ M 

def Msep (M : ℝ) (f g : ℝ → ℝ) := ∀ x : ℝ, ∃ y : ℝ, x < y ∧ |f y - g y| ≥ M 
def Msep' (M : ℝ) (f g : ℝ → ℝ) := ∀ x : ℝ, ∃ y : ℝ, y <x ∧ |f y - g y| ≥ M 

theorem temp (M : ℝ) (f g : ℝ → ℝ) : Msep M f g ↔ Msep' M f g := begin
rw [Msep, Msep'],
split,
{
  intro h,
  intro x,
  specialize h (-x),
  cases h with y hy,
  use (-y),
}
end
-- Q5
example (f g : ℝ → ℝ) : (g = (λ x, f x + x^2)) → ∀ M > 0, Mfar M f g := begin
intro h,
intros M hM,
rw Mfar,
rw h,
simp only,
simp,
use (M.sqrt),
intros y hy,
have : M < y^2, exact real.lt_sq_of_sqrt_lt hy,
exact le_of_lt this,
end 

section Q8
noncomputable def gib (x : ℝ) : ℝ := ite (((floor_ring.floor x):ℝ) = x) 0 1

example : gib 1 = 0 := begin
simp [gib],
end

theorem gib_int : ∀ x : ℤ, gib x = 0 := begin
simp [gib],
end 

theorem gib_non_int (x : ℝ) : (∀ y : ℤ, (y : ℝ) ≠ x) → gib x = 1 := begin
intro h,
simp [gib],
exact ne.elim (h ⌊x⌋),
end

-- Q8
-- a) 
example (M : ℝ) (hM : M > 0) : ∀ f g, Mfar M f g → Msep M f g := begin
intros f g,
simp only [Mfar, Msep],
intro h, -- f is M-far from g
cases h with z h, -- there is some `z` for which every `y > z`, `|f y - g y| ≥ M`
intro x,
use (max x z) + 1, -- thus we can simply pick any (specifically `max x z + 1`) `y` greater than both `x ` and `z`. 
split,
  linarith [le_max_left x z],
{
  specialize h (max x z + 1),
  apply h,
  linarith [le_max_right x z],
},
end
-- b)
example : ¬ (∀ f g, Msep 1 f g → Mfar 1 f g) := begin
simp,
use gib, use λ _, 0,
simp [Mfar, Msep],
split,
intro x,
use floor_ring.floor x + 1.5,
split,
suffices : x < floor_ring.floor x + 1,
  linarith,
simp,

rw gib_non_int,
simp,

intro y,
intro h,
have : ((y - (floor_ring.floor x) - 1: ℤ) : ℝ) = (0.5 : ℝ),
push_cast, linarith,
cases y - floor_ring.floor x - 1 with n m,
simp at this,
cases n,
{
simp at this,
exact this,
},
{
  have : 1 ≤ n.succ, rw nat.succ_eq_add_one, linarith,
  have : 1 ≤ (n.succ : ℝ), simp,
  have : (2⁻¹: ℝ) < 1, norm_num,
  linarith,
},
have l1 : int.neg_succ_of_nat m < 0,
exact int.neg_succ_lt_zero m,
have l2 : (int.neg_succ_of_nat m : ℝ) < 0, exact int.cast_lt_zero.mpr l1,
linarith,

intro x,
use (floor_ring.floor x + 1),
simp,
have : (int.floor x + 1 : ℝ) = ((int.floor x + 1 : ℤ) : ℝ), push_cast,
rw this,
rw gib_int,
norm_num,
end
end Q8

-- Q8 is actually easier than Q7
-- however we can use a similar technique to the `gibbs` function in 8.b) for Q7
section Q7
noncomputable def jim (x : ℝ) := ite ((floor_ring.floor x : ℝ) = x) x 0
-- if we can get it to work for M = 1, we can simply scale the solution up and down to satisfy other values of M.
-- to satisfy 1-sep, we need only pick an integer y greater than every x
-- moreover, because you can always find jim(y) = 0 for non integer real numbers, making M-far false.

theorem jim_int : ∀ x : ℤ, jim x = x := begin
intro x,
simp [jim],
end

theorem jim_non_int (x : ℝ) : (∀ y : ℤ, (y : ℝ) ≠ x) → jim x = 0 := begin
intro h,
simp only [jim, int.floor_ring_floor_eq],
have := h ⌊x⌋,
simp [this],
end

example : ∃ f g, Msep 1 f g := begin
use jim, use (λ _, 0),
simp [Msep],
intro x,
use ⌊|x|⌋ + 1,
split,
have : |x| < ↑⌊|x|⌋ + 1,
simp,
have : x ≤ |x|, exact le_abs_self x,
linarith,
have : ↑⌊|x|⌋ + 1 = ((⌊|x|⌋ + 1 : ℤ) : ℝ), push_cast,
rw this,
rw jim_int,
rw abs_eq_self.mpr _,
norm_num,
have : |x| ≥ 0, exact abs_nonneg x,
exact int.floor_nonneg.mpr this,

simp,
have : |x| ≥ 0, exact abs_nonneg x,
have := int.floor_nonneg.mpr this,
have : (⌊|x|⌋ :ℝ) ≥ 0, simp [this],
linarith,
end 
end Q7