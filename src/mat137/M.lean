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